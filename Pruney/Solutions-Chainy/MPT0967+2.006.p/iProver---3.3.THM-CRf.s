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
% DateTime   : Thu Dec  3 12:00:38 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_503)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f56,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

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

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_430,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_432,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_23])).

cnf(c_918,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_921,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1444,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_918,c_921])).

cnf(c_1498,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_432,c_1444])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_6])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_278,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_9])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_917,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_1680,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_918,c_917])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_919,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_297,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_301,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_297,c_9])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_301])).

cnf(c_916,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_1602,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_918,c_916])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_924,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1966,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1602,c_924])).

cnf(c_2551,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X1) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1966,c_924])).

cnf(c_3909,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_919,c_2551])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1067,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_1068,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_1199,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | r1_tarski(k2_relat_1(sK3),X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1572,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ r1_tarski(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_2157,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_2158,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2157])).

cnf(c_4281,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3909,c_28,c_29,c_1068,c_2158])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_920,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1835,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_920,c_921])).

cnf(c_5694,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4281,c_1835])).

cnf(c_1061,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1062,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1061])).

cnf(c_6248,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5694,c_28,c_1062])).

cnf(c_6249,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6248])).

cnf(c_6257,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1680,c_6249])).

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

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_141])).

cnf(c_417,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_911,plain,
    ( k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_6488,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6257,c_911])).

cnf(c_440,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK1 != sK2
    | sK0 != sK0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_141,c_24])).

cnf(c_1064,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_1065,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1073,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_622,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1110,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_1129,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_1147,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1331,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_624,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1136,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,sK1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_1361,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(sK2,sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_1363,plain,
    ( r1_tarski(sK2,sK1)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 != sK1
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1361])).

cnf(c_1091,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relat_1(sK3),X1)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2179,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(c_4458,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2179])).

cnf(c_4459,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4458])).

cnf(c_6642,plain,
    ( k1_relat_1(sK3) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6488,c_23,c_28,c_22,c_29,c_503,c_1061,c_1062,c_1064,c_1065,c_1067,c_1068,c_1073,c_1147,c_1331,c_1363,c_2157,c_2158,c_4458,c_4459])).

cnf(c_6645,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1498,c_6642])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7068,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6645,c_21])).

cnf(c_7069,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7068])).

cnf(c_7290,plain,
    ( k1_relat_1(sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7069,c_6642])).

cnf(c_1965,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1680,c_924])).

cnf(c_923,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_926,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1934,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_926])).

cnf(c_2381,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1965,c_1934])).

cnf(c_2402,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2381])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1687,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1120,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_1301,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != sK0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_1686,plain,
    ( ~ r1_tarski(sK0,sK0)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != sK0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1301])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_368,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_914,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_77,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_83,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_623,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1228,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1229,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1228])).

cnf(c_1595,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_914,c_21,c_77,c_83,c_1229])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7290,c_6488,c_4459,c_4458,c_2402,c_2158,c_2157,c_1687,c_1686,c_1595,c_1498,c_1363,c_1331,c_1147,c_1129,c_1110,c_1073,c_1068,c_1067,c_1065,c_1064,c_1062,c_1061,c_440,c_29,c_22,c_28,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.43/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/0.98  
% 2.43/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/0.98  
% 2.43/0.98  ------  iProver source info
% 2.43/0.98  
% 2.43/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.43/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/0.98  git: non_committed_changes: false
% 2.43/0.98  git: last_make_outside_of_git: false
% 2.43/0.98  
% 2.43/0.98  ------ 
% 2.43/0.98  
% 2.43/0.98  ------ Input Options
% 2.43/0.98  
% 2.43/0.98  --out_options                           all
% 2.43/0.98  --tptp_safe_out                         true
% 2.43/0.98  --problem_path                          ""
% 2.43/0.98  --include_path                          ""
% 2.43/0.98  --clausifier                            res/vclausify_rel
% 2.43/0.98  --clausifier_options                    --mode clausify
% 2.43/0.98  --stdin                                 false
% 2.43/0.98  --stats_out                             all
% 2.43/0.98  
% 2.43/0.98  ------ General Options
% 2.43/0.98  
% 2.43/0.98  --fof                                   false
% 2.43/0.98  --time_out_real                         305.
% 2.43/0.98  --time_out_virtual                      -1.
% 2.43/0.98  --symbol_type_check                     false
% 2.43/0.98  --clausify_out                          false
% 2.43/0.98  --sig_cnt_out                           false
% 2.43/0.98  --trig_cnt_out                          false
% 2.43/0.98  --trig_cnt_out_tolerance                1.
% 2.43/0.98  --trig_cnt_out_sk_spl                   false
% 2.43/0.98  --abstr_cl_out                          false
% 2.43/0.98  
% 2.43/0.98  ------ Global Options
% 2.43/0.98  
% 2.43/0.98  --schedule                              default
% 2.43/0.98  --add_important_lit                     false
% 2.43/0.98  --prop_solver_per_cl                    1000
% 2.43/0.98  --min_unsat_core                        false
% 2.43/0.98  --soft_assumptions                      false
% 2.43/0.98  --soft_lemma_size                       3
% 2.43/0.98  --prop_impl_unit_size                   0
% 2.43/0.98  --prop_impl_unit                        []
% 2.43/0.98  --share_sel_clauses                     true
% 2.43/0.98  --reset_solvers                         false
% 2.43/0.98  --bc_imp_inh                            [conj_cone]
% 2.43/0.98  --conj_cone_tolerance                   3.
% 2.43/0.98  --extra_neg_conj                        none
% 2.43/0.98  --large_theory_mode                     true
% 2.43/0.98  --prolific_symb_bound                   200
% 2.43/0.98  --lt_threshold                          2000
% 2.43/0.98  --clause_weak_htbl                      true
% 2.43/0.98  --gc_record_bc_elim                     false
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing Options
% 2.43/0.98  
% 2.43/0.98  --preprocessing_flag                    true
% 2.43/0.98  --time_out_prep_mult                    0.1
% 2.43/0.98  --splitting_mode                        input
% 2.43/0.98  --splitting_grd                         true
% 2.43/0.98  --splitting_cvd                         false
% 2.43/0.98  --splitting_cvd_svl                     false
% 2.43/0.98  --splitting_nvd                         32
% 2.43/0.98  --sub_typing                            true
% 2.43/0.98  --prep_gs_sim                           true
% 2.43/0.98  --prep_unflatten                        true
% 2.43/0.98  --prep_res_sim                          true
% 2.43/0.98  --prep_upred                            true
% 2.43/0.98  --prep_sem_filter                       exhaustive
% 2.43/0.98  --prep_sem_filter_out                   false
% 2.43/0.98  --pred_elim                             true
% 2.43/0.98  --res_sim_input                         true
% 2.43/0.98  --eq_ax_congr_red                       true
% 2.43/0.98  --pure_diseq_elim                       true
% 2.43/0.98  --brand_transform                       false
% 2.43/0.98  --non_eq_to_eq                          false
% 2.43/0.98  --prep_def_merge                        true
% 2.43/0.98  --prep_def_merge_prop_impl              false
% 2.43/0.98  --prep_def_merge_mbd                    true
% 2.43/0.98  --prep_def_merge_tr_red                 false
% 2.43/0.98  --prep_def_merge_tr_cl                  false
% 2.43/0.98  --smt_preprocessing                     true
% 2.43/0.98  --smt_ac_axioms                         fast
% 2.43/0.98  --preprocessed_out                      false
% 2.43/0.98  --preprocessed_stats                    false
% 2.43/0.98  
% 2.43/0.98  ------ Abstraction refinement Options
% 2.43/0.98  
% 2.43/0.98  --abstr_ref                             []
% 2.43/0.98  --abstr_ref_prep                        false
% 2.43/0.98  --abstr_ref_until_sat                   false
% 2.43/0.98  --abstr_ref_sig_restrict                funpre
% 2.43/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/0.98  --abstr_ref_under                       []
% 2.43/0.98  
% 2.43/0.98  ------ SAT Options
% 2.43/0.98  
% 2.43/0.98  --sat_mode                              false
% 2.43/0.98  --sat_fm_restart_options                ""
% 2.43/0.98  --sat_gr_def                            false
% 2.43/0.98  --sat_epr_types                         true
% 2.43/0.98  --sat_non_cyclic_types                  false
% 2.43/0.98  --sat_finite_models                     false
% 2.43/0.98  --sat_fm_lemmas                         false
% 2.43/0.98  --sat_fm_prep                           false
% 2.43/0.98  --sat_fm_uc_incr                        true
% 2.43/0.98  --sat_out_model                         small
% 2.43/0.98  --sat_out_clauses                       false
% 2.43/0.98  
% 2.43/0.98  ------ QBF Options
% 2.43/0.98  
% 2.43/0.98  --qbf_mode                              false
% 2.43/0.98  --qbf_elim_univ                         false
% 2.43/0.98  --qbf_dom_inst                          none
% 2.43/0.98  --qbf_dom_pre_inst                      false
% 2.43/0.98  --qbf_sk_in                             false
% 2.43/0.98  --qbf_pred_elim                         true
% 2.43/0.98  --qbf_split                             512
% 2.43/0.98  
% 2.43/0.98  ------ BMC1 Options
% 2.43/0.98  
% 2.43/0.98  --bmc1_incremental                      false
% 2.43/0.98  --bmc1_axioms                           reachable_all
% 2.43/0.98  --bmc1_min_bound                        0
% 2.43/0.98  --bmc1_max_bound                        -1
% 2.43/0.98  --bmc1_max_bound_default                -1
% 2.43/0.98  --bmc1_symbol_reachability              true
% 2.43/0.98  --bmc1_property_lemmas                  false
% 2.43/0.98  --bmc1_k_induction                      false
% 2.43/0.98  --bmc1_non_equiv_states                 false
% 2.43/0.98  --bmc1_deadlock                         false
% 2.43/0.98  --bmc1_ucm                              false
% 2.43/0.98  --bmc1_add_unsat_core                   none
% 2.43/0.98  --bmc1_unsat_core_children              false
% 2.43/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/0.98  --bmc1_out_stat                         full
% 2.43/0.98  --bmc1_ground_init                      false
% 2.43/0.98  --bmc1_pre_inst_next_state              false
% 2.43/0.98  --bmc1_pre_inst_state                   false
% 2.43/0.98  --bmc1_pre_inst_reach_state             false
% 2.43/0.98  --bmc1_out_unsat_core                   false
% 2.43/0.98  --bmc1_aig_witness_out                  false
% 2.43/0.98  --bmc1_verbose                          false
% 2.43/0.98  --bmc1_dump_clauses_tptp                false
% 2.43/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.43/0.98  --bmc1_dump_file                        -
% 2.43/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.43/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.43/0.98  --bmc1_ucm_extend_mode                  1
% 2.43/0.98  --bmc1_ucm_init_mode                    2
% 2.43/0.98  --bmc1_ucm_cone_mode                    none
% 2.43/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.43/0.98  --bmc1_ucm_relax_model                  4
% 2.43/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.43/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/0.98  --bmc1_ucm_layered_model                none
% 2.43/0.98  --bmc1_ucm_max_lemma_size               10
% 2.43/0.98  
% 2.43/0.98  ------ AIG Options
% 2.43/0.98  
% 2.43/0.98  --aig_mode                              false
% 2.43/0.98  
% 2.43/0.98  ------ Instantiation Options
% 2.43/0.98  
% 2.43/0.98  --instantiation_flag                    true
% 2.43/0.98  --inst_sos_flag                         false
% 2.43/0.98  --inst_sos_phase                        true
% 2.43/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel_side                     num_symb
% 2.43/0.98  --inst_solver_per_active                1400
% 2.43/0.98  --inst_solver_calls_frac                1.
% 2.43/0.98  --inst_passive_queue_type               priority_queues
% 2.43/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/0.98  --inst_passive_queues_freq              [25;2]
% 2.43/0.98  --inst_dismatching                      true
% 2.43/0.98  --inst_eager_unprocessed_to_passive     true
% 2.43/0.98  --inst_prop_sim_given                   true
% 2.43/0.98  --inst_prop_sim_new                     false
% 2.43/0.98  --inst_subs_new                         false
% 2.43/0.98  --inst_eq_res_simp                      false
% 2.43/0.98  --inst_subs_given                       false
% 2.43/0.98  --inst_orphan_elimination               true
% 2.43/0.98  --inst_learning_loop_flag               true
% 2.43/0.98  --inst_learning_start                   3000
% 2.43/0.98  --inst_learning_factor                  2
% 2.43/0.98  --inst_start_prop_sim_after_learn       3
% 2.43/0.98  --inst_sel_renew                        solver
% 2.43/0.98  --inst_lit_activity_flag                true
% 2.43/0.98  --inst_restr_to_given                   false
% 2.43/0.98  --inst_activity_threshold               500
% 2.43/0.98  --inst_out_proof                        true
% 2.43/0.98  
% 2.43/0.98  ------ Resolution Options
% 2.43/0.98  
% 2.43/0.98  --resolution_flag                       true
% 2.43/0.98  --res_lit_sel                           adaptive
% 2.43/0.98  --res_lit_sel_side                      none
% 2.43/0.98  --res_ordering                          kbo
% 2.43/0.98  --res_to_prop_solver                    active
% 2.43/0.98  --res_prop_simpl_new                    false
% 2.43/0.98  --res_prop_simpl_given                  true
% 2.43/0.98  --res_passive_queue_type                priority_queues
% 2.43/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/0.98  --res_passive_queues_freq               [15;5]
% 2.43/0.98  --res_forward_subs                      full
% 2.43/0.98  --res_backward_subs                     full
% 2.43/0.98  --res_forward_subs_resolution           true
% 2.43/0.98  --res_backward_subs_resolution          true
% 2.43/0.98  --res_orphan_elimination                true
% 2.43/0.98  --res_time_limit                        2.
% 2.43/0.98  --res_out_proof                         true
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Options
% 2.43/0.98  
% 2.43/0.98  --superposition_flag                    true
% 2.43/0.98  --sup_passive_queue_type                priority_queues
% 2.43/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.43/0.98  --demod_completeness_check              fast
% 2.43/0.98  --demod_use_ground                      true
% 2.43/0.98  --sup_to_prop_solver                    passive
% 2.43/0.98  --sup_prop_simpl_new                    true
% 2.43/0.98  --sup_prop_simpl_given                  true
% 2.43/0.98  --sup_fun_splitting                     false
% 2.43/0.98  --sup_smt_interval                      50000
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Simplification Setup
% 2.43/0.98  
% 2.43/0.98  --sup_indices_passive                   []
% 2.43/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_full_bw                           [BwDemod]
% 2.43/0.98  --sup_immed_triv                        [TrivRules]
% 2.43/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_immed_bw_main                     []
% 2.43/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  
% 2.43/0.98  ------ Combination Options
% 2.43/0.98  
% 2.43/0.98  --comb_res_mult                         3
% 2.43/0.98  --comb_sup_mult                         2
% 2.43/0.98  --comb_inst_mult                        10
% 2.43/0.98  
% 2.43/0.98  ------ Debug Options
% 2.43/0.98  
% 2.43/0.98  --dbg_backtrace                         false
% 2.43/0.98  --dbg_dump_prop_clauses                 false
% 2.43/0.98  --dbg_dump_prop_clauses_file            -
% 2.43/0.98  --dbg_out_stat                          false
% 2.43/0.98  ------ Parsing...
% 2.43/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.43/0.98  ------ Proving...
% 2.43/0.98  ------ Problem Properties 
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  clauses                                 19
% 2.43/0.98  conjectures                             3
% 2.43/0.98  EPR                                     6
% 2.43/0.98  Horn                                    17
% 2.43/0.98  unary                                   4
% 2.43/0.98  binary                                  7
% 2.43/0.98  lits                                    47
% 2.43/0.98  lits eq                                 19
% 2.43/0.98  fd_pure                                 0
% 2.43/0.98  fd_pseudo                               0
% 2.43/0.98  fd_cond                                 0
% 2.43/0.98  fd_pseudo_cond                          1
% 2.43/0.98  AC symbols                              0
% 2.43/0.98  
% 2.43/0.98  ------ Schedule dynamic 5 is on 
% 2.43/0.98  
% 2.43/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  ------ 
% 2.43/0.98  Current options:
% 2.43/0.98  ------ 
% 2.43/0.98  
% 2.43/0.98  ------ Input Options
% 2.43/0.98  
% 2.43/0.98  --out_options                           all
% 2.43/0.98  --tptp_safe_out                         true
% 2.43/0.98  --problem_path                          ""
% 2.43/0.98  --include_path                          ""
% 2.43/0.98  --clausifier                            res/vclausify_rel
% 2.43/0.98  --clausifier_options                    --mode clausify
% 2.43/0.98  --stdin                                 false
% 2.43/0.98  --stats_out                             all
% 2.43/0.98  
% 2.43/0.98  ------ General Options
% 2.43/0.98  
% 2.43/0.98  --fof                                   false
% 2.43/0.98  --time_out_real                         305.
% 2.43/0.98  --time_out_virtual                      -1.
% 2.43/0.98  --symbol_type_check                     false
% 2.43/0.98  --clausify_out                          false
% 2.43/0.98  --sig_cnt_out                           false
% 2.43/0.98  --trig_cnt_out                          false
% 2.43/0.98  --trig_cnt_out_tolerance                1.
% 2.43/0.98  --trig_cnt_out_sk_spl                   false
% 2.43/0.98  --abstr_cl_out                          false
% 2.43/0.98  
% 2.43/0.98  ------ Global Options
% 2.43/0.98  
% 2.43/0.98  --schedule                              default
% 2.43/0.98  --add_important_lit                     false
% 2.43/0.98  --prop_solver_per_cl                    1000
% 2.43/0.98  --min_unsat_core                        false
% 2.43/0.98  --soft_assumptions                      false
% 2.43/0.98  --soft_lemma_size                       3
% 2.43/0.98  --prop_impl_unit_size                   0
% 2.43/0.98  --prop_impl_unit                        []
% 2.43/0.98  --share_sel_clauses                     true
% 2.43/0.98  --reset_solvers                         false
% 2.43/0.98  --bc_imp_inh                            [conj_cone]
% 2.43/0.98  --conj_cone_tolerance                   3.
% 2.43/0.98  --extra_neg_conj                        none
% 2.43/0.98  --large_theory_mode                     true
% 2.43/0.98  --prolific_symb_bound                   200
% 2.43/0.98  --lt_threshold                          2000
% 2.43/0.98  --clause_weak_htbl                      true
% 2.43/0.98  --gc_record_bc_elim                     false
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing Options
% 2.43/0.98  
% 2.43/0.98  --preprocessing_flag                    true
% 2.43/0.98  --time_out_prep_mult                    0.1
% 2.43/0.98  --splitting_mode                        input
% 2.43/0.98  --splitting_grd                         true
% 2.43/0.98  --splitting_cvd                         false
% 2.43/0.98  --splitting_cvd_svl                     false
% 2.43/0.98  --splitting_nvd                         32
% 2.43/0.98  --sub_typing                            true
% 2.43/0.98  --prep_gs_sim                           true
% 2.43/0.98  --prep_unflatten                        true
% 2.43/0.98  --prep_res_sim                          true
% 2.43/0.98  --prep_upred                            true
% 2.43/0.98  --prep_sem_filter                       exhaustive
% 2.43/0.98  --prep_sem_filter_out                   false
% 2.43/0.98  --pred_elim                             true
% 2.43/0.98  --res_sim_input                         true
% 2.43/0.98  --eq_ax_congr_red                       true
% 2.43/0.98  --pure_diseq_elim                       true
% 2.43/0.98  --brand_transform                       false
% 2.43/0.98  --non_eq_to_eq                          false
% 2.43/0.98  --prep_def_merge                        true
% 2.43/0.98  --prep_def_merge_prop_impl              false
% 2.43/0.98  --prep_def_merge_mbd                    true
% 2.43/0.98  --prep_def_merge_tr_red                 false
% 2.43/0.98  --prep_def_merge_tr_cl                  false
% 2.43/0.98  --smt_preprocessing                     true
% 2.43/0.98  --smt_ac_axioms                         fast
% 2.43/0.98  --preprocessed_out                      false
% 2.43/0.98  --preprocessed_stats                    false
% 2.43/0.98  
% 2.43/0.98  ------ Abstraction refinement Options
% 2.43/0.98  
% 2.43/0.98  --abstr_ref                             []
% 2.43/0.98  --abstr_ref_prep                        false
% 2.43/0.98  --abstr_ref_until_sat                   false
% 2.43/0.98  --abstr_ref_sig_restrict                funpre
% 2.43/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/0.98  --abstr_ref_under                       []
% 2.43/0.98  
% 2.43/0.98  ------ SAT Options
% 2.43/0.98  
% 2.43/0.98  --sat_mode                              false
% 2.43/0.98  --sat_fm_restart_options                ""
% 2.43/0.98  --sat_gr_def                            false
% 2.43/0.98  --sat_epr_types                         true
% 2.43/0.98  --sat_non_cyclic_types                  false
% 2.43/0.98  --sat_finite_models                     false
% 2.43/0.98  --sat_fm_lemmas                         false
% 2.43/0.98  --sat_fm_prep                           false
% 2.43/0.98  --sat_fm_uc_incr                        true
% 2.43/0.98  --sat_out_model                         small
% 2.43/0.98  --sat_out_clauses                       false
% 2.43/0.98  
% 2.43/0.98  ------ QBF Options
% 2.43/0.98  
% 2.43/0.98  --qbf_mode                              false
% 2.43/0.98  --qbf_elim_univ                         false
% 2.43/0.98  --qbf_dom_inst                          none
% 2.43/0.98  --qbf_dom_pre_inst                      false
% 2.43/0.98  --qbf_sk_in                             false
% 2.43/0.98  --qbf_pred_elim                         true
% 2.43/0.98  --qbf_split                             512
% 2.43/0.98  
% 2.43/0.98  ------ BMC1 Options
% 2.43/0.98  
% 2.43/0.98  --bmc1_incremental                      false
% 2.43/0.98  --bmc1_axioms                           reachable_all
% 2.43/0.98  --bmc1_min_bound                        0
% 2.43/0.98  --bmc1_max_bound                        -1
% 2.43/0.98  --bmc1_max_bound_default                -1
% 2.43/0.98  --bmc1_symbol_reachability              true
% 2.43/0.98  --bmc1_property_lemmas                  false
% 2.43/0.98  --bmc1_k_induction                      false
% 2.43/0.98  --bmc1_non_equiv_states                 false
% 2.43/0.98  --bmc1_deadlock                         false
% 2.43/0.98  --bmc1_ucm                              false
% 2.43/0.98  --bmc1_add_unsat_core                   none
% 2.43/0.98  --bmc1_unsat_core_children              false
% 2.43/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/0.98  --bmc1_out_stat                         full
% 2.43/0.98  --bmc1_ground_init                      false
% 2.43/0.98  --bmc1_pre_inst_next_state              false
% 2.43/0.98  --bmc1_pre_inst_state                   false
% 2.43/0.98  --bmc1_pre_inst_reach_state             false
% 2.43/0.98  --bmc1_out_unsat_core                   false
% 2.43/0.98  --bmc1_aig_witness_out                  false
% 2.43/0.98  --bmc1_verbose                          false
% 2.43/0.98  --bmc1_dump_clauses_tptp                false
% 2.43/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.43/0.98  --bmc1_dump_file                        -
% 2.43/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.43/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.43/0.98  --bmc1_ucm_extend_mode                  1
% 2.43/0.98  --bmc1_ucm_init_mode                    2
% 2.43/0.98  --bmc1_ucm_cone_mode                    none
% 2.43/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.43/0.98  --bmc1_ucm_relax_model                  4
% 2.43/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.43/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/0.98  --bmc1_ucm_layered_model                none
% 2.43/0.98  --bmc1_ucm_max_lemma_size               10
% 2.43/0.98  
% 2.43/0.98  ------ AIG Options
% 2.43/0.98  
% 2.43/0.98  --aig_mode                              false
% 2.43/0.98  
% 2.43/0.98  ------ Instantiation Options
% 2.43/0.98  
% 2.43/0.98  --instantiation_flag                    true
% 2.43/0.98  --inst_sos_flag                         false
% 2.43/0.98  --inst_sos_phase                        true
% 2.43/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel_side                     none
% 2.43/0.98  --inst_solver_per_active                1400
% 2.43/0.98  --inst_solver_calls_frac                1.
% 2.43/0.98  --inst_passive_queue_type               priority_queues
% 2.43/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/0.98  --inst_passive_queues_freq              [25;2]
% 2.43/0.98  --inst_dismatching                      true
% 2.43/0.98  --inst_eager_unprocessed_to_passive     true
% 2.43/0.98  --inst_prop_sim_given                   true
% 2.43/0.98  --inst_prop_sim_new                     false
% 2.43/0.98  --inst_subs_new                         false
% 2.43/0.98  --inst_eq_res_simp                      false
% 2.43/0.98  --inst_subs_given                       false
% 2.43/0.98  --inst_orphan_elimination               true
% 2.43/0.98  --inst_learning_loop_flag               true
% 2.43/0.98  --inst_learning_start                   3000
% 2.43/0.98  --inst_learning_factor                  2
% 2.43/0.98  --inst_start_prop_sim_after_learn       3
% 2.43/0.98  --inst_sel_renew                        solver
% 2.43/0.98  --inst_lit_activity_flag                true
% 2.43/0.98  --inst_restr_to_given                   false
% 2.43/0.98  --inst_activity_threshold               500
% 2.43/0.98  --inst_out_proof                        true
% 2.43/0.98  
% 2.43/0.98  ------ Resolution Options
% 2.43/0.98  
% 2.43/0.98  --resolution_flag                       false
% 2.43/0.98  --res_lit_sel                           adaptive
% 2.43/0.98  --res_lit_sel_side                      none
% 2.43/0.98  --res_ordering                          kbo
% 2.43/0.98  --res_to_prop_solver                    active
% 2.43/0.98  --res_prop_simpl_new                    false
% 2.43/0.98  --res_prop_simpl_given                  true
% 2.43/0.98  --res_passive_queue_type                priority_queues
% 2.43/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/0.98  --res_passive_queues_freq               [15;5]
% 2.43/0.98  --res_forward_subs                      full
% 2.43/0.98  --res_backward_subs                     full
% 2.43/0.98  --res_forward_subs_resolution           true
% 2.43/0.98  --res_backward_subs_resolution          true
% 2.43/0.98  --res_orphan_elimination                true
% 2.43/0.98  --res_time_limit                        2.
% 2.43/0.98  --res_out_proof                         true
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Options
% 2.43/0.98  
% 2.43/0.98  --superposition_flag                    true
% 2.43/0.98  --sup_passive_queue_type                priority_queues
% 2.43/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.43/0.98  --demod_completeness_check              fast
% 2.43/0.98  --demod_use_ground                      true
% 2.43/0.98  --sup_to_prop_solver                    passive
% 2.43/0.98  --sup_prop_simpl_new                    true
% 2.43/0.98  --sup_prop_simpl_given                  true
% 2.43/0.98  --sup_fun_splitting                     false
% 2.43/0.98  --sup_smt_interval                      50000
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Simplification Setup
% 2.43/0.98  
% 2.43/0.98  --sup_indices_passive                   []
% 2.43/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_full_bw                           [BwDemod]
% 2.43/0.98  --sup_immed_triv                        [TrivRules]
% 2.43/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_immed_bw_main                     []
% 2.43/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  
% 2.43/0.98  ------ Combination Options
% 2.43/0.98  
% 2.43/0.98  --comb_res_mult                         3
% 2.43/0.98  --comb_sup_mult                         2
% 2.43/0.98  --comb_inst_mult                        10
% 2.43/0.98  
% 2.43/0.98  ------ Debug Options
% 2.43/0.98  
% 2.43/0.98  --dbg_backtrace                         false
% 2.43/0.98  --dbg_dump_prop_clauses                 false
% 2.43/0.98  --dbg_dump_prop_clauses_file            -
% 2.43/0.98  --dbg_out_stat                          false
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  ------ Proving...
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  % SZS status Theorem for theBenchmark.p
% 2.43/0.98  
% 2.43/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/0.98  
% 2.43/0.98  fof(f10,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f22,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(ennf_transformation,[],[f10])).
% 2.43/0.98  
% 2.43/0.98  fof(f23,plain,(
% 2.43/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(flattening,[],[f22])).
% 2.43/0.98  
% 2.43/0.98  fof(f30,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(nnf_transformation,[],[f23])).
% 2.43/0.98  
% 2.43/0.98  fof(f47,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f30])).
% 2.43/0.98  
% 2.43/0.98  fof(f11,conjecture,(
% 2.43/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f12,negated_conjecture,(
% 2.43/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.43/0.98    inference(negated_conjecture,[],[f11])).
% 2.43/0.98  
% 2.43/0.98  fof(f24,plain,(
% 2.43/0.98    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.43/0.98    inference(ennf_transformation,[],[f12])).
% 2.43/0.98  
% 2.43/0.98  fof(f25,plain,(
% 2.43/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.43/0.98    inference(flattening,[],[f24])).
% 2.43/0.98  
% 2.43/0.98  fof(f31,plain,(
% 2.43/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.43/0.98    introduced(choice_axiom,[])).
% 2.43/0.98  
% 2.43/0.98  fof(f32,plain,(
% 2.43/0.98    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.43/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f31])).
% 2.43/0.98  
% 2.43/0.98  fof(f54,plain,(
% 2.43/0.98    v1_funct_2(sK3,sK0,sK1)),
% 2.43/0.98    inference(cnf_transformation,[],[f32])).
% 2.43/0.98  
% 2.43/0.98  fof(f55,plain,(
% 2.43/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.43/0.98    inference(cnf_transformation,[],[f32])).
% 2.43/0.98  
% 2.43/0.98  fof(f8,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f19,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(ennf_transformation,[],[f8])).
% 2.43/0.98  
% 2.43/0.98  fof(f45,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f19])).
% 2.43/0.98  
% 2.43/0.98  fof(f7,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f18,plain,(
% 2.43/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(ennf_transformation,[],[f7])).
% 2.43/0.98  
% 2.43/0.98  fof(f43,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f18])).
% 2.43/0.98  
% 2.43/0.98  fof(f4,axiom,(
% 2.43/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f15,plain,(
% 2.43/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.43/0.98    inference(ennf_transformation,[],[f4])).
% 2.43/0.98  
% 2.43/0.98  fof(f28,plain,(
% 2.43/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.43/0.98    inference(nnf_transformation,[],[f15])).
% 2.43/0.98  
% 2.43/0.98  fof(f38,plain,(
% 2.43/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f28])).
% 2.43/0.98  
% 2.43/0.98  fof(f6,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f17,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/0.98    inference(ennf_transformation,[],[f6])).
% 2.43/0.98  
% 2.43/0.98  fof(f42,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f17])).
% 2.43/0.98  
% 2.43/0.98  fof(f56,plain,(
% 2.43/0.98    r1_tarski(sK1,sK2)),
% 2.43/0.98    inference(cnf_transformation,[],[f32])).
% 2.43/0.98  
% 2.43/0.98  fof(f5,axiom,(
% 2.43/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f16,plain,(
% 2.43/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.43/0.98    inference(ennf_transformation,[],[f5])).
% 2.43/0.98  
% 2.43/0.98  fof(f29,plain,(
% 2.43/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.43/0.98    inference(nnf_transformation,[],[f16])).
% 2.43/0.98  
% 2.43/0.98  fof(f40,plain,(
% 2.43/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f29])).
% 2.43/0.98  
% 2.43/0.98  fof(f44,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f18])).
% 2.43/0.98  
% 2.43/0.98  fof(f2,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f13,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.43/0.98    inference(ennf_transformation,[],[f2])).
% 2.43/0.98  
% 2.43/0.98  fof(f14,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.43/0.98    inference(flattening,[],[f13])).
% 2.43/0.98  
% 2.43/0.98  fof(f36,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f14])).
% 2.43/0.98  
% 2.43/0.98  fof(f9,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f20,plain,(
% 2.43/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.43/0.98    inference(ennf_transformation,[],[f9])).
% 2.43/0.98  
% 2.43/0.98  fof(f21,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.43/0.98    inference(flattening,[],[f20])).
% 2.43/0.98  
% 2.43/0.98  fof(f46,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f21])).
% 2.43/0.98  
% 2.43/0.98  fof(f49,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f30])).
% 2.43/0.98  
% 2.43/0.98  fof(f58,plain,(
% 2.43/0.98    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 2.43/0.98    inference(cnf_transformation,[],[f32])).
% 2.43/0.98  
% 2.43/0.98  fof(f53,plain,(
% 2.43/0.98    v1_funct_1(sK3)),
% 2.43/0.98    inference(cnf_transformation,[],[f32])).
% 2.43/0.98  
% 2.43/0.98  fof(f1,axiom,(
% 2.43/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f26,plain,(
% 2.43/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.43/0.98    inference(nnf_transformation,[],[f1])).
% 2.43/0.98  
% 2.43/0.98  fof(f27,plain,(
% 2.43/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.43/0.98    inference(flattening,[],[f26])).
% 2.43/0.98  
% 2.43/0.98  fof(f35,plain,(
% 2.43/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f27])).
% 2.43/0.98  
% 2.43/0.98  fof(f3,axiom,(
% 2.43/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f37,plain,(
% 2.43/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f3])).
% 2.43/0.98  
% 2.43/0.98  fof(f57,plain,(
% 2.43/0.98    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.43/0.98    inference(cnf_transformation,[],[f32])).
% 2.43/0.98  
% 2.43/0.98  fof(f33,plain,(
% 2.43/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.43/0.98    inference(cnf_transformation,[],[f27])).
% 2.43/0.98  
% 2.43/0.98  fof(f60,plain,(
% 2.43/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.43/0.98    inference(equality_resolution,[],[f33])).
% 2.43/0.98  
% 2.43/0.98  fof(f51,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f30])).
% 2.43/0.98  
% 2.43/0.98  fof(f63,plain,(
% 2.43/0.98    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.43/0.98    inference(equality_resolution,[],[f51])).
% 2.43/0.98  
% 2.43/0.98  cnf(c_19,plain,
% 2.43/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.43/0.98      | k1_xboole_0 = X2 ),
% 2.43/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_24,negated_conjecture,
% 2.43/0.98      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.43/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_429,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.43/0.98      | sK1 != X2
% 2.43/0.98      | sK0 != X1
% 2.43/0.98      | sK3 != X0
% 2.43/0.98      | k1_xboole_0 = X2 ),
% 2.43/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_430,plain,
% 2.43/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.43/0.98      | k1_relset_1(sK0,sK1,sK3) = sK0
% 2.43/0.98      | k1_xboole_0 = sK1 ),
% 2.43/0.98      inference(unflattening,[status(thm)],[c_429]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_23,negated_conjecture,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.43/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_432,plain,
% 2.43/0.98      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.43/0.98      inference(global_propositional_subsumption,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_430,c_23]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_918,plain,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_12,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.43/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_921,plain,
% 2.43/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.43/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1444,plain,
% 2.43/0.98      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_918,c_921]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1498,plain,
% 2.43/0.98      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_432,c_1444]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_11,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | v4_relat_1(X0,X1) ),
% 2.43/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_6,plain,
% 2.43/0.98      ( ~ v4_relat_1(X0,X1)
% 2.43/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 2.43/0.98      | ~ v1_relat_1(X0) ),
% 2.43/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_274,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 2.43/0.98      | ~ v1_relat_1(X0) ),
% 2.43/0.98      inference(resolution,[status(thm)],[c_11,c_6]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_9,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | v1_relat_1(X0) ),
% 2.43/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_278,plain,
% 2.43/0.98      ( r1_tarski(k1_relat_1(X0),X1)
% 2.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.43/0.98      inference(global_propositional_subsumption,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_274,c_9]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_279,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.43/0.98      inference(renaming,[status(thm)],[c_278]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_917,plain,
% 2.43/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.43/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1680,plain,
% 2.43/0.98      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_918,c_917]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_22,negated_conjecture,
% 2.43/0.98      ( r1_tarski(sK1,sK2) ),
% 2.43/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_919,plain,
% 2.43/0.98      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_8,plain,
% 2.43/0.98      ( ~ v5_relat_1(X0,X1)
% 2.43/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 2.43/0.98      | ~ v1_relat_1(X0) ),
% 2.43/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_10,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | v5_relat_1(X0,X2) ),
% 2.43/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_296,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | r1_tarski(k2_relat_1(X3),X4)
% 2.43/0.98      | ~ v1_relat_1(X3)
% 2.43/0.98      | X0 != X3
% 2.43/0.98      | X2 != X4 ),
% 2.43/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_297,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 2.43/0.98      | ~ v1_relat_1(X0) ),
% 2.43/0.98      inference(unflattening,[status(thm)],[c_296]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_301,plain,
% 2.43/0.98      ( r1_tarski(k2_relat_1(X0),X2)
% 2.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.43/0.98      inference(global_propositional_subsumption,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_297,c_9]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_302,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.43/0.98      inference(renaming,[status(thm)],[c_301]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_916,plain,
% 2.43/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.43/0.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1602,plain,
% 2.43/0.98      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_918,c_916]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_3,plain,
% 2.43/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.43/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_924,plain,
% 2.43/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.43/0.98      | r1_tarski(X1,X2) != iProver_top
% 2.43/0.98      | r1_tarski(X0,X2) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1966,plain,
% 2.43/0.98      ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
% 2.43/0.98      | r1_tarski(sK1,X0) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_1602,c_924]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2551,plain,
% 2.43/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.43/0.98      | r1_tarski(k2_relat_1(sK3),X1) = iProver_top
% 2.43/0.98      | r1_tarski(sK1,X0) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_1966,c_924]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_3909,plain,
% 2.43/0.98      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 2.43/0.98      | r1_tarski(sK1,sK1) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_919,c_2551]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_28,plain,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_29,plain,
% 2.43/0.98      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1067,plain,
% 2.43/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.43/0.98      | r1_tarski(k2_relat_1(sK3),sK1) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_302]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1068,plain,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.43/0.98      | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1199,plain,
% 2.43/0.98      ( ~ r1_tarski(X0,X1)
% 2.43/0.98      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.43/0.98      | r1_tarski(k2_relat_1(sK3),X1) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1572,plain,
% 2.43/0.98      ( r1_tarski(k2_relat_1(sK3),X0)
% 2.43/0.98      | ~ r1_tarski(k2_relat_1(sK3),sK1)
% 2.43/0.98      | ~ r1_tarski(sK1,X0) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_1199]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2157,plain,
% 2.43/0.98      ( ~ r1_tarski(k2_relat_1(sK3),sK1)
% 2.43/0.98      | r1_tarski(k2_relat_1(sK3),sK2)
% 2.43/0.98      | ~ r1_tarski(sK1,sK2) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_1572]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2158,plain,
% 2.43/0.98      ( r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
% 2.43/0.98      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 2.43/0.98      | r1_tarski(sK1,sK2) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_2157]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_4281,plain,
% 2.43/0.98      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 2.43/0.98      inference(global_propositional_subsumption,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_3909,c_28,c_29,c_1068,c_2158]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_13,plain,
% 2.43/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.43/0.98      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.43/0.98      | ~ v1_relat_1(X0) ),
% 2.43/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_920,plain,
% 2.43/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.43/0.98      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 2.43/0.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.43/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1835,plain,
% 2.43/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.43/0.98      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 2.43/0.98      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 2.43/0.98      | v1_relat_1(X2) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_920,c_921]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_5694,plain,
% 2.43/0.98      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 2.43/0.98      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.43/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_4281,c_1835]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1061,plain,
% 2.43/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.43/0.98      | v1_relat_1(sK3) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1062,plain,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.43/0.98      | v1_relat_1(sK3) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_1061]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_6248,plain,
% 2.43/0.98      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 2.43/0.98      | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
% 2.43/0.98      inference(global_propositional_subsumption,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_5694,c_28,c_1062]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_6249,plain,
% 2.43/0.98      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 2.43/0.98      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 2.43/0.98      inference(renaming,[status(thm)],[c_6248]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_6257,plain,
% 2.43/0.98      ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_1680,c_6249]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_17,plain,
% 2.43/0.98      ( v1_funct_2(X0,X1,X2)
% 2.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | k1_relset_1(X1,X2,X0) != X1
% 2.43/0.98      | k1_xboole_0 = X2 ),
% 2.43/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_20,negated_conjecture,
% 2.43/0.98      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.43/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.43/0.98      | ~ v1_funct_1(sK3) ),
% 2.43/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_25,negated_conjecture,
% 2.43/0.98      ( v1_funct_1(sK3) ),
% 2.43/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_140,plain,
% 2.43/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.43/0.98      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 2.43/0.98      inference(global_propositional_subsumption,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_20,c_25]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_141,negated_conjecture,
% 2.43/0.98      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.43/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.43/0.98      inference(renaming,[status(thm)],[c_140]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_416,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.43/0.98      | k1_relset_1(X1,X2,X0) != X1
% 2.43/0.98      | sK2 != X2
% 2.43/0.98      | sK0 != X1
% 2.43/0.98      | sK3 != X0
% 2.43/0.98      | k1_xboole_0 = X2 ),
% 2.43/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_141]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_417,plain,
% 2.43/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.43/0.98      | k1_relset_1(sK0,sK2,sK3) != sK0
% 2.43/0.98      | k1_xboole_0 = sK2 ),
% 2.43/0.98      inference(unflattening,[status(thm)],[c_416]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_911,plain,
% 2.43/0.98      ( k1_relset_1(sK0,sK2,sK3) != sK0
% 2.43/0.98      | k1_xboole_0 = sK2
% 2.43/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_6488,plain,
% 2.43/0.98      ( k1_relat_1(sK3) != sK0
% 2.43/0.98      | sK2 = k1_xboole_0
% 2.43/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.43/0.98      inference(demodulation,[status(thm)],[c_6257,c_911]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_440,plain,
% 2.43/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.43/0.98      | sK1 != sK2
% 2.43/0.98      | sK0 != sK0
% 2.43/0.98      | sK3 != sK3 ),
% 2.43/0.98      inference(resolution_lifted,[status(thm)],[c_141,c_24]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1064,plain,
% 2.43/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.43/0.98      | r1_tarski(k1_relat_1(sK3),sK0) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_279]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1065,plain,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.43/0.98      | r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_1064]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_0,plain,
% 2.43/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.43/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1073,plain,
% 2.43/0.98      ( ~ r1_tarski(sK1,sK2) | ~ r1_tarski(sK2,sK1) | sK1 = sK2 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_622,plain,( X0 = X0 ),theory(equality) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1110,plain,
% 2.43/0.98      ( sK3 = sK3 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_622]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1129,plain,
% 2.43/0.98      ( sK0 = sK0 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_622]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1147,plain,
% 2.43/0.98      ( sK1 = sK1 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_622]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_4,plain,
% 2.43/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 2.43/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1331,plain,
% 2.43/0.98      ( r1_tarski(k1_xboole_0,sK1) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_624,plain,
% 2.43/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.43/0.98      theory(equality) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1136,plain,
% 2.43/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,sK1) | sK1 != X1 | sK2 != X0 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_624]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1361,plain,
% 2.43/0.98      ( ~ r1_tarski(X0,sK1)
% 2.43/0.98      | r1_tarski(sK2,sK1)
% 2.43/0.98      | sK1 != sK1
% 2.43/0.98      | sK2 != X0 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_1136]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1363,plain,
% 2.43/0.98      ( r1_tarski(sK2,sK1)
% 2.43/0.98      | ~ r1_tarski(k1_xboole_0,sK1)
% 2.43/0.98      | sK1 != sK1
% 2.43/0.98      | sK2 != k1_xboole_0 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_1361]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1091,plain,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.43/0.98      | ~ r1_tarski(k2_relat_1(sK3),X1)
% 2.43/0.98      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 2.43/0.98      | ~ v1_relat_1(sK3) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2179,plain,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 2.43/0.98      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.43/0.98      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 2.43/0.98      | ~ v1_relat_1(sK3) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_1091]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_4458,plain,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.43/0.98      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.43/0.98      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 2.43/0.98      | ~ v1_relat_1(sK3) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_2179]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_4459,plain,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 2.43/0.98      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 2.43/0.98      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 2.43/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_4458]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_6642,plain,
% 2.43/0.98      ( k1_relat_1(sK3) != sK0 ),
% 2.43/0.98      inference(global_propositional_subsumption,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_6488,c_23,c_28,c_22,c_29,c_503,c_1061,c_1062,c_1064,
% 2.43/0.98                 c_1065,c_1067,c_1068,c_1073,c_1147,c_1331,c_1363,c_2157,
% 2.43/0.98                 c_2158,c_4458,c_4459]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_6645,plain,
% 2.43/0.98      ( sK1 = k1_xboole_0 ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_1498,c_6642]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_21,negated_conjecture,
% 2.43/0.98      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 2.43/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_7068,plain,
% 2.43/0.98      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.43/0.98      inference(demodulation,[status(thm)],[c_6645,c_21]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_7069,plain,
% 2.43/0.98      ( sK0 = k1_xboole_0 ),
% 2.43/0.98      inference(equality_resolution_simp,[status(thm)],[c_7068]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_7290,plain,
% 2.43/0.98      ( k1_relat_1(sK3) != k1_xboole_0 ),
% 2.43/0.98      inference(demodulation,[status(thm)],[c_7069,c_6642]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1965,plain,
% 2.43/0.98      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.43/0.98      | r1_tarski(sK0,X0) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_1680,c_924]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_923,plain,
% 2.43/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_926,plain,
% 2.43/0.98      ( X0 = X1
% 2.43/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.43/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1934,plain,
% 2.43/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_923,c_926]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2381,plain,
% 2.43/0.98      ( k1_relat_1(sK3) = k1_xboole_0
% 2.43/0.98      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_1965,c_1934]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2402,plain,
% 2.43/0.98      ( ~ r1_tarski(sK0,k1_xboole_0) | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.43/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2381]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2,plain,
% 2.43/0.98      ( r1_tarski(X0,X0) ),
% 2.43/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1687,plain,
% 2.43/0.98      ( r1_tarski(sK0,sK0) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1120,plain,
% 2.43/0.98      ( ~ r1_tarski(X0,X1)
% 2.43/0.98      | r1_tarski(sK0,k1_xboole_0)
% 2.43/0.98      | sK0 != X0
% 2.43/0.98      | k1_xboole_0 != X1 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_624]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1301,plain,
% 2.43/0.98      ( ~ r1_tarski(sK0,X0)
% 2.43/0.98      | r1_tarski(sK0,k1_xboole_0)
% 2.43/0.98      | sK0 != sK0
% 2.43/0.98      | k1_xboole_0 != X0 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_1120]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1686,plain,
% 2.43/0.98      ( ~ r1_tarski(sK0,sK0)
% 2.43/0.98      | r1_tarski(sK0,k1_xboole_0)
% 2.43/0.98      | sK0 != sK0
% 2.43/0.98      | k1_xboole_0 != sK0 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_1301]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_15,plain,
% 2.43/0.98      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.43/0.98      | k1_xboole_0 = X1
% 2.43/0.98      | k1_xboole_0 = X0 ),
% 2.43/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_367,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.43/0.98      | sK1 != k1_xboole_0
% 2.43/0.98      | sK0 != X1
% 2.43/0.98      | sK3 != X0
% 2.43/0.98      | k1_xboole_0 = X0
% 2.43/0.98      | k1_xboole_0 = X1 ),
% 2.43/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_368,plain,
% 2.43/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 2.43/0.98      | sK1 != k1_xboole_0
% 2.43/0.98      | k1_xboole_0 = sK0
% 2.43/0.98      | k1_xboole_0 = sK3 ),
% 2.43/0.98      inference(unflattening,[status(thm)],[c_367]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_914,plain,
% 2.43/0.98      ( sK1 != k1_xboole_0
% 2.43/0.98      | k1_xboole_0 = sK0
% 2.43/0.98      | k1_xboole_0 = sK3
% 2.43/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_77,plain,
% 2.43/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_83,plain,
% 2.43/0.98      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.43/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_623,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1228,plain,
% 2.43/0.98      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_623]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1229,plain,
% 2.43/0.98      ( sK1 != k1_xboole_0
% 2.43/0.98      | k1_xboole_0 = sK1
% 2.43/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_1228]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1595,plain,
% 2.43/0.98      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK0 ),
% 2.43/0.98      inference(global_propositional_subsumption,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_914,c_21,c_77,c_83,c_1229]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(contradiction,plain,
% 2.43/0.98      ( $false ),
% 2.43/0.98      inference(minisat,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_7290,c_6488,c_4459,c_4458,c_2402,c_2158,c_2157,c_1687,
% 2.43/0.98                 c_1686,c_1595,c_1498,c_1363,c_1331,c_1147,c_1129,c_1110,
% 2.43/0.98                 c_1073,c_1068,c_1067,c_1065,c_1064,c_1062,c_1061,c_440,
% 2.43/0.98                 c_29,c_22,c_28,c_23]) ).
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/0.98  
% 2.43/0.98  ------                               Statistics
% 2.43/0.98  
% 2.43/0.98  ------ General
% 2.43/0.98  
% 2.43/0.98  abstr_ref_over_cycles:                  0
% 2.43/0.98  abstr_ref_under_cycles:                 0
% 2.43/0.98  gc_basic_clause_elim:                   0
% 2.43/0.98  forced_gc_time:                         0
% 2.43/0.98  parsing_time:                           0.01
% 2.43/0.98  unif_index_cands_time:                  0.
% 2.43/0.98  unif_index_add_time:                    0.
% 2.43/0.98  orderings_time:                         0.
% 2.43/0.98  out_proof_time:                         0.009
% 2.43/0.98  total_time:                             0.187
% 2.43/0.98  num_of_symbols:                         48
% 2.43/0.98  num_of_terms:                           1870
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing
% 2.43/0.98  
% 2.43/0.98  num_of_splits:                          0
% 2.43/0.98  num_of_split_atoms:                     0
% 2.43/0.98  num_of_reused_defs:                     0
% 2.43/0.98  num_eq_ax_congr_red:                    15
% 2.43/0.98  num_of_sem_filtered_clauses:            2
% 2.43/0.98  num_of_subtypes:                        0
% 2.43/0.98  monotx_restored_types:                  0
% 2.43/0.98  sat_num_of_epr_types:                   0
% 2.43/0.98  sat_num_of_non_cyclic_types:            0
% 2.43/0.98  sat_guarded_non_collapsed_types:        0
% 2.43/0.98  num_pure_diseq_elim:                    0
% 2.43/0.98  simp_replaced_by:                       0
% 2.43/0.98  res_preprocessed:                       97
% 2.43/0.98  prep_upred:                             0
% 2.43/0.98  prep_unflattend:                        35
% 2.43/0.98  smt_new_axioms:                         0
% 2.43/0.98  pred_elim_cands:                        3
% 2.43/0.98  pred_elim:                              3
% 2.43/0.98  pred_elim_cl:                           5
% 2.43/0.98  pred_elim_cycles:                       6
% 2.43/0.98  merged_defs:                            0
% 2.43/0.98  merged_defs_ncl:                        0
% 2.43/0.98  bin_hyper_res:                          0
% 2.43/0.98  prep_cycles:                            4
% 2.43/0.98  pred_elim_time:                         0.005
% 2.43/0.98  splitting_time:                         0.
% 2.43/0.98  sem_filter_time:                        0.
% 2.43/0.98  monotx_time:                            0.
% 2.43/0.98  subtype_inf_time:                       0.
% 2.43/0.98  
% 2.43/0.98  ------ Problem properties
% 2.43/0.98  
% 2.43/0.98  clauses:                                19
% 2.43/0.98  conjectures:                            3
% 2.43/0.98  epr:                                    6
% 2.43/0.98  horn:                                   17
% 2.43/0.98  ground:                                 10
% 2.43/0.98  unary:                                  4
% 2.43/0.98  binary:                                 7
% 2.43/0.98  lits:                                   47
% 2.43/0.98  lits_eq:                                19
% 2.43/0.98  fd_pure:                                0
% 2.43/0.98  fd_pseudo:                              0
% 2.43/0.98  fd_cond:                                0
% 2.43/0.98  fd_pseudo_cond:                         1
% 2.43/0.98  ac_symbols:                             0
% 2.43/0.98  
% 2.43/0.98  ------ Propositional Solver
% 2.43/0.98  
% 2.43/0.98  prop_solver_calls:                      28
% 2.43/0.98  prop_fast_solver_calls:                 789
% 2.43/0.98  smt_solver_calls:                       0
% 2.43/0.98  smt_fast_solver_calls:                  0
% 2.43/0.98  prop_num_of_clauses:                    1978
% 2.43/0.98  prop_preprocess_simplified:             4750
% 2.43/0.98  prop_fo_subsumed:                       26
% 2.43/0.98  prop_solver_time:                       0.
% 2.43/0.98  smt_solver_time:                        0.
% 2.43/0.98  smt_fast_solver_time:                   0.
% 2.43/0.98  prop_fast_solver_time:                  0.
% 2.43/0.98  prop_unsat_core_time:                   0.
% 2.43/0.98  
% 2.43/0.98  ------ QBF
% 2.43/0.98  
% 2.43/0.98  qbf_q_res:                              0
% 2.43/0.98  qbf_num_tautologies:                    0
% 2.43/0.98  qbf_prep_cycles:                        0
% 2.43/0.98  
% 2.43/0.98  ------ BMC1
% 2.43/0.98  
% 2.43/0.98  bmc1_current_bound:                     -1
% 2.43/0.98  bmc1_last_solved_bound:                 -1
% 2.43/0.98  bmc1_unsat_core_size:                   -1
% 2.43/0.98  bmc1_unsat_core_parents_size:           -1
% 2.43/0.98  bmc1_merge_next_fun:                    0
% 2.43/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.43/0.98  
% 2.43/0.98  ------ Instantiation
% 2.43/0.98  
% 2.43/0.98  inst_num_of_clauses:                    640
% 2.43/0.98  inst_num_in_passive:                    37
% 2.43/0.98  inst_num_in_active:                     430
% 2.43/0.98  inst_num_in_unprocessed:                173
% 2.43/0.98  inst_num_of_loops:                      450
% 2.43/0.98  inst_num_of_learning_restarts:          0
% 2.43/0.98  inst_num_moves_active_passive:          15
% 2.43/0.98  inst_lit_activity:                      0
% 2.43/0.98  inst_lit_activity_moves:                0
% 2.43/0.98  inst_num_tautologies:                   0
% 2.43/0.98  inst_num_prop_implied:                  0
% 2.43/0.98  inst_num_existing_simplified:           0
% 2.43/0.98  inst_num_eq_res_simplified:             0
% 2.43/0.98  inst_num_child_elim:                    0
% 2.43/0.98  inst_num_of_dismatching_blockings:      96
% 2.43/0.98  inst_num_of_non_proper_insts:           1091
% 2.43/0.98  inst_num_of_duplicates:                 0
% 2.43/0.98  inst_inst_num_from_inst_to_res:         0
% 2.43/0.98  inst_dismatching_checking_time:         0.
% 2.43/0.98  
% 2.43/0.98  ------ Resolution
% 2.43/0.98  
% 2.43/0.98  res_num_of_clauses:                     0
% 2.43/0.98  res_num_in_passive:                     0
% 2.43/0.98  res_num_in_active:                      0
% 2.43/0.98  res_num_of_loops:                       101
% 2.43/0.98  res_forward_subset_subsumed:            101
% 2.43/0.98  res_backward_subset_subsumed:           0
% 2.43/0.98  res_forward_subsumed:                   0
% 2.43/0.98  res_backward_subsumed:                  0
% 2.43/0.98  res_forward_subsumption_resolution:     0
% 2.43/0.98  res_backward_subsumption_resolution:    0
% 2.43/0.98  res_clause_to_clause_subsumption:       823
% 2.43/0.98  res_orphan_elimination:                 0
% 2.43/0.98  res_tautology_del:                      260
% 2.43/0.98  res_num_eq_res_simplified:              1
% 2.43/0.98  res_num_sel_changes:                    0
% 2.43/0.98  res_moves_from_active_to_pass:          0
% 2.43/0.98  
% 2.43/0.98  ------ Superposition
% 2.43/0.98  
% 2.43/0.98  sup_time_total:                         0.
% 2.43/0.98  sup_time_generating:                    0.
% 2.43/0.98  sup_time_sim_full:                      0.
% 2.43/0.98  sup_time_sim_immed:                     0.
% 2.43/0.98  
% 2.43/0.98  sup_num_of_clauses:                     72
% 2.43/0.98  sup_num_in_active:                      27
% 2.43/0.98  sup_num_in_passive:                     45
% 2.43/0.98  sup_num_of_loops:                       88
% 2.43/0.98  sup_fw_superposition:                   164
% 2.43/0.98  sup_bw_superposition:                   43
% 2.43/0.98  sup_immediate_simplified:               87
% 2.43/0.98  sup_given_eliminated:                   0
% 2.43/0.98  comparisons_done:                       0
% 2.43/0.98  comparisons_avoided:                    12
% 2.43/0.98  
% 2.43/0.98  ------ Simplifications
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  sim_fw_subset_subsumed:                 45
% 2.43/0.98  sim_bw_subset_subsumed:                 11
% 2.43/0.98  sim_fw_subsumed:                        19
% 2.43/0.98  sim_bw_subsumed:                        11
% 2.43/0.98  sim_fw_subsumption_res:                 0
% 2.43/0.98  sim_bw_subsumption_res:                 2
% 2.43/0.98  sim_tautology_del:                      5
% 2.43/0.98  sim_eq_tautology_del:                   24
% 2.43/0.98  sim_eq_res_simp:                        3
% 2.43/0.98  sim_fw_demodulated:                     0
% 2.43/0.98  sim_bw_demodulated:                     57
% 2.43/0.98  sim_light_normalised:                   17
% 2.43/0.98  sim_joinable_taut:                      0
% 2.43/0.98  sim_joinable_simp:                      0
% 2.43/0.98  sim_ac_normalised:                      0
% 2.43/0.98  sim_smt_subsumption:                    0
% 2.43/0.98  
%------------------------------------------------------------------------------
