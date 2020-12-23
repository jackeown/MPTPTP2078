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
% DateTime   : Thu Dec  3 12:00:37 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_600)

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

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f28,plain,
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

fof(f29,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f28])).

fof(f51,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f54,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f45])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_392,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_394,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_23])).

cnf(c_1241,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1243,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2293,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1241,c_1243])).

cnf(c_2491,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_394,c_2293])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1242,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1247,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1244,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1705,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1244])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1249,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2459,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1249])).

cnf(c_3043,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1247,c_2459])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1245,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2292,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_1243])).

cnf(c_3163,plain,
    ( k1_relset_1(sK0,X0,sK3) = k1_relat_1(sK3)
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3043,c_2292])).

cnf(c_3349,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1242,c_3163])).

cnf(c_17,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_134,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_25])).

cnf(c_135,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_134])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_135])).

cnf(c_379,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_1240,plain,
    ( k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_3390,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3349,c_1240])).

cnf(c_29,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_507,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK1 != sK2
    | sK0 != sK0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_135,c_24])).

cnf(c_1402,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1403,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1402])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1413,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_758,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1487,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_1508,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_1650,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_1706,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1705])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1717,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_760,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1497,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,sK1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_1735,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(sK2,sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1497])).

cnf(c_1737,plain,
    ( r1_tarski(sK2,sK1)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 != sK1
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1735])).

cnf(c_1447,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK0,sK2))
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1754,plain,
    ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(sK0,sK2))
    | ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1447])).

cnf(c_2886,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_2887,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2886])).

cnf(c_2959,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
    | ~ r1_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2960,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2959])).

cnf(c_3393,plain,
    ( k1_relat_1(sK3) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3390,c_22,c_29,c_600,c_1402,c_1403,c_1413,c_1508,c_1705,c_1706,c_1717,c_1737,c_2886,c_2887,c_2959,c_2960])).

cnf(c_3396,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2491,c_3393])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3568,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3396,c_21])).

cnf(c_3569,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3568])).

cnf(c_3635,plain,
    ( k1_relat_1(sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3569,c_3393])).

cnf(c_3560,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3396,c_2293])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK1 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_480,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_1236,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_3564,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3396,c_1236])).

cnf(c_3576,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3564,c_3569])).

cnf(c_3577,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3576])).

cnf(c_3566,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3396,c_1241])).

cnf(c_3573,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3566,c_3569])).

cnf(c_3580,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3577,c_3573])).

cnf(c_3591,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3560,c_3569,c_3580])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3635,c_3591])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:56:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.70/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/0.98  
% 2.70/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/0.98  
% 2.70/0.98  ------  iProver source info
% 2.70/0.98  
% 2.70/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.70/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/0.98  git: non_committed_changes: false
% 2.70/0.98  git: last_make_outside_of_git: false
% 2.70/0.98  
% 2.70/0.98  ------ 
% 2.70/0.98  
% 2.70/0.98  ------ Input Options
% 2.70/0.98  
% 2.70/0.98  --out_options                           all
% 2.70/0.98  --tptp_safe_out                         true
% 2.70/0.98  --problem_path                          ""
% 2.70/0.98  --include_path                          ""
% 2.70/0.98  --clausifier                            res/vclausify_rel
% 2.70/0.98  --clausifier_options                    --mode clausify
% 2.70/0.98  --stdin                                 false
% 2.70/0.98  --stats_out                             all
% 2.70/0.98  
% 2.70/0.98  ------ General Options
% 2.70/0.98  
% 2.70/0.98  --fof                                   false
% 2.70/0.98  --time_out_real                         305.
% 2.70/0.98  --time_out_virtual                      -1.
% 2.70/0.98  --symbol_type_check                     false
% 2.70/0.98  --clausify_out                          false
% 2.70/0.98  --sig_cnt_out                           false
% 2.70/0.98  --trig_cnt_out                          false
% 2.70/0.98  --trig_cnt_out_tolerance                1.
% 2.70/0.98  --trig_cnt_out_sk_spl                   false
% 2.70/0.98  --abstr_cl_out                          false
% 2.70/0.98  
% 2.70/0.98  ------ Global Options
% 2.70/0.98  
% 2.70/0.98  --schedule                              default
% 2.70/0.98  --add_important_lit                     false
% 2.70/0.98  --prop_solver_per_cl                    1000
% 2.70/0.98  --min_unsat_core                        false
% 2.70/0.98  --soft_assumptions                      false
% 2.70/0.98  --soft_lemma_size                       3
% 2.70/0.98  --prop_impl_unit_size                   0
% 2.70/0.98  --prop_impl_unit                        []
% 2.70/0.98  --share_sel_clauses                     true
% 2.70/0.98  --reset_solvers                         false
% 2.70/0.98  --bc_imp_inh                            [conj_cone]
% 2.70/0.98  --conj_cone_tolerance                   3.
% 2.70/0.98  --extra_neg_conj                        none
% 2.70/0.98  --large_theory_mode                     true
% 2.70/0.98  --prolific_symb_bound                   200
% 2.70/0.98  --lt_threshold                          2000
% 2.70/0.98  --clause_weak_htbl                      true
% 2.70/0.98  --gc_record_bc_elim                     false
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing Options
% 2.70/0.98  
% 2.70/0.98  --preprocessing_flag                    true
% 2.70/0.98  --time_out_prep_mult                    0.1
% 2.70/0.98  --splitting_mode                        input
% 2.70/0.98  --splitting_grd                         true
% 2.70/0.98  --splitting_cvd                         false
% 2.70/0.98  --splitting_cvd_svl                     false
% 2.70/0.98  --splitting_nvd                         32
% 2.70/0.98  --sub_typing                            true
% 2.70/0.98  --prep_gs_sim                           true
% 2.70/0.98  --prep_unflatten                        true
% 2.70/0.98  --prep_res_sim                          true
% 2.70/0.98  --prep_upred                            true
% 2.70/0.98  --prep_sem_filter                       exhaustive
% 2.70/0.98  --prep_sem_filter_out                   false
% 2.70/0.98  --pred_elim                             true
% 2.70/0.98  --res_sim_input                         true
% 2.70/0.98  --eq_ax_congr_red                       true
% 2.70/0.98  --pure_diseq_elim                       true
% 2.70/0.98  --brand_transform                       false
% 2.70/0.98  --non_eq_to_eq                          false
% 2.70/0.98  --prep_def_merge                        true
% 2.70/0.98  --prep_def_merge_prop_impl              false
% 2.70/0.98  --prep_def_merge_mbd                    true
% 2.70/0.98  --prep_def_merge_tr_red                 false
% 2.70/0.98  --prep_def_merge_tr_cl                  false
% 2.70/0.98  --smt_preprocessing                     true
% 2.70/0.98  --smt_ac_axioms                         fast
% 2.70/0.98  --preprocessed_out                      false
% 2.70/0.98  --preprocessed_stats                    false
% 2.70/0.98  
% 2.70/0.98  ------ Abstraction refinement Options
% 2.70/0.98  
% 2.70/0.98  --abstr_ref                             []
% 2.70/0.98  --abstr_ref_prep                        false
% 2.70/0.98  --abstr_ref_until_sat                   false
% 2.70/0.98  --abstr_ref_sig_restrict                funpre
% 2.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.98  --abstr_ref_under                       []
% 2.70/0.98  
% 2.70/0.98  ------ SAT Options
% 2.70/0.98  
% 2.70/0.98  --sat_mode                              false
% 2.70/0.98  --sat_fm_restart_options                ""
% 2.70/0.98  --sat_gr_def                            false
% 2.70/0.98  --sat_epr_types                         true
% 2.70/0.98  --sat_non_cyclic_types                  false
% 2.70/0.98  --sat_finite_models                     false
% 2.70/0.98  --sat_fm_lemmas                         false
% 2.70/0.98  --sat_fm_prep                           false
% 2.70/0.98  --sat_fm_uc_incr                        true
% 2.70/0.98  --sat_out_model                         small
% 2.70/0.98  --sat_out_clauses                       false
% 2.70/0.98  
% 2.70/0.98  ------ QBF Options
% 2.70/0.98  
% 2.70/0.98  --qbf_mode                              false
% 2.70/0.98  --qbf_elim_univ                         false
% 2.70/0.98  --qbf_dom_inst                          none
% 2.70/0.98  --qbf_dom_pre_inst                      false
% 2.70/0.98  --qbf_sk_in                             false
% 2.70/0.98  --qbf_pred_elim                         true
% 2.70/0.98  --qbf_split                             512
% 2.70/0.98  
% 2.70/0.98  ------ BMC1 Options
% 2.70/0.98  
% 2.70/0.98  --bmc1_incremental                      false
% 2.70/0.98  --bmc1_axioms                           reachable_all
% 2.70/0.98  --bmc1_min_bound                        0
% 2.70/0.98  --bmc1_max_bound                        -1
% 2.70/0.98  --bmc1_max_bound_default                -1
% 2.70/0.98  --bmc1_symbol_reachability              true
% 2.70/0.98  --bmc1_property_lemmas                  false
% 2.70/0.98  --bmc1_k_induction                      false
% 2.70/0.98  --bmc1_non_equiv_states                 false
% 2.70/0.98  --bmc1_deadlock                         false
% 2.70/0.98  --bmc1_ucm                              false
% 2.70/0.98  --bmc1_add_unsat_core                   none
% 2.70/0.98  --bmc1_unsat_core_children              false
% 2.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.98  --bmc1_out_stat                         full
% 2.70/0.98  --bmc1_ground_init                      false
% 2.70/0.98  --bmc1_pre_inst_next_state              false
% 2.70/0.98  --bmc1_pre_inst_state                   false
% 2.70/0.98  --bmc1_pre_inst_reach_state             false
% 2.70/0.98  --bmc1_out_unsat_core                   false
% 2.70/0.98  --bmc1_aig_witness_out                  false
% 2.70/0.98  --bmc1_verbose                          false
% 2.70/0.98  --bmc1_dump_clauses_tptp                false
% 2.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.98  --bmc1_dump_file                        -
% 2.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.98  --bmc1_ucm_extend_mode                  1
% 2.70/0.98  --bmc1_ucm_init_mode                    2
% 2.70/0.98  --bmc1_ucm_cone_mode                    none
% 2.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.98  --bmc1_ucm_relax_model                  4
% 2.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.98  --bmc1_ucm_layered_model                none
% 2.70/0.98  --bmc1_ucm_max_lemma_size               10
% 2.70/0.98  
% 2.70/0.98  ------ AIG Options
% 2.70/0.98  
% 2.70/0.98  --aig_mode                              false
% 2.70/0.98  
% 2.70/0.98  ------ Instantiation Options
% 2.70/0.98  
% 2.70/0.98  --instantiation_flag                    true
% 2.70/0.98  --inst_sos_flag                         false
% 2.70/0.98  --inst_sos_phase                        true
% 2.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.98  --inst_lit_sel_side                     num_symb
% 2.70/0.98  --inst_solver_per_active                1400
% 2.70/0.98  --inst_solver_calls_frac                1.
% 2.70/0.98  --inst_passive_queue_type               priority_queues
% 2.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.98  --inst_passive_queues_freq              [25;2]
% 2.70/0.98  --inst_dismatching                      true
% 2.70/0.98  --inst_eager_unprocessed_to_passive     true
% 2.70/0.98  --inst_prop_sim_given                   true
% 2.70/0.98  --inst_prop_sim_new                     false
% 2.70/0.98  --inst_subs_new                         false
% 2.70/0.98  --inst_eq_res_simp                      false
% 2.70/0.98  --inst_subs_given                       false
% 2.70/0.98  --inst_orphan_elimination               true
% 2.70/0.98  --inst_learning_loop_flag               true
% 2.70/0.98  --inst_learning_start                   3000
% 2.70/0.98  --inst_learning_factor                  2
% 2.70/0.98  --inst_start_prop_sim_after_learn       3
% 2.70/0.98  --inst_sel_renew                        solver
% 2.70/0.98  --inst_lit_activity_flag                true
% 2.70/0.98  --inst_restr_to_given                   false
% 2.70/0.98  --inst_activity_threshold               500
% 2.70/0.98  --inst_out_proof                        true
% 2.70/0.98  
% 2.70/0.98  ------ Resolution Options
% 2.70/0.98  
% 2.70/0.98  --resolution_flag                       true
% 2.70/0.98  --res_lit_sel                           adaptive
% 2.70/0.98  --res_lit_sel_side                      none
% 2.70/0.98  --res_ordering                          kbo
% 2.70/0.98  --res_to_prop_solver                    active
% 2.70/0.98  --res_prop_simpl_new                    false
% 2.70/0.98  --res_prop_simpl_given                  true
% 2.70/0.98  --res_passive_queue_type                priority_queues
% 2.70/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.98  --res_passive_queues_freq               [15;5]
% 2.70/0.98  --res_forward_subs                      full
% 2.70/0.98  --res_backward_subs                     full
% 2.70/0.98  --res_forward_subs_resolution           true
% 2.70/0.98  --res_backward_subs_resolution          true
% 2.70/0.98  --res_orphan_elimination                true
% 2.70/0.98  --res_time_limit                        2.
% 2.70/0.98  --res_out_proof                         true
% 2.70/0.98  
% 2.70/0.98  ------ Superposition Options
% 2.70/0.98  
% 2.70/0.98  --superposition_flag                    true
% 2.70/0.98  --sup_passive_queue_type                priority_queues
% 2.70/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.98  --demod_completeness_check              fast
% 2.70/0.98  --demod_use_ground                      true
% 2.70/0.98  --sup_to_prop_solver                    passive
% 2.70/0.98  --sup_prop_simpl_new                    true
% 2.70/0.98  --sup_prop_simpl_given                  true
% 2.70/0.98  --sup_fun_splitting                     false
% 2.70/0.98  --sup_smt_interval                      50000
% 2.70/0.98  
% 2.70/0.98  ------ Superposition Simplification Setup
% 2.70/0.98  
% 2.70/0.98  --sup_indices_passive                   []
% 2.70/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_full_bw                           [BwDemod]
% 2.70/0.98  --sup_immed_triv                        [TrivRules]
% 2.70/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_immed_bw_main                     []
% 2.70/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.98  
% 2.70/0.98  ------ Combination Options
% 2.70/0.98  
% 2.70/0.98  --comb_res_mult                         3
% 2.70/0.98  --comb_sup_mult                         2
% 2.70/0.98  --comb_inst_mult                        10
% 2.70/0.98  
% 2.70/0.98  ------ Debug Options
% 2.70/0.98  
% 2.70/0.98  --dbg_backtrace                         false
% 2.70/0.98  --dbg_dump_prop_clauses                 false
% 2.70/0.98  --dbg_dump_prop_clauses_file            -
% 2.70/0.98  --dbg_out_stat                          false
% 2.70/0.98  ------ Parsing...
% 2.70/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/0.98  ------ Proving...
% 2.70/0.98  ------ Problem Properties 
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  clauses                                 24
% 2.70/0.98  conjectures                             3
% 2.70/0.98  EPR                                     7
% 2.70/0.98  Horn                                    21
% 2.70/0.98  unary                                   4
% 2.70/0.98  binary                                  11
% 2.70/0.98  lits                                    58
% 2.70/0.98  lits eq                                 21
% 2.70/0.98  fd_pure                                 0
% 2.70/0.98  fd_pseudo                               0
% 2.70/0.98  fd_cond                                 0
% 2.70/0.98  fd_pseudo_cond                          1
% 2.70/0.98  AC symbols                              0
% 2.70/0.98  
% 2.70/0.98  ------ Schedule dynamic 5 is on 
% 2.70/0.98  
% 2.70/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  ------ 
% 2.70/0.98  Current options:
% 2.70/0.98  ------ 
% 2.70/0.98  
% 2.70/0.98  ------ Input Options
% 2.70/0.98  
% 2.70/0.98  --out_options                           all
% 2.70/0.98  --tptp_safe_out                         true
% 2.70/0.98  --problem_path                          ""
% 2.70/0.98  --include_path                          ""
% 2.70/0.98  --clausifier                            res/vclausify_rel
% 2.70/0.98  --clausifier_options                    --mode clausify
% 2.70/0.98  --stdin                                 false
% 2.70/0.98  --stats_out                             all
% 2.70/0.98  
% 2.70/0.98  ------ General Options
% 2.70/0.98  
% 2.70/0.98  --fof                                   false
% 2.70/0.98  --time_out_real                         305.
% 2.70/0.98  --time_out_virtual                      -1.
% 2.70/0.98  --symbol_type_check                     false
% 2.70/0.98  --clausify_out                          false
% 2.70/0.98  --sig_cnt_out                           false
% 2.70/0.98  --trig_cnt_out                          false
% 2.70/0.98  --trig_cnt_out_tolerance                1.
% 2.70/0.98  --trig_cnt_out_sk_spl                   false
% 2.70/0.98  --abstr_cl_out                          false
% 2.70/0.98  
% 2.70/0.98  ------ Global Options
% 2.70/0.98  
% 2.70/0.98  --schedule                              default
% 2.70/0.98  --add_important_lit                     false
% 2.70/0.98  --prop_solver_per_cl                    1000
% 2.70/0.98  --min_unsat_core                        false
% 2.70/0.98  --soft_assumptions                      false
% 2.70/0.98  --soft_lemma_size                       3
% 2.70/0.98  --prop_impl_unit_size                   0
% 2.70/0.98  --prop_impl_unit                        []
% 2.70/0.98  --share_sel_clauses                     true
% 2.70/0.98  --reset_solvers                         false
% 2.70/0.98  --bc_imp_inh                            [conj_cone]
% 2.70/0.98  --conj_cone_tolerance                   3.
% 2.70/0.98  --extra_neg_conj                        none
% 2.70/0.98  --large_theory_mode                     true
% 2.70/0.98  --prolific_symb_bound                   200
% 2.70/0.98  --lt_threshold                          2000
% 2.70/0.98  --clause_weak_htbl                      true
% 2.70/0.98  --gc_record_bc_elim                     false
% 2.70/0.98  
% 2.70/0.98  ------ Preprocessing Options
% 2.70/0.98  
% 2.70/0.98  --preprocessing_flag                    true
% 2.70/0.98  --time_out_prep_mult                    0.1
% 2.70/0.98  --splitting_mode                        input
% 2.70/0.98  --splitting_grd                         true
% 2.70/0.98  --splitting_cvd                         false
% 2.70/0.98  --splitting_cvd_svl                     false
% 2.70/0.98  --splitting_nvd                         32
% 2.70/0.98  --sub_typing                            true
% 2.70/0.98  --prep_gs_sim                           true
% 2.70/0.98  --prep_unflatten                        true
% 2.70/0.98  --prep_res_sim                          true
% 2.70/0.98  --prep_upred                            true
% 2.70/0.98  --prep_sem_filter                       exhaustive
% 2.70/0.98  --prep_sem_filter_out                   false
% 2.70/0.98  --pred_elim                             true
% 2.70/0.98  --res_sim_input                         true
% 2.70/0.98  --eq_ax_congr_red                       true
% 2.70/0.98  --pure_diseq_elim                       true
% 2.70/0.98  --brand_transform                       false
% 2.70/0.98  --non_eq_to_eq                          false
% 2.70/0.98  --prep_def_merge                        true
% 2.70/0.98  --prep_def_merge_prop_impl              false
% 2.70/0.98  --prep_def_merge_mbd                    true
% 2.70/0.98  --prep_def_merge_tr_red                 false
% 2.70/0.98  --prep_def_merge_tr_cl                  false
% 2.70/0.98  --smt_preprocessing                     true
% 2.70/0.98  --smt_ac_axioms                         fast
% 2.70/0.98  --preprocessed_out                      false
% 2.70/0.98  --preprocessed_stats                    false
% 2.70/0.98  
% 2.70/0.98  ------ Abstraction refinement Options
% 2.70/0.98  
% 2.70/0.98  --abstr_ref                             []
% 2.70/0.98  --abstr_ref_prep                        false
% 2.70/0.98  --abstr_ref_until_sat                   false
% 2.70/0.98  --abstr_ref_sig_restrict                funpre
% 2.70/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.98  --abstr_ref_under                       []
% 2.70/0.98  
% 2.70/0.98  ------ SAT Options
% 2.70/0.98  
% 2.70/0.98  --sat_mode                              false
% 2.70/0.98  --sat_fm_restart_options                ""
% 2.70/0.98  --sat_gr_def                            false
% 2.70/0.98  --sat_epr_types                         true
% 2.70/0.98  --sat_non_cyclic_types                  false
% 2.70/0.98  --sat_finite_models                     false
% 2.70/0.98  --sat_fm_lemmas                         false
% 2.70/0.98  --sat_fm_prep                           false
% 2.70/0.98  --sat_fm_uc_incr                        true
% 2.70/0.98  --sat_out_model                         small
% 2.70/0.98  --sat_out_clauses                       false
% 2.70/0.98  
% 2.70/0.98  ------ QBF Options
% 2.70/0.98  
% 2.70/0.98  --qbf_mode                              false
% 2.70/0.98  --qbf_elim_univ                         false
% 2.70/0.98  --qbf_dom_inst                          none
% 2.70/0.98  --qbf_dom_pre_inst                      false
% 2.70/0.98  --qbf_sk_in                             false
% 2.70/0.98  --qbf_pred_elim                         true
% 2.70/0.98  --qbf_split                             512
% 2.70/0.98  
% 2.70/0.98  ------ BMC1 Options
% 2.70/0.98  
% 2.70/0.98  --bmc1_incremental                      false
% 2.70/0.98  --bmc1_axioms                           reachable_all
% 2.70/0.98  --bmc1_min_bound                        0
% 2.70/0.98  --bmc1_max_bound                        -1
% 2.70/0.98  --bmc1_max_bound_default                -1
% 2.70/0.98  --bmc1_symbol_reachability              true
% 2.70/0.98  --bmc1_property_lemmas                  false
% 2.70/0.98  --bmc1_k_induction                      false
% 2.70/0.98  --bmc1_non_equiv_states                 false
% 2.70/0.98  --bmc1_deadlock                         false
% 2.70/0.98  --bmc1_ucm                              false
% 2.70/0.98  --bmc1_add_unsat_core                   none
% 2.70/0.98  --bmc1_unsat_core_children              false
% 2.70/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.98  --bmc1_out_stat                         full
% 2.70/0.98  --bmc1_ground_init                      false
% 2.70/0.98  --bmc1_pre_inst_next_state              false
% 2.70/0.98  --bmc1_pre_inst_state                   false
% 2.70/0.98  --bmc1_pre_inst_reach_state             false
% 2.70/0.98  --bmc1_out_unsat_core                   false
% 2.70/0.98  --bmc1_aig_witness_out                  false
% 2.70/0.98  --bmc1_verbose                          false
% 2.70/0.98  --bmc1_dump_clauses_tptp                false
% 2.70/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.98  --bmc1_dump_file                        -
% 2.70/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.98  --bmc1_ucm_extend_mode                  1
% 2.70/0.98  --bmc1_ucm_init_mode                    2
% 2.70/0.98  --bmc1_ucm_cone_mode                    none
% 2.70/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.98  --bmc1_ucm_relax_model                  4
% 2.70/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.98  --bmc1_ucm_layered_model                none
% 2.70/0.98  --bmc1_ucm_max_lemma_size               10
% 2.70/0.98  
% 2.70/0.98  ------ AIG Options
% 2.70/0.98  
% 2.70/0.98  --aig_mode                              false
% 2.70/0.98  
% 2.70/0.98  ------ Instantiation Options
% 2.70/0.98  
% 2.70/0.98  --instantiation_flag                    true
% 2.70/0.98  --inst_sos_flag                         false
% 2.70/0.98  --inst_sos_phase                        true
% 2.70/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.98  --inst_lit_sel_side                     none
% 2.70/0.98  --inst_solver_per_active                1400
% 2.70/0.98  --inst_solver_calls_frac                1.
% 2.70/0.98  --inst_passive_queue_type               priority_queues
% 2.70/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.98  --inst_passive_queues_freq              [25;2]
% 2.70/0.98  --inst_dismatching                      true
% 2.70/0.98  --inst_eager_unprocessed_to_passive     true
% 2.70/0.98  --inst_prop_sim_given                   true
% 2.70/0.98  --inst_prop_sim_new                     false
% 2.70/0.98  --inst_subs_new                         false
% 2.70/0.98  --inst_eq_res_simp                      false
% 2.70/0.98  --inst_subs_given                       false
% 2.70/0.98  --inst_orphan_elimination               true
% 2.70/0.98  --inst_learning_loop_flag               true
% 2.70/0.98  --inst_learning_start                   3000
% 2.70/0.98  --inst_learning_factor                  2
% 2.70/0.98  --inst_start_prop_sim_after_learn       3
% 2.70/0.98  --inst_sel_renew                        solver
% 2.70/0.98  --inst_lit_activity_flag                true
% 2.70/0.98  --inst_restr_to_given                   false
% 2.70/0.98  --inst_activity_threshold               500
% 2.70/0.98  --inst_out_proof                        true
% 2.70/0.98  
% 2.70/0.98  ------ Resolution Options
% 2.70/0.98  
% 2.70/0.98  --resolution_flag                       false
% 2.70/0.98  --res_lit_sel                           adaptive
% 2.70/0.98  --res_lit_sel_side                      none
% 2.70/0.98  --res_ordering                          kbo
% 2.70/0.98  --res_to_prop_solver                    active
% 2.70/0.98  --res_prop_simpl_new                    false
% 2.70/0.98  --res_prop_simpl_given                  true
% 2.70/0.98  --res_passive_queue_type                priority_queues
% 2.70/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.98  --res_passive_queues_freq               [15;5]
% 2.70/0.98  --res_forward_subs                      full
% 2.70/0.98  --res_backward_subs                     full
% 2.70/0.98  --res_forward_subs_resolution           true
% 2.70/0.98  --res_backward_subs_resolution          true
% 2.70/0.98  --res_orphan_elimination                true
% 2.70/0.98  --res_time_limit                        2.
% 2.70/0.98  --res_out_proof                         true
% 2.70/0.98  
% 2.70/0.98  ------ Superposition Options
% 2.70/0.98  
% 2.70/0.98  --superposition_flag                    true
% 2.70/0.98  --sup_passive_queue_type                priority_queues
% 2.70/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.98  --demod_completeness_check              fast
% 2.70/0.98  --demod_use_ground                      true
% 2.70/0.98  --sup_to_prop_solver                    passive
% 2.70/0.98  --sup_prop_simpl_new                    true
% 2.70/0.98  --sup_prop_simpl_given                  true
% 2.70/0.98  --sup_fun_splitting                     false
% 2.70/0.98  --sup_smt_interval                      50000
% 2.70/0.98  
% 2.70/0.98  ------ Superposition Simplification Setup
% 2.70/0.98  
% 2.70/0.98  --sup_indices_passive                   []
% 2.70/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_full_bw                           [BwDemod]
% 2.70/0.98  --sup_immed_triv                        [TrivRules]
% 2.70/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_immed_bw_main                     []
% 2.70/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.98  
% 2.70/0.98  ------ Combination Options
% 2.70/0.98  
% 2.70/0.98  --comb_res_mult                         3
% 2.70/0.98  --comb_sup_mult                         2
% 2.70/0.98  --comb_inst_mult                        10
% 2.70/0.98  
% 2.70/0.98  ------ Debug Options
% 2.70/0.98  
% 2.70/0.98  --dbg_backtrace                         false
% 2.70/0.98  --dbg_dump_prop_clauses                 false
% 2.70/0.98  --dbg_dump_prop_clauses_file            -
% 2.70/0.98  --dbg_out_stat                          false
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  ------ Proving...
% 2.70/0.98  
% 2.70/0.98  
% 2.70/0.98  % SZS status Theorem for theBenchmark.p
% 2.70/0.98  
% 2.70/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/0.98  
% 2.70/0.98  fof(f10,axiom,(
% 2.70/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.98  
% 2.70/0.98  fof(f20,plain,(
% 2.70/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.98    inference(ennf_transformation,[],[f10])).
% 2.70/0.98  
% 2.70/0.98  fof(f21,plain,(
% 2.70/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.98    inference(flattening,[],[f20])).
% 2.70/0.98  
% 2.70/0.98  fof(f27,plain,(
% 2.70/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.98    inference(nnf_transformation,[],[f21])).
% 2.70/0.98  
% 2.70/0.98  fof(f44,plain,(
% 2.70/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.98    inference(cnf_transformation,[],[f27])).
% 2.70/0.98  
% 2.70/0.98  fof(f11,conjecture,(
% 2.70/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.98  
% 2.70/0.98  fof(f12,negated_conjecture,(
% 2.70/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.70/0.98    inference(negated_conjecture,[],[f11])).
% 2.70/0.98  
% 2.70/0.98  fof(f22,plain,(
% 2.70/0.98    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.70/0.98    inference(ennf_transformation,[],[f12])).
% 2.70/0.98  
% 2.70/0.98  fof(f23,plain,(
% 2.70/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.70/0.98    inference(flattening,[],[f22])).
% 2.70/0.98  
% 2.70/0.98  fof(f28,plain,(
% 2.70/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.70/0.98    introduced(choice_axiom,[])).
% 2.70/0.98  
% 2.70/0.98  fof(f29,plain,(
% 2.70/0.98    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.70/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f28])).
% 2.70/0.98  
% 2.70/0.98  fof(f51,plain,(
% 2.70/0.98    v1_funct_2(sK3,sK0,sK1)),
% 2.70/0.98    inference(cnf_transformation,[],[f29])).
% 2.70/0.98  
% 2.70/0.98  fof(f52,plain,(
% 2.70/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.70/0.98    inference(cnf_transformation,[],[f29])).
% 2.70/0.98  
% 2.70/0.98  fof(f7,axiom,(
% 2.70/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.98  
% 2.70/0.98  fof(f16,plain,(
% 2.70/0.98    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.70/0.98    inference(ennf_transformation,[],[f7])).
% 2.70/0.98  
% 2.70/0.98  fof(f40,plain,(
% 2.70/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.98    inference(cnf_transformation,[],[f16])).
% 2.70/0.98  
% 2.70/0.98  fof(f53,plain,(
% 2.70/0.98    r1_tarski(sK1,sK2)),
% 2.70/0.98    inference(cnf_transformation,[],[f29])).
% 2.70/0.98  
% 2.70/0.98  fof(f5,axiom,(
% 2.70/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 2.70/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.98  
% 2.70/0.98  fof(f15,plain,(
% 2.70/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 2.70/0.98    inference(ennf_transformation,[],[f5])).
% 2.70/0.99  
% 2.70/0.99  fof(f37,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f15])).
% 2.70/0.99  
% 2.70/0.99  fof(f6,axiom,(
% 2.70/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f26,plain,(
% 2.70/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.70/0.99    inference(nnf_transformation,[],[f6])).
% 2.70/0.99  
% 2.70/0.99  fof(f38,plain,(
% 2.70/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f26])).
% 2.70/0.99  
% 2.70/0.99  fof(f3,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f13,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.70/0.99    inference(ennf_transformation,[],[f3])).
% 2.70/0.99  
% 2.70/0.99  fof(f14,plain,(
% 2.70/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.70/0.99    inference(flattening,[],[f13])).
% 2.70/0.99  
% 2.70/0.99  fof(f34,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f14])).
% 2.70/0.99  
% 2.70/0.99  fof(f39,plain,(
% 2.70/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f26])).
% 2.70/0.99  
% 2.70/0.99  fof(f46,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f27])).
% 2.70/0.99  
% 2.70/0.99  fof(f55,plain,(
% 2.70/0.99    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 2.70/0.99    inference(cnf_transformation,[],[f29])).
% 2.70/0.99  
% 2.70/0.99  fof(f50,plain,(
% 2.70/0.99    v1_funct_1(sK3)),
% 2.70/0.99    inference(cnf_transformation,[],[f29])).
% 2.70/0.99  
% 2.70/0.99  fof(f2,axiom,(
% 2.70/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f24,plain,(
% 2.70/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.70/0.99    inference(nnf_transformation,[],[f2])).
% 2.70/0.99  
% 2.70/0.99  fof(f25,plain,(
% 2.70/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.70/0.99    inference(flattening,[],[f24])).
% 2.70/0.99  
% 2.70/0.99  fof(f33,plain,(
% 2.70/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f25])).
% 2.70/0.99  
% 2.70/0.99  fof(f4,axiom,(
% 2.70/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f35,plain,(
% 2.70/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f4])).
% 2.70/0.99  
% 2.70/0.99  fof(f54,plain,(
% 2.70/0.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.70/0.99    inference(cnf_transformation,[],[f29])).
% 2.70/0.99  
% 2.70/0.99  fof(f45,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f27])).
% 2.70/0.99  
% 2.70/0.99  fof(f62,plain,(
% 2.70/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.70/0.99    inference(equality_resolution,[],[f45])).
% 2.70/0.99  
% 2.70/0.99  cnf(c_19,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.70/0.99      | k1_xboole_0 = X2 ),
% 2.70/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_24,negated_conjecture,
% 2.70/0.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_391,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.70/0.99      | sK1 != X2
% 2.70/0.99      | sK0 != X1
% 2.70/0.99      | sK3 != X0
% 2.70/0.99      | k1_xboole_0 = X2 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_392,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.70/0.99      | k1_relset_1(sK0,sK1,sK3) = sK0
% 2.70/0.99      | k1_xboole_0 = sK1 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_391]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_23,negated_conjecture,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.70/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_394,plain,
% 2.70/0.99      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_392,c_23]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1241,plain,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_10,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1243,plain,
% 2.70/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.70/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2293,plain,
% 2.70/0.99      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1241,c_1243]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2491,plain,
% 2.70/0.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_394,c_2293]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_22,negated_conjecture,
% 2.70/0.99      ( r1_tarski(sK1,sK2) ),
% 2.70/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1242,plain,
% 2.70/0.99      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_6,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1)
% 2.70/0.99      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 2.70/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1247,plain,
% 2.70/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.70/0.99      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_9,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1244,plain,
% 2.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.70/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1705,plain,
% 2.70/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1241,c_1244]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_4,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.70/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1249,plain,
% 2.70/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.70/0.99      | r1_tarski(X1,X2) != iProver_top
% 2.70/0.99      | r1_tarski(X0,X2) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2459,plain,
% 2.70/0.99      ( r1_tarski(k2_zfmisc_1(sK0,sK1),X0) != iProver_top
% 2.70/0.99      | r1_tarski(sK3,X0) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1705,c_1249]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3043,plain,
% 2.70/0.99      ( r1_tarski(sK1,X0) != iProver_top
% 2.70/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK0,X0)) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1247,c_2459]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_8,plain,
% 2.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1245,plain,
% 2.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.70/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2292,plain,
% 2.70/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.70/0.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1245,c_1243]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3163,plain,
% 2.70/0.99      ( k1_relset_1(sK0,X0,sK3) = k1_relat_1(sK3)
% 2.70/0.99      | r1_tarski(sK1,X0) != iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_3043,c_2292]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3349,plain,
% 2.70/0.99      ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1242,c_3163]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_17,plain,
% 2.70/0.99      ( v1_funct_2(X0,X1,X2)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.70/0.99      | k1_xboole_0 = X2 ),
% 2.70/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_20,negated_conjecture,
% 2.70/0.99      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.70/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.70/0.99      | ~ v1_funct_1(sK3) ),
% 2.70/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_25,negated_conjecture,
% 2.70/0.99      ( v1_funct_1(sK3) ),
% 2.70/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_134,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.70/0.99      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_20,c_25]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_135,negated_conjecture,
% 2.70/0.99      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.70/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.70/0.99      inference(renaming,[status(thm)],[c_134]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_378,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.70/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.70/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.70/0.99      | sK2 != X2
% 2.70/0.99      | sK0 != X1
% 2.70/0.99      | sK3 != X0
% 2.70/0.99      | k1_xboole_0 = X2 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_135]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_379,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.70/0.99      | k1_relset_1(sK0,sK2,sK3) != sK0
% 2.70/0.99      | k1_xboole_0 = sK2 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_378]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1240,plain,
% 2.70/0.99      ( k1_relset_1(sK0,sK2,sK3) != sK0
% 2.70/0.99      | k1_xboole_0 = sK2
% 2.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3390,plain,
% 2.70/0.99      ( k1_relat_1(sK3) != sK0
% 2.70/0.99      | sK2 = k1_xboole_0
% 2.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_3349,c_1240]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_29,plain,
% 2.70/0.99      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_507,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.70/0.99      | sK1 != sK2
% 2.70/0.99      | sK0 != sK0
% 2.70/0.99      | sK3 != sK3 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_135,c_24]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1402,plain,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.70/0.99      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1403,plain,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 2.70/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1402]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.70/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1413,plain,
% 2.70/0.99      ( ~ r1_tarski(sK1,sK2) | ~ r1_tarski(sK2,sK1) | sK1 = sK2 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_758,plain,( X0 = X0 ),theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1487,plain,
% 2.70/0.99      ( sK0 = sK0 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_758]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1508,plain,
% 2.70/0.99      ( sK1 = sK1 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_758]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1650,plain,
% 2.70/0.99      ( sK3 = sK3 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_758]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1706,plain,
% 2.70/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 2.70/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1705]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_5,plain,
% 2.70/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1717,plain,
% 2.70/0.99      ( r1_tarski(k1_xboole_0,sK1) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_760,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.70/0.99      theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1497,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,sK1) | sK1 != X1 | sK2 != X0 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_760]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1735,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,sK1)
% 2.70/0.99      | r1_tarski(sK2,sK1)
% 2.70/0.99      | sK1 != sK1
% 2.70/0.99      | sK2 != X0 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1497]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1737,plain,
% 2.70/0.99      ( r1_tarski(sK2,sK1)
% 2.70/0.99      | ~ r1_tarski(k1_xboole_0,sK1)
% 2.70/0.99      | sK1 != sK1
% 2.70/0.99      | sK2 != k1_xboole_0 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1735]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1447,plain,
% 2.70/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(sK0,sK2))
% 2.70/0.99      | ~ r1_tarski(sK3,X0)
% 2.70/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1754,plain,
% 2.70/0.99      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(sK0,sK2))
% 2.70/0.99      | ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
% 2.70/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1447]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2886,plain,
% 2.70/0.99      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
% 2.70/0.99      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 2.70/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1754]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2887,plain,
% 2.70/0.99      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) != iProver_top
% 2.70/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.70/0.99      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2886]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2959,plain,
% 2.70/0.99      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
% 2.70/0.99      | ~ r1_tarski(sK1,sK2) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2960,plain,
% 2.70/0.99      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) = iProver_top
% 2.70/0.99      | r1_tarski(sK1,sK2) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_2959]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3393,plain,
% 2.70/0.99      ( k1_relat_1(sK3) != sK0 ),
% 2.70/0.99      inference(global_propositional_subsumption,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_3390,c_22,c_29,c_600,c_1402,c_1403,c_1413,c_1508,
% 2.70/0.99                 c_1705,c_1706,c_1717,c_1737,c_2886,c_2887,c_2959,c_2960]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3396,plain,
% 2.70/0.99      ( sK1 = k1_xboole_0 ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2491,c_3393]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_21,negated_conjecture,
% 2.70/0.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 2.70/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3568,plain,
% 2.70/0.99      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_3396,c_21]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3569,plain,
% 2.70/0.99      ( sK0 = k1_xboole_0 ),
% 2.70/0.99      inference(equality_resolution_simp,[status(thm)],[c_3568]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3635,plain,
% 2.70/0.99      ( k1_relat_1(sK3) != k1_xboole_0 ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_3569,c_3393]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3560,plain,
% 2.70/0.99      ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_3396,c_2293]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_18,plain,
% 2.70/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.70/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.70/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_479,plain,
% 2.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.70/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.70/0.99      | sK1 != X1
% 2.70/0.99      | sK0 != k1_xboole_0
% 2.70/0.99      | sK3 != X0 ),
% 2.70/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_480,plain,
% 2.70/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.70/0.99      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.70/0.99      | sK0 != k1_xboole_0 ),
% 2.70/0.99      inference(unflattening,[status(thm)],[c_479]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1236,plain,
% 2.70/0.99      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.70/0.99      | sK0 != k1_xboole_0
% 2.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3564,plain,
% 2.70/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 2.70/0.99      | sK0 != k1_xboole_0
% 2.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_3396,c_1236]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3576,plain,
% 2.70/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 2.70/0.99      | k1_xboole_0 != k1_xboole_0
% 2.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.70/0.99      inference(light_normalisation,[status(thm)],[c_3564,c_3569]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3577,plain,
% 2.70/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 2.70/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.70/0.99      inference(equality_resolution_simp,[status(thm)],[c_3576]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3566,plain,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 2.70/0.99      inference(demodulation,[status(thm)],[c_3396,c_1241]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3573,plain,
% 2.70/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.70/0.99      inference(light_normalisation,[status(thm)],[c_3566,c_3569]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3580,plain,
% 2.70/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 2.70/0.99      inference(forward_subsumption_resolution,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_3577,c_3573]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_3591,plain,
% 2.70/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.70/0.99      inference(light_normalisation,[status(thm)],[c_3560,c_3569,c_3580]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(contradiction,plain,
% 2.70/0.99      ( $false ),
% 2.70/0.99      inference(minisat,[status(thm)],[c_3635,c_3591]) ).
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  ------                               Statistics
% 2.70/0.99  
% 2.70/0.99  ------ General
% 2.70/0.99  
% 2.70/0.99  abstr_ref_over_cycles:                  0
% 2.70/0.99  abstr_ref_under_cycles:                 0
% 2.70/0.99  gc_basic_clause_elim:                   0
% 2.70/0.99  forced_gc_time:                         0
% 2.70/0.99  parsing_time:                           0.011
% 2.70/0.99  unif_index_cands_time:                  0.
% 2.70/0.99  unif_index_add_time:                    0.
% 2.70/0.99  orderings_time:                         0.
% 2.70/0.99  out_proof_time:                         0.009
% 2.70/0.99  total_time:                             0.143
% 2.70/0.99  num_of_symbols:                         48
% 2.70/0.99  num_of_terms:                           2175
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing
% 2.70/0.99  
% 2.70/0.99  num_of_splits:                          3
% 2.70/0.99  num_of_split_atoms:                     2
% 2.70/0.99  num_of_reused_defs:                     1
% 2.70/0.99  num_eq_ax_congr_red:                    7
% 2.70/0.99  num_of_sem_filtered_clauses:            2
% 2.70/0.99  num_of_subtypes:                        0
% 2.70/0.99  monotx_restored_types:                  0
% 2.70/0.99  sat_num_of_epr_types:                   0
% 2.70/0.99  sat_num_of_non_cyclic_types:            0
% 2.70/0.99  sat_guarded_non_collapsed_types:        0
% 2.70/0.99  num_pure_diseq_elim:                    0
% 2.70/0.99  simp_replaced_by:                       0
% 2.70/0.99  res_preprocessed:                       105
% 2.70/0.99  prep_upred:                             0
% 2.70/0.99  prep_unflattend:                        46
% 2.70/0.99  smt_new_axioms:                         0
% 2.70/0.99  pred_elim_cands:                        2
% 2.70/0.99  pred_elim:                              4
% 2.70/0.99  pred_elim_cl:                           3
% 2.70/0.99  pred_elim_cycles:                       6
% 2.70/0.99  merged_defs:                            8
% 2.70/0.99  merged_defs_ncl:                        0
% 2.70/0.99  bin_hyper_res:                          8
% 2.70/0.99  prep_cycles:                            4
% 2.70/0.99  pred_elim_time:                         0.006
% 2.70/0.99  splitting_time:                         0.
% 2.70/0.99  sem_filter_time:                        0.
% 2.70/0.99  monotx_time:                            0.001
% 2.70/0.99  subtype_inf_time:                       0.
% 2.70/0.99  
% 2.70/0.99  ------ Problem properties
% 2.70/0.99  
% 2.70/0.99  clauses:                                24
% 2.70/0.99  conjectures:                            3
% 2.70/0.99  epr:                                    7
% 2.70/0.99  horn:                                   21
% 2.70/0.99  ground:                                 12
% 2.70/0.99  unary:                                  4
% 2.70/0.99  binary:                                 11
% 2.70/0.99  lits:                                   58
% 2.70/0.99  lits_eq:                                21
% 2.70/0.99  fd_pure:                                0
% 2.70/0.99  fd_pseudo:                              0
% 2.70/0.99  fd_cond:                                0
% 2.70/0.99  fd_pseudo_cond:                         1
% 2.70/0.99  ac_symbols:                             0
% 2.70/0.99  
% 2.70/0.99  ------ Propositional Solver
% 2.70/0.99  
% 2.70/0.99  prop_solver_calls:                      27
% 2.70/0.99  prop_fast_solver_calls:                 666
% 2.70/0.99  smt_solver_calls:                       0
% 2.70/0.99  smt_fast_solver_calls:                  0
% 2.70/0.99  prop_num_of_clauses:                    1162
% 2.70/0.99  prop_preprocess_simplified:             4128
% 2.70/0.99  prop_fo_subsumed:                       8
% 2.70/0.99  prop_solver_time:                       0.
% 2.70/0.99  smt_solver_time:                        0.
% 2.70/0.99  smt_fast_solver_time:                   0.
% 2.70/0.99  prop_fast_solver_time:                  0.
% 2.70/0.99  prop_unsat_core_time:                   0.
% 2.70/0.99  
% 2.70/0.99  ------ QBF
% 2.70/0.99  
% 2.70/0.99  qbf_q_res:                              0
% 2.70/0.99  qbf_num_tautologies:                    0
% 2.70/0.99  qbf_prep_cycles:                        0
% 2.70/0.99  
% 2.70/0.99  ------ BMC1
% 2.70/0.99  
% 2.70/0.99  bmc1_current_bound:                     -1
% 2.70/0.99  bmc1_last_solved_bound:                 -1
% 2.70/0.99  bmc1_unsat_core_size:                   -1
% 2.70/0.99  bmc1_unsat_core_parents_size:           -1
% 2.70/0.99  bmc1_merge_next_fun:                    0
% 2.70/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation
% 2.70/0.99  
% 2.70/0.99  inst_num_of_clauses:                    356
% 2.70/0.99  inst_num_in_passive:                    102
% 2.70/0.99  inst_num_in_active:                     174
% 2.70/0.99  inst_num_in_unprocessed:                80
% 2.70/0.99  inst_num_of_loops:                      220
% 2.70/0.99  inst_num_of_learning_restarts:          0
% 2.70/0.99  inst_num_moves_active_passive:          43
% 2.70/0.99  inst_lit_activity:                      0
% 2.70/0.99  inst_lit_activity_moves:                0
% 2.70/0.99  inst_num_tautologies:                   0
% 2.70/0.99  inst_num_prop_implied:                  0
% 2.70/0.99  inst_num_existing_simplified:           0
% 2.70/0.99  inst_num_eq_res_simplified:             0
% 2.70/0.99  inst_num_child_elim:                    0
% 2.70/0.99  inst_num_of_dismatching_blockings:      48
% 2.70/0.99  inst_num_of_non_proper_insts:           403
% 2.70/0.99  inst_num_of_duplicates:                 0
% 2.70/0.99  inst_inst_num_from_inst_to_res:         0
% 2.70/0.99  inst_dismatching_checking_time:         0.
% 2.70/0.99  
% 2.70/0.99  ------ Resolution
% 2.70/0.99  
% 2.70/0.99  res_num_of_clauses:                     0
% 2.70/0.99  res_num_in_passive:                     0
% 2.70/0.99  res_num_in_active:                      0
% 2.70/0.99  res_num_of_loops:                       109
% 2.70/0.99  res_forward_subset_subsumed:            23
% 2.70/0.99  res_backward_subset_subsumed:           0
% 2.70/0.99  res_forward_subsumed:                   0
% 2.70/0.99  res_backward_subsumed:                  1
% 2.70/0.99  res_forward_subsumption_resolution:     0
% 2.70/0.99  res_backward_subsumption_resolution:    0
% 2.70/0.99  res_clause_to_clause_subsumption:       211
% 2.70/0.99  res_orphan_elimination:                 0
% 2.70/0.99  res_tautology_del:                      73
% 2.70/0.99  res_num_eq_res_simplified:              1
% 2.70/0.99  res_num_sel_changes:                    0
% 2.70/0.99  res_moves_from_active_to_pass:          0
% 2.70/0.99  
% 2.70/0.99  ------ Superposition
% 2.70/0.99  
% 2.70/0.99  sup_time_total:                         0.
% 2.70/0.99  sup_time_generating:                    0.
% 2.70/0.99  sup_time_sim_full:                      0.
% 2.70/0.99  sup_time_sim_immed:                     0.
% 2.70/0.99  
% 2.70/0.99  sup_num_of_clauses:                     44
% 2.70/0.99  sup_num_in_active:                      19
% 2.70/0.99  sup_num_in_passive:                     25
% 2.70/0.99  sup_num_of_loops:                       43
% 2.70/0.99  sup_fw_superposition:                   33
% 2.70/0.99  sup_bw_superposition:                   9
% 2.70/0.99  sup_immediate_simplified:               14
% 2.70/0.99  sup_given_eliminated:                   0
% 2.70/0.99  comparisons_done:                       0
% 2.70/0.99  comparisons_avoided:                    3
% 2.70/0.99  
% 2.70/0.99  ------ Simplifications
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  sim_fw_subset_subsumed:                 5
% 2.70/0.99  sim_bw_subset_subsumed:                 0
% 2.70/0.99  sim_fw_subsumed:                        2
% 2.70/0.99  sim_bw_subsumed:                        0
% 2.70/0.99  sim_fw_subsumption_res:                 2
% 2.70/0.99  sim_bw_subsumption_res:                 0
% 2.70/0.99  sim_tautology_del:                      2
% 2.70/0.99  sim_eq_tautology_del:                   4
% 2.70/0.99  sim_eq_res_simp:                        4
% 2.70/0.99  sim_fw_demodulated:                     0
% 2.70/0.99  sim_bw_demodulated:                     24
% 2.70/0.99  sim_light_normalised:                   10
% 2.70/0.99  sim_joinable_taut:                      0
% 2.70/0.99  sim_joinable_simp:                      0
% 2.70/0.99  sim_ac_normalised:                      0
% 2.70/0.99  sim_smt_subsumption:                    0
% 2.70/0.99  
%------------------------------------------------------------------------------
