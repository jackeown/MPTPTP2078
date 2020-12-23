%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1033+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:43 EST 2020

% Result     : Theorem 1.16s
% Output     : CNFRefutation 1.16s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_928)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK3)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_partfun1(X2,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK3,X0,X1)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19,f18])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f11])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_294,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_484,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_195,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_196,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_195])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_198,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_196,c_11,c_9])).

cnf(c_290,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subtyping,[status(esa)],[c_198])).

cnf(c_488,plain,
    ( v1_partfun1(sK3,sK0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_4,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8,negated_conjecture,
    ( r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_162,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | X0 = X2
    | sK3 != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_163,plain,
    ( ~ v1_partfun1(sK3,X0)
    | ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_162])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_167,plain,
    ( ~ v1_partfun1(sK3,X0)
    | ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_163,c_14,c_11])).

cnf(c_291,plain,
    ( ~ v1_partfun1(sK3,X0_42)
    | ~ v1_partfun1(sK2,X0_42)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42)))
    | sK3 = sK2 ),
    inference(subtyping,[status(esa)],[c_167])).

cnf(c_487,plain,
    ( sK3 = sK2
    | v1_partfun1(sK3,X0_42) != iProver_top
    | v1_partfun1(sK2,X0_42) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_629,plain,
    ( sK3 = sK2
    | v1_partfun1(sK3,sK0) != iProver_top
    | v1_partfun1(sK2,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_484,c_487])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_632,plain,
    ( v1_partfun1(sK2,sK0) != iProver_top
    | v1_partfun1(sK3,sK0) != iProver_top
    | sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_17])).

cnf(c_633,plain,
    ( sK3 = sK2
    | v1_partfun1(sK3,sK0) != iProver_top
    | v1_partfun1(sK2,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_632])).

cnf(c_688,plain,
    ( sK3 = sK2
    | v1_partfun1(sK2,sK0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_488,c_633])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_209,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_210,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_212,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_210,c_14,c_12])).

cnf(c_214,plain,
    ( v1_partfun1(sK2,sK0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_848,plain,
    ( sK3 = sK2
    | v1_xboole_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_688,c_214])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_296,plain,
    ( ~ v1_xboole_0(X0_42)
    | k1_xboole_0 = X0_42 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_483,plain,
    ( k1_xboole_0 = X0_42
    | v1_xboole_0(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_854,plain,
    ( sK3 = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_848,c_483])).

cnf(c_3,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_6,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_141,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK3 != X0
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_142,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK2 != sK3 ),
    inference(unflattening,[status(thm)],[c_141])).

cnf(c_146,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK2 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_142,c_9])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK2 != sK3 ),
    inference(subtyping,[status(esa)],[c_146])).

cnf(c_486,plain,
    ( sK2 != sK3
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_860,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_486])).

cnf(c_925,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_484,c_860])).

cnf(c_933,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_925,c_484])).

cnf(c_7,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_295,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_934,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_925,c_295])).

cnf(c_935,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_934])).

cnf(c_938,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_933,c_935])).

cnf(c_931,plain,
    ( sK3 != sK2
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_925,c_486])).

cnf(c_944,plain,
    ( sK3 != sK2
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_931,c_935])).

cnf(c_1032,plain,
    ( sK3 = sK2
    | v1_partfun1(sK3,k1_xboole_0) != iProver_top
    | v1_partfun1(sK2,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_935,c_633])).

cnf(c_930,plain,
    ( v1_partfun1(sK3,sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_925,c_488])).

cnf(c_949,plain,
    ( v1_partfun1(sK3,k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_930,c_935])).

cnf(c_299,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_601,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_609,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_302,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_556,plain,
    ( sK3 != X0_42
    | sK2 != X0_42
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_838,plain,
    ( sK3 != k1_xboole_0
    | sK2 = sK3
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_973,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_296])).

cnf(c_976,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_617,plain,
    ( X0_42 != X1_42
    | sK3 != X1_42
    | sK3 = X0_42 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_699,plain,
    ( X0_42 != sK3
    | sK3 = X0_42
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_974,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_982,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_296])).

cnf(c_987,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_982])).

cnf(c_670,plain,
    ( X0_42 != X1_42
    | sK2 != X1_42
    | sK2 = X0_42 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_734,plain,
    ( X0_42 != sK2
    | sK2 = X0_42
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_983,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_293,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_485,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_297,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
    | ~ v1_xboole_0(X1_42)
    | v1_xboole_0(X0_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_482,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) != iProver_top
    | v1_xboole_0(X1_42) != iProver_top
    | v1_xboole_0(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_741,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_485,c_482])).

cnf(c_1030,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_935,c_741])).

cnf(c_740,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_484,c_482])).

cnf(c_1031,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_935,c_740])).

cnf(c_1218,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_1253,plain,
    ( v1_partfun1(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_949,c_9,c_601,c_609,c_838,c_976,c_974,c_987,c_983,c_1030,c_1031,c_1218])).

cnf(c_289,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subtyping,[status(esa)],[c_212])).

cnf(c_489,plain,
    ( v1_partfun1(sK2,sK0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_929,plain,
    ( v1_partfun1(sK2,sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_925,c_489])).

cnf(c_954,plain,
    ( v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_929,c_935])).

cnf(c_1260,plain,
    ( v1_partfun1(sK2,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_954,c_9,c_601,c_609,c_838,c_976,c_974,c_987,c_983,c_1030,c_1031,c_1218])).

cnf(c_1308,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_944,c_9,c_601,c_609,c_838,c_928,c_976,c_974,c_987,c_983,c_1030,c_1031,c_1218])).

cnf(c_1315,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_938,c_1308])).


%------------------------------------------------------------------------------
