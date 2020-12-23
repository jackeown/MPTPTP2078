%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:32 EST 2020

% Result     : Theorem 1.04s
% Output     : CNFRefutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :  104 (1534 expanded)
%              Number of clauses        :   70 ( 454 expanded)
%              Number of leaves         :    9 ( 390 expanded)
%              Depth                    :   24
%              Number of atoms          :  357 (11787 expanded)
%              Number of equality atoms :  125 (2640 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_294,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_484,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

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

cnf(c_5,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_8,negated_conjecture,
    ( r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_162,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | X0 = X2
    | sK3 != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_8])).

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

cnf(c_694,plain,
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
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

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

cnf(c_866,plain,
    ( sK3 = sK2
    | v1_xboole_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_694,c_214])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_297,plain,
    ( ~ v1_xboole_0(X0_42)
    | k1_xboole_0 = X0_42 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_482,plain,
    ( k1_xboole_0 = X0_42
    | v1_xboole_0(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_874,plain,
    ( sK3 = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_866,c_482])).

cnf(c_2,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_6,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_141,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK3 != X3
    | sK2 != X3
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

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

cnf(c_960,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_486])).

cnf(c_1038,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_484,c_960])).

cnf(c_293,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_485,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_1047,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1038,c_485])).

cnf(c_7,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_295,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1049,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1038,c_295])).

cnf(c_1050,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1049])).

cnf(c_1056,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1047,c_1050])).

cnf(c_1046,plain,
    ( sK3 != sK2
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1038,c_486])).

cnf(c_1059,plain,
    ( sK3 != sK2
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1046,c_1050])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
    | ~ v1_xboole_0(X2_42)
    | v1_xboole_0(X0_42) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_483,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) != iProver_top
    | v1_xboole_0(X2_42) != iProver_top
    | v1_xboole_0(X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_768,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_485,c_483])).

cnf(c_872,plain,
    ( sK3 = sK2
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_866,c_768])).

cnf(c_892,plain,
    ( sK3 = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_872,c_482])).

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

cnf(c_903,plain,
    ( sK3 != k1_xboole_0
    | sK2 = sK3
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_767,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_484,c_483])).

cnf(c_873,plain,
    ( sK3 = sK2
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_866,c_767])).

cnf(c_953,plain,
    ( sK3 = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_873,c_482])).

cnf(c_1216,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_1243,plain,
    ( sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_892,c_9,c_903,c_953,c_1216])).

cnf(c_1303,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1059,c_9,c_892,c_903,c_953,c_1216])).

cnf(c_1310,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1056,c_1303])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:47:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.04/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.04/0.99  
% 1.04/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.04/0.99  
% 1.04/0.99  ------  iProver source info
% 1.04/0.99  
% 1.04/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.04/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.04/0.99  git: non_committed_changes: false
% 1.04/0.99  git: last_make_outside_of_git: false
% 1.04/0.99  
% 1.04/0.99  ------ 
% 1.04/0.99  
% 1.04/0.99  ------ Input Options
% 1.04/0.99  
% 1.04/0.99  --out_options                           all
% 1.04/0.99  --tptp_safe_out                         true
% 1.04/0.99  --problem_path                          ""
% 1.04/0.99  --include_path                          ""
% 1.04/0.99  --clausifier                            res/vclausify_rel
% 1.04/0.99  --clausifier_options                    --mode clausify
% 1.04/0.99  --stdin                                 false
% 1.04/0.99  --stats_out                             all
% 1.04/0.99  
% 1.04/0.99  ------ General Options
% 1.04/0.99  
% 1.04/0.99  --fof                                   false
% 1.04/0.99  --time_out_real                         305.
% 1.04/0.99  --time_out_virtual                      -1.
% 1.04/0.99  --symbol_type_check                     false
% 1.04/0.99  --clausify_out                          false
% 1.04/0.99  --sig_cnt_out                           false
% 1.04/0.99  --trig_cnt_out                          false
% 1.04/0.99  --trig_cnt_out_tolerance                1.
% 1.04/0.99  --trig_cnt_out_sk_spl                   false
% 1.04/0.99  --abstr_cl_out                          false
% 1.04/0.99  
% 1.04/0.99  ------ Global Options
% 1.04/0.99  
% 1.04/0.99  --schedule                              default
% 1.04/0.99  --add_important_lit                     false
% 1.04/0.99  --prop_solver_per_cl                    1000
% 1.04/0.99  --min_unsat_core                        false
% 1.04/0.99  --soft_assumptions                      false
% 1.04/0.99  --soft_lemma_size                       3
% 1.04/0.99  --prop_impl_unit_size                   0
% 1.04/0.99  --prop_impl_unit                        []
% 1.04/0.99  --share_sel_clauses                     true
% 1.04/0.99  --reset_solvers                         false
% 1.04/0.99  --bc_imp_inh                            [conj_cone]
% 1.04/0.99  --conj_cone_tolerance                   3.
% 1.04/0.99  --extra_neg_conj                        none
% 1.04/0.99  --large_theory_mode                     true
% 1.04/0.99  --prolific_symb_bound                   200
% 1.04/0.99  --lt_threshold                          2000
% 1.04/0.99  --clause_weak_htbl                      true
% 1.04/0.99  --gc_record_bc_elim                     false
% 1.04/0.99  
% 1.04/0.99  ------ Preprocessing Options
% 1.04/0.99  
% 1.04/0.99  --preprocessing_flag                    true
% 1.04/0.99  --time_out_prep_mult                    0.1
% 1.04/0.99  --splitting_mode                        input
% 1.04/0.99  --splitting_grd                         true
% 1.04/0.99  --splitting_cvd                         false
% 1.04/0.99  --splitting_cvd_svl                     false
% 1.04/0.99  --splitting_nvd                         32
% 1.04/0.99  --sub_typing                            true
% 1.04/0.99  --prep_gs_sim                           true
% 1.04/0.99  --prep_unflatten                        true
% 1.04/0.99  --prep_res_sim                          true
% 1.04/0.99  --prep_upred                            true
% 1.04/0.99  --prep_sem_filter                       exhaustive
% 1.04/0.99  --prep_sem_filter_out                   false
% 1.04/0.99  --pred_elim                             true
% 1.04/0.99  --res_sim_input                         true
% 1.04/0.99  --eq_ax_congr_red                       true
% 1.04/0.99  --pure_diseq_elim                       true
% 1.04/0.99  --brand_transform                       false
% 1.04/0.99  --non_eq_to_eq                          false
% 1.04/0.99  --prep_def_merge                        true
% 1.04/0.99  --prep_def_merge_prop_impl              false
% 1.04/0.99  --prep_def_merge_mbd                    true
% 1.04/0.99  --prep_def_merge_tr_red                 false
% 1.04/0.99  --prep_def_merge_tr_cl                  false
% 1.04/0.99  --smt_preprocessing                     true
% 1.04/0.99  --smt_ac_axioms                         fast
% 1.04/0.99  --preprocessed_out                      false
% 1.04/0.99  --preprocessed_stats                    false
% 1.04/0.99  
% 1.04/0.99  ------ Abstraction refinement Options
% 1.04/0.99  
% 1.04/0.99  --abstr_ref                             []
% 1.04/0.99  --abstr_ref_prep                        false
% 1.04/0.99  --abstr_ref_until_sat                   false
% 1.04/0.99  --abstr_ref_sig_restrict                funpre
% 1.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.04/0.99  --abstr_ref_under                       []
% 1.04/0.99  
% 1.04/0.99  ------ SAT Options
% 1.04/0.99  
% 1.04/0.99  --sat_mode                              false
% 1.04/0.99  --sat_fm_restart_options                ""
% 1.04/0.99  --sat_gr_def                            false
% 1.04/0.99  --sat_epr_types                         true
% 1.04/0.99  --sat_non_cyclic_types                  false
% 1.04/0.99  --sat_finite_models                     false
% 1.04/0.99  --sat_fm_lemmas                         false
% 1.04/0.99  --sat_fm_prep                           false
% 1.04/0.99  --sat_fm_uc_incr                        true
% 1.04/0.99  --sat_out_model                         small
% 1.04/0.99  --sat_out_clauses                       false
% 1.04/0.99  
% 1.04/0.99  ------ QBF Options
% 1.04/0.99  
% 1.04/0.99  --qbf_mode                              false
% 1.04/0.99  --qbf_elim_univ                         false
% 1.04/0.99  --qbf_dom_inst                          none
% 1.04/0.99  --qbf_dom_pre_inst                      false
% 1.04/0.99  --qbf_sk_in                             false
% 1.04/0.99  --qbf_pred_elim                         true
% 1.04/0.99  --qbf_split                             512
% 1.04/0.99  
% 1.04/0.99  ------ BMC1 Options
% 1.04/0.99  
% 1.04/0.99  --bmc1_incremental                      false
% 1.04/0.99  --bmc1_axioms                           reachable_all
% 1.04/0.99  --bmc1_min_bound                        0
% 1.04/0.99  --bmc1_max_bound                        -1
% 1.04/0.99  --bmc1_max_bound_default                -1
% 1.04/0.99  --bmc1_symbol_reachability              true
% 1.04/0.99  --bmc1_property_lemmas                  false
% 1.04/0.99  --bmc1_k_induction                      false
% 1.04/0.99  --bmc1_non_equiv_states                 false
% 1.04/0.99  --bmc1_deadlock                         false
% 1.04/0.99  --bmc1_ucm                              false
% 1.04/0.99  --bmc1_add_unsat_core                   none
% 1.04/0.99  --bmc1_unsat_core_children              false
% 1.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.04/0.99  --bmc1_out_stat                         full
% 1.04/0.99  --bmc1_ground_init                      false
% 1.04/0.99  --bmc1_pre_inst_next_state              false
% 1.04/0.99  --bmc1_pre_inst_state                   false
% 1.04/0.99  --bmc1_pre_inst_reach_state             false
% 1.04/0.99  --bmc1_out_unsat_core                   false
% 1.04/0.99  --bmc1_aig_witness_out                  false
% 1.04/0.99  --bmc1_verbose                          false
% 1.04/0.99  --bmc1_dump_clauses_tptp                false
% 1.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.04/0.99  --bmc1_dump_file                        -
% 1.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.04/0.99  --bmc1_ucm_extend_mode                  1
% 1.04/0.99  --bmc1_ucm_init_mode                    2
% 1.04/0.99  --bmc1_ucm_cone_mode                    none
% 1.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.04/0.99  --bmc1_ucm_relax_model                  4
% 1.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.04/0.99  --bmc1_ucm_layered_model                none
% 1.04/0.99  --bmc1_ucm_max_lemma_size               10
% 1.04/0.99  
% 1.04/0.99  ------ AIG Options
% 1.04/0.99  
% 1.04/0.99  --aig_mode                              false
% 1.04/0.99  
% 1.04/0.99  ------ Instantiation Options
% 1.04/0.99  
% 1.04/0.99  --instantiation_flag                    true
% 1.04/0.99  --inst_sos_flag                         false
% 1.04/0.99  --inst_sos_phase                        true
% 1.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.04/0.99  --inst_lit_sel_side                     num_symb
% 1.04/0.99  --inst_solver_per_active                1400
% 1.04/0.99  --inst_solver_calls_frac                1.
% 1.04/0.99  --inst_passive_queue_type               priority_queues
% 1.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.04/0.99  --inst_passive_queues_freq              [25;2]
% 1.04/0.99  --inst_dismatching                      true
% 1.04/0.99  --inst_eager_unprocessed_to_passive     true
% 1.04/0.99  --inst_prop_sim_given                   true
% 1.04/0.99  --inst_prop_sim_new                     false
% 1.04/0.99  --inst_subs_new                         false
% 1.04/0.99  --inst_eq_res_simp                      false
% 1.04/0.99  --inst_subs_given                       false
% 1.04/0.99  --inst_orphan_elimination               true
% 1.04/0.99  --inst_learning_loop_flag               true
% 1.04/0.99  --inst_learning_start                   3000
% 1.04/0.99  --inst_learning_factor                  2
% 1.04/0.99  --inst_start_prop_sim_after_learn       3
% 1.04/0.99  --inst_sel_renew                        solver
% 1.04/0.99  --inst_lit_activity_flag                true
% 1.04/0.99  --inst_restr_to_given                   false
% 1.04/0.99  --inst_activity_threshold               500
% 1.04/0.99  --inst_out_proof                        true
% 1.04/0.99  
% 1.04/0.99  ------ Resolution Options
% 1.04/0.99  
% 1.04/0.99  --resolution_flag                       true
% 1.04/0.99  --res_lit_sel                           adaptive
% 1.04/0.99  --res_lit_sel_side                      none
% 1.04/0.99  --res_ordering                          kbo
% 1.04/0.99  --res_to_prop_solver                    active
% 1.04/0.99  --res_prop_simpl_new                    false
% 1.04/0.99  --res_prop_simpl_given                  true
% 1.04/0.99  --res_passive_queue_type                priority_queues
% 1.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.04/0.99  --res_passive_queues_freq               [15;5]
% 1.04/0.99  --res_forward_subs                      full
% 1.04/0.99  --res_backward_subs                     full
% 1.04/0.99  --res_forward_subs_resolution           true
% 1.04/0.99  --res_backward_subs_resolution          true
% 1.04/0.99  --res_orphan_elimination                true
% 1.04/0.99  --res_time_limit                        2.
% 1.04/0.99  --res_out_proof                         true
% 1.04/0.99  
% 1.04/0.99  ------ Superposition Options
% 1.04/0.99  
% 1.04/0.99  --superposition_flag                    true
% 1.04/0.99  --sup_passive_queue_type                priority_queues
% 1.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.04/0.99  --demod_completeness_check              fast
% 1.04/0.99  --demod_use_ground                      true
% 1.04/0.99  --sup_to_prop_solver                    passive
% 1.04/0.99  --sup_prop_simpl_new                    true
% 1.04/0.99  --sup_prop_simpl_given                  true
% 1.04/0.99  --sup_fun_splitting                     false
% 1.04/0.99  --sup_smt_interval                      50000
% 1.04/0.99  
% 1.04/0.99  ------ Superposition Simplification Setup
% 1.04/0.99  
% 1.04/0.99  --sup_indices_passive                   []
% 1.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.04/0.99  --sup_full_bw                           [BwDemod]
% 1.04/0.99  --sup_immed_triv                        [TrivRules]
% 1.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.04/0.99  --sup_immed_bw_main                     []
% 1.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.04/0.99  
% 1.04/0.99  ------ Combination Options
% 1.04/0.99  
% 1.04/0.99  --comb_res_mult                         3
% 1.04/0.99  --comb_sup_mult                         2
% 1.04/0.99  --comb_inst_mult                        10
% 1.04/0.99  
% 1.04/0.99  ------ Debug Options
% 1.04/0.99  
% 1.04/0.99  --dbg_backtrace                         false
% 1.04/0.99  --dbg_dump_prop_clauses                 false
% 1.04/0.99  --dbg_dump_prop_clauses_file            -
% 1.04/0.99  --dbg_out_stat                          false
% 1.04/0.99  ------ Parsing...
% 1.04/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.04/0.99  
% 1.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.04/0.99  
% 1.04/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.04/0.99  
% 1.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.04/0.99  ------ Proving...
% 1.04/0.99  ------ Problem Properties 
% 1.04/0.99  
% 1.04/0.99  
% 1.04/0.99  clauses                                 9
% 1.04/0.99  conjectures                             3
% 1.04/0.99  EPR                                     4
% 1.04/0.99  Horn                                    7
% 1.04/0.99  unary                                   2
% 1.04/0.99  binary                                  5
% 1.04/0.99  lits                                    20
% 1.04/0.99  lits eq                                 5
% 1.04/0.99  fd_pure                                 0
% 1.04/0.99  fd_pseudo                               0
% 1.04/0.99  fd_cond                                 1
% 1.04/0.99  fd_pseudo_cond                          0
% 1.04/0.99  AC symbols                              0
% 1.04/0.99  
% 1.04/0.99  ------ Schedule dynamic 5 is on 
% 1.04/0.99  
% 1.04/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.04/0.99  
% 1.04/0.99  
% 1.04/0.99  ------ 
% 1.04/0.99  Current options:
% 1.04/0.99  ------ 
% 1.04/0.99  
% 1.04/0.99  ------ Input Options
% 1.04/0.99  
% 1.04/0.99  --out_options                           all
% 1.04/0.99  --tptp_safe_out                         true
% 1.04/0.99  --problem_path                          ""
% 1.04/0.99  --include_path                          ""
% 1.04/0.99  --clausifier                            res/vclausify_rel
% 1.04/0.99  --clausifier_options                    --mode clausify
% 1.04/0.99  --stdin                                 false
% 1.04/0.99  --stats_out                             all
% 1.04/0.99  
% 1.04/0.99  ------ General Options
% 1.04/0.99  
% 1.04/0.99  --fof                                   false
% 1.04/0.99  --time_out_real                         305.
% 1.04/0.99  --time_out_virtual                      -1.
% 1.04/0.99  --symbol_type_check                     false
% 1.04/0.99  --clausify_out                          false
% 1.04/0.99  --sig_cnt_out                           false
% 1.04/0.99  --trig_cnt_out                          false
% 1.04/0.99  --trig_cnt_out_tolerance                1.
% 1.04/0.99  --trig_cnt_out_sk_spl                   false
% 1.04/0.99  --abstr_cl_out                          false
% 1.04/0.99  
% 1.04/0.99  ------ Global Options
% 1.04/0.99  
% 1.04/0.99  --schedule                              default
% 1.04/0.99  --add_important_lit                     false
% 1.04/0.99  --prop_solver_per_cl                    1000
% 1.04/0.99  --min_unsat_core                        false
% 1.04/0.99  --soft_assumptions                      false
% 1.04/0.99  --soft_lemma_size                       3
% 1.04/0.99  --prop_impl_unit_size                   0
% 1.04/0.99  --prop_impl_unit                        []
% 1.04/0.99  --share_sel_clauses                     true
% 1.04/0.99  --reset_solvers                         false
% 1.04/0.99  --bc_imp_inh                            [conj_cone]
% 1.04/0.99  --conj_cone_tolerance                   3.
% 1.04/0.99  --extra_neg_conj                        none
% 1.04/0.99  --large_theory_mode                     true
% 1.04/0.99  --prolific_symb_bound                   200
% 1.04/0.99  --lt_threshold                          2000
% 1.04/0.99  --clause_weak_htbl                      true
% 1.04/0.99  --gc_record_bc_elim                     false
% 1.04/0.99  
% 1.04/0.99  ------ Preprocessing Options
% 1.04/0.99  
% 1.04/0.99  --preprocessing_flag                    true
% 1.04/0.99  --time_out_prep_mult                    0.1
% 1.04/0.99  --splitting_mode                        input
% 1.04/0.99  --splitting_grd                         true
% 1.04/0.99  --splitting_cvd                         false
% 1.04/0.99  --splitting_cvd_svl                     false
% 1.04/0.99  --splitting_nvd                         32
% 1.04/0.99  --sub_typing                            true
% 1.04/0.99  --prep_gs_sim                           true
% 1.04/0.99  --prep_unflatten                        true
% 1.04/0.99  --prep_res_sim                          true
% 1.04/0.99  --prep_upred                            true
% 1.04/0.99  --prep_sem_filter                       exhaustive
% 1.04/0.99  --prep_sem_filter_out                   false
% 1.04/0.99  --pred_elim                             true
% 1.04/0.99  --res_sim_input                         true
% 1.04/0.99  --eq_ax_congr_red                       true
% 1.04/0.99  --pure_diseq_elim                       true
% 1.04/0.99  --brand_transform                       false
% 1.04/0.99  --non_eq_to_eq                          false
% 1.04/0.99  --prep_def_merge                        true
% 1.04/0.99  --prep_def_merge_prop_impl              false
% 1.04/0.99  --prep_def_merge_mbd                    true
% 1.04/0.99  --prep_def_merge_tr_red                 false
% 1.04/0.99  --prep_def_merge_tr_cl                  false
% 1.04/0.99  --smt_preprocessing                     true
% 1.04/0.99  --smt_ac_axioms                         fast
% 1.04/0.99  --preprocessed_out                      false
% 1.04/0.99  --preprocessed_stats                    false
% 1.04/0.99  
% 1.04/0.99  ------ Abstraction refinement Options
% 1.04/0.99  
% 1.04/0.99  --abstr_ref                             []
% 1.04/0.99  --abstr_ref_prep                        false
% 1.04/0.99  --abstr_ref_until_sat                   false
% 1.04/0.99  --abstr_ref_sig_restrict                funpre
% 1.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.04/0.99  --abstr_ref_under                       []
% 1.04/0.99  
% 1.04/0.99  ------ SAT Options
% 1.04/0.99  
% 1.04/0.99  --sat_mode                              false
% 1.04/0.99  --sat_fm_restart_options                ""
% 1.04/0.99  --sat_gr_def                            false
% 1.04/0.99  --sat_epr_types                         true
% 1.04/0.99  --sat_non_cyclic_types                  false
% 1.04/0.99  --sat_finite_models                     false
% 1.04/0.99  --sat_fm_lemmas                         false
% 1.04/0.99  --sat_fm_prep                           false
% 1.04/0.99  --sat_fm_uc_incr                        true
% 1.04/0.99  --sat_out_model                         small
% 1.04/0.99  --sat_out_clauses                       false
% 1.04/0.99  
% 1.04/0.99  ------ QBF Options
% 1.04/0.99  
% 1.04/0.99  --qbf_mode                              false
% 1.04/0.99  --qbf_elim_univ                         false
% 1.04/0.99  --qbf_dom_inst                          none
% 1.04/0.99  --qbf_dom_pre_inst                      false
% 1.04/0.99  --qbf_sk_in                             false
% 1.04/0.99  --qbf_pred_elim                         true
% 1.04/0.99  --qbf_split                             512
% 1.04/0.99  
% 1.04/0.99  ------ BMC1 Options
% 1.04/0.99  
% 1.04/0.99  --bmc1_incremental                      false
% 1.04/0.99  --bmc1_axioms                           reachable_all
% 1.04/0.99  --bmc1_min_bound                        0
% 1.04/0.99  --bmc1_max_bound                        -1
% 1.04/0.99  --bmc1_max_bound_default                -1
% 1.04/0.99  --bmc1_symbol_reachability              true
% 1.04/0.99  --bmc1_property_lemmas                  false
% 1.04/0.99  --bmc1_k_induction                      false
% 1.04/0.99  --bmc1_non_equiv_states                 false
% 1.04/0.99  --bmc1_deadlock                         false
% 1.04/0.99  --bmc1_ucm                              false
% 1.04/0.99  --bmc1_add_unsat_core                   none
% 1.04/0.99  --bmc1_unsat_core_children              false
% 1.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.04/0.99  --bmc1_out_stat                         full
% 1.04/0.99  --bmc1_ground_init                      false
% 1.04/0.99  --bmc1_pre_inst_next_state              false
% 1.04/0.99  --bmc1_pre_inst_state                   false
% 1.04/0.99  --bmc1_pre_inst_reach_state             false
% 1.04/0.99  --bmc1_out_unsat_core                   false
% 1.04/0.99  --bmc1_aig_witness_out                  false
% 1.04/0.99  --bmc1_verbose                          false
% 1.04/0.99  --bmc1_dump_clauses_tptp                false
% 1.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.04/0.99  --bmc1_dump_file                        -
% 1.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.04/0.99  --bmc1_ucm_extend_mode                  1
% 1.04/0.99  --bmc1_ucm_init_mode                    2
% 1.04/0.99  --bmc1_ucm_cone_mode                    none
% 1.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.04/0.99  --bmc1_ucm_relax_model                  4
% 1.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.04/0.99  --bmc1_ucm_layered_model                none
% 1.04/0.99  --bmc1_ucm_max_lemma_size               10
% 1.04/0.99  
% 1.04/0.99  ------ AIG Options
% 1.04/0.99  
% 1.04/0.99  --aig_mode                              false
% 1.04/0.99  
% 1.04/0.99  ------ Instantiation Options
% 1.04/0.99  
% 1.04/0.99  --instantiation_flag                    true
% 1.04/0.99  --inst_sos_flag                         false
% 1.04/0.99  --inst_sos_phase                        true
% 1.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.04/0.99  --inst_lit_sel_side                     none
% 1.04/0.99  --inst_solver_per_active                1400
% 1.04/0.99  --inst_solver_calls_frac                1.
% 1.04/0.99  --inst_passive_queue_type               priority_queues
% 1.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.04/0.99  --inst_passive_queues_freq              [25;2]
% 1.04/0.99  --inst_dismatching                      true
% 1.04/0.99  --inst_eager_unprocessed_to_passive     true
% 1.04/0.99  --inst_prop_sim_given                   true
% 1.04/0.99  --inst_prop_sim_new                     false
% 1.04/0.99  --inst_subs_new                         false
% 1.04/0.99  --inst_eq_res_simp                      false
% 1.04/0.99  --inst_subs_given                       false
% 1.04/0.99  --inst_orphan_elimination               true
% 1.04/0.99  --inst_learning_loop_flag               true
% 1.04/0.99  --inst_learning_start                   3000
% 1.04/0.99  --inst_learning_factor                  2
% 1.04/0.99  --inst_start_prop_sim_after_learn       3
% 1.04/0.99  --inst_sel_renew                        solver
% 1.04/0.99  --inst_lit_activity_flag                true
% 1.04/0.99  --inst_restr_to_given                   false
% 1.04/0.99  --inst_activity_threshold               500
% 1.04/0.99  --inst_out_proof                        true
% 1.04/0.99  
% 1.04/0.99  ------ Resolution Options
% 1.04/0.99  
% 1.04/0.99  --resolution_flag                       false
% 1.04/0.99  --res_lit_sel                           adaptive
% 1.04/0.99  --res_lit_sel_side                      none
% 1.04/0.99  --res_ordering                          kbo
% 1.04/0.99  --res_to_prop_solver                    active
% 1.04/0.99  --res_prop_simpl_new                    false
% 1.04/0.99  --res_prop_simpl_given                  true
% 1.04/0.99  --res_passive_queue_type                priority_queues
% 1.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.04/0.99  --res_passive_queues_freq               [15;5]
% 1.04/0.99  --res_forward_subs                      full
% 1.04/0.99  --res_backward_subs                     full
% 1.04/0.99  --res_forward_subs_resolution           true
% 1.04/0.99  --res_backward_subs_resolution          true
% 1.04/0.99  --res_orphan_elimination                true
% 1.04/0.99  --res_time_limit                        2.
% 1.04/0.99  --res_out_proof                         true
% 1.04/0.99  
% 1.04/0.99  ------ Superposition Options
% 1.04/0.99  
% 1.04/0.99  --superposition_flag                    true
% 1.04/0.99  --sup_passive_queue_type                priority_queues
% 1.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.04/0.99  --demod_completeness_check              fast
% 1.04/0.99  --demod_use_ground                      true
% 1.04/0.99  --sup_to_prop_solver                    passive
% 1.04/0.99  --sup_prop_simpl_new                    true
% 1.04/0.99  --sup_prop_simpl_given                  true
% 1.04/0.99  --sup_fun_splitting                     false
% 1.04/0.99  --sup_smt_interval                      50000
% 1.04/0.99  
% 1.04/0.99  ------ Superposition Simplification Setup
% 1.04/0.99  
% 1.04/0.99  --sup_indices_passive                   []
% 1.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.04/0.99  --sup_full_bw                           [BwDemod]
% 1.04/0.99  --sup_immed_triv                        [TrivRules]
% 1.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.04/0.99  --sup_immed_bw_main                     []
% 1.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.04/0.99  
% 1.04/0.99  ------ Combination Options
% 1.04/0.99  
% 1.04/0.99  --comb_res_mult                         3
% 1.04/0.99  --comb_sup_mult                         2
% 1.04/0.99  --comb_inst_mult                        10
% 1.04/0.99  
% 1.04/0.99  ------ Debug Options
% 1.04/0.99  
% 1.04/0.99  --dbg_backtrace                         false
% 1.04/0.99  --dbg_dump_prop_clauses                 false
% 1.04/0.99  --dbg_dump_prop_clauses_file            -
% 1.04/0.99  --dbg_out_stat                          false
% 1.04/0.99  
% 1.04/0.99  
% 1.04/0.99  
% 1.04/0.99  
% 1.04/0.99  ------ Proving...
% 1.04/0.99  
% 1.04/0.99  
% 1.04/0.99  % SZS status Theorem for theBenchmark.p
% 1.04/0.99  
% 1.04/0.99   Resolution empty clause
% 1.04/0.99  
% 1.04/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.04/0.99  
% 1.04/0.99  fof(f6,conjecture,(
% 1.04/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.04/0.99  
% 1.04/0.99  fof(f7,negated_conjecture,(
% 1.04/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.04/0.99    inference(negated_conjecture,[],[f6])).
% 1.04/0.99  
% 1.04/0.99  fof(f16,plain,(
% 1.04/0.99    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.04/0.99    inference(ennf_transformation,[],[f7])).
% 1.04/0.99  
% 1.04/0.99  fof(f17,plain,(
% 1.04/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.04/0.99    inference(flattening,[],[f16])).
% 1.04/0.99  
% 1.04/0.99  fof(f19,plain,(
% 1.04/0.99    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK3,X0,X1) & v1_funct_1(sK3))) )),
% 1.04/0.99    introduced(choice_axiom,[])).
% 1.04/0.99  
% 1.04/0.99  fof(f18,plain,(
% 1.04/0.99    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.04/0.99    introduced(choice_axiom,[])).
% 1.04/0.99  
% 1.04/0.99  fof(f20,plain,(
% 1.04/0.99    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19,f18])).
% 1.04/0.99  
% 1.04/0.99  fof(f32,plain,(
% 1.04/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.04/0.99    inference(cnf_transformation,[],[f20])).
% 1.04/0.99  
% 1.04/0.99  fof(f4,axiom,(
% 1.04/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.04/0.99  
% 1.04/0.99  fof(f12,plain,(
% 1.04/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.04/0.99    inference(ennf_transformation,[],[f4])).
% 1.04/0.99  
% 1.04/0.99  fof(f13,plain,(
% 1.04/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.04/0.99    inference(flattening,[],[f12])).
% 1.04/0.99  
% 1.04/0.99  fof(f25,plain,(
% 1.04/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.04/0.99    inference(cnf_transformation,[],[f13])).
% 1.04/0.99  
% 1.04/0.99  fof(f31,plain,(
% 1.04/0.99    v1_funct_2(sK3,sK0,sK1)),
% 1.04/0.99    inference(cnf_transformation,[],[f20])).
% 1.04/0.99  
% 1.04/0.99  fof(f30,plain,(
% 1.04/0.99    v1_funct_1(sK3)),
% 1.04/0.99    inference(cnf_transformation,[],[f20])).
% 1.04/0.99  
% 1.04/0.99  fof(f5,axiom,(
% 1.04/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.04/0.99  
% 1.04/0.99  fof(f14,plain,(
% 1.04/0.99    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.04/0.99    inference(ennf_transformation,[],[f5])).
% 1.04/0.99  
% 1.04/0.99  fof(f15,plain,(
% 1.04/0.99    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.04/0.99    inference(flattening,[],[f14])).
% 1.04/0.99  
% 1.04/0.99  fof(f26,plain,(
% 1.04/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.04/0.99    inference(cnf_transformation,[],[f15])).
% 1.04/0.99  
% 1.04/0.99  fof(f33,plain,(
% 1.04/0.99    r1_partfun1(sK2,sK3)),
% 1.04/0.99    inference(cnf_transformation,[],[f20])).
% 1.04/0.99  
% 1.04/0.99  fof(f27,plain,(
% 1.04/0.99    v1_funct_1(sK2)),
% 1.04/0.99    inference(cnf_transformation,[],[f20])).
% 1.04/0.99  
% 1.04/0.99  fof(f29,plain,(
% 1.04/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.04/0.99    inference(cnf_transformation,[],[f20])).
% 1.04/0.99  
% 1.04/0.99  fof(f28,plain,(
% 1.04/0.99    v1_funct_2(sK2,sK0,sK1)),
% 1.04/0.99    inference(cnf_transformation,[],[f20])).
% 1.04/0.99  
% 1.04/0.99  fof(f1,axiom,(
% 1.04/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.04/0.99  
% 1.04/0.99  fof(f8,plain,(
% 1.04/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.04/0.99    inference(ennf_transformation,[],[f1])).
% 1.04/0.99  
% 1.04/0.99  fof(f21,plain,(
% 1.04/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.04/0.99    inference(cnf_transformation,[],[f8])).
% 1.04/0.99  
% 1.04/0.99  fof(f3,axiom,(
% 1.04/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.04/0.99  
% 1.04/0.99  fof(f10,plain,(
% 1.04/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.04/0.99    inference(ennf_transformation,[],[f3])).
% 1.04/0.99  
% 1.04/0.99  fof(f11,plain,(
% 1.04/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.04/0.99    inference(flattening,[],[f10])).
% 1.04/0.99  
% 1.04/0.99  fof(f23,plain,(
% 1.04/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.04/0.99    inference(cnf_transformation,[],[f11])).
% 1.04/0.99  
% 1.04/0.99  fof(f35,plain,(
% 1.04/0.99    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.04/0.99    inference(cnf_transformation,[],[f20])).
% 1.04/0.99  
% 1.04/0.99  fof(f34,plain,(
% 1.04/0.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.04/0.99    inference(cnf_transformation,[],[f20])).
% 1.04/0.99  
% 1.04/0.99  fof(f2,axiom,(
% 1.04/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.04/0.99  
% 1.04/0.99  fof(f9,plain,(
% 1.04/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.04/0.99    inference(ennf_transformation,[],[f2])).
% 1.04/0.99  
% 1.04/0.99  fof(f22,plain,(
% 1.04/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 1.04/0.99    inference(cnf_transformation,[],[f9])).
% 1.04/0.99  
% 1.04/0.99  cnf(c_9,negated_conjecture,
% 1.04/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.04/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_294,negated_conjecture,
% 1.04/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.04/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_484,plain,
% 1.04/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.04/0.99      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_3,plain,
% 1.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.04/0.99      | v1_partfun1(X0,X1)
% 1.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.04/0.99      | ~ v1_funct_1(X0)
% 1.04/0.99      | v1_xboole_0(X2) ),
% 1.04/0.99      inference(cnf_transformation,[],[f25]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_10,negated_conjecture,
% 1.04/0.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 1.04/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_195,plain,
% 1.04/0.99      ( v1_partfun1(X0,X1)
% 1.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.04/0.99      | ~ v1_funct_1(X0)
% 1.04/0.99      | v1_xboole_0(X2)
% 1.04/0.99      | sK3 != X0
% 1.04/0.99      | sK1 != X2
% 1.04/0.99      | sK0 != X1 ),
% 1.04/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_10]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_196,plain,
% 1.04/0.99      ( v1_partfun1(sK3,sK0)
% 1.04/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.04/0.99      | ~ v1_funct_1(sK3)
% 1.04/0.99      | v1_xboole_0(sK1) ),
% 1.04/0.99      inference(unflattening,[status(thm)],[c_195]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_11,negated_conjecture,
% 1.04/0.99      ( v1_funct_1(sK3) ),
% 1.04/0.99      inference(cnf_transformation,[],[f30]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_198,plain,
% 1.04/0.99      ( v1_partfun1(sK3,sK0) | v1_xboole_0(sK1) ),
% 1.04/0.99      inference(global_propositional_subsumption,
% 1.04/0.99                [status(thm)],
% 1.04/0.99                [c_196,c_11,c_9]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_290,plain,
% 1.04/0.99      ( v1_partfun1(sK3,sK0) | v1_xboole_0(sK1) ),
% 1.04/0.99      inference(subtyping,[status(esa)],[c_198]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_488,plain,
% 1.04/0.99      ( v1_partfun1(sK3,sK0) = iProver_top | v1_xboole_0(sK1) = iProver_top ),
% 1.04/0.99      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_5,plain,
% 1.04/0.99      ( ~ r1_partfun1(X0,X1)
% 1.04/0.99      | ~ v1_partfun1(X1,X2)
% 1.04/0.99      | ~ v1_partfun1(X0,X2)
% 1.04/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.04/0.99      | ~ v1_funct_1(X0)
% 1.04/0.99      | ~ v1_funct_1(X1)
% 1.04/0.99      | X1 = X0 ),
% 1.04/0.99      inference(cnf_transformation,[],[f26]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_8,negated_conjecture,
% 1.04/0.99      ( r1_partfun1(sK2,sK3) ),
% 1.04/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_162,plain,
% 1.04/0.99      ( ~ v1_partfun1(X0,X1)
% 1.04/0.99      | ~ v1_partfun1(X2,X1)
% 1.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.04/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.04/0.99      | ~ v1_funct_1(X0)
% 1.04/0.99      | ~ v1_funct_1(X2)
% 1.04/0.99      | X0 = X2
% 1.04/0.99      | sK3 != X0
% 1.04/0.99      | sK2 != X2 ),
% 1.04/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_8]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_163,plain,
% 1.04/0.99      ( ~ v1_partfun1(sK3,X0)
% 1.04/0.99      | ~ v1_partfun1(sK2,X0)
% 1.04/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.04/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.04/0.99      | ~ v1_funct_1(sK3)
% 1.04/0.99      | ~ v1_funct_1(sK2)
% 1.04/0.99      | sK3 = sK2 ),
% 1.04/0.99      inference(unflattening,[status(thm)],[c_162]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_14,negated_conjecture,
% 1.04/0.99      ( v1_funct_1(sK2) ),
% 1.04/0.99      inference(cnf_transformation,[],[f27]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_167,plain,
% 1.04/0.99      ( ~ v1_partfun1(sK3,X0)
% 1.04/0.99      | ~ v1_partfun1(sK2,X0)
% 1.04/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.04/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.04/0.99      | sK3 = sK2 ),
% 1.04/0.99      inference(global_propositional_subsumption,
% 1.04/0.99                [status(thm)],
% 1.04/0.99                [c_163,c_14,c_11]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_291,plain,
% 1.04/0.99      ( ~ v1_partfun1(sK3,X0_42)
% 1.04/0.99      | ~ v1_partfun1(sK2,X0_42)
% 1.04/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42)))
% 1.04/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42)))
% 1.04/0.99      | sK3 = sK2 ),
% 1.04/0.99      inference(subtyping,[status(esa)],[c_167]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_487,plain,
% 1.04/0.99      ( sK3 = sK2
% 1.04/0.99      | v1_partfun1(sK3,X0_42) != iProver_top
% 1.04/0.99      | v1_partfun1(sK2,X0_42) != iProver_top
% 1.04/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top
% 1.04/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
% 1.04/0.99      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_629,plain,
% 1.04/0.99      ( sK3 = sK2
% 1.04/0.99      | v1_partfun1(sK3,sK0) != iProver_top
% 1.04/0.99      | v1_partfun1(sK2,sK0) != iProver_top
% 1.04/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 1.04/0.99      inference(superposition,[status(thm)],[c_484,c_487]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_12,negated_conjecture,
% 1.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.04/0.99      inference(cnf_transformation,[],[f29]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_17,plain,
% 1.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.04/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_632,plain,
% 1.04/0.99      ( v1_partfun1(sK2,sK0) != iProver_top
% 1.04/0.99      | v1_partfun1(sK3,sK0) != iProver_top
% 1.04/0.99      | sK3 = sK2 ),
% 1.04/0.99      inference(global_propositional_subsumption,[status(thm)],[c_629,c_17]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_633,plain,
% 1.04/0.99      ( sK3 = sK2
% 1.04/0.99      | v1_partfun1(sK3,sK0) != iProver_top
% 1.04/0.99      | v1_partfun1(sK2,sK0) != iProver_top ),
% 1.04/0.99      inference(renaming,[status(thm)],[c_632]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_694,plain,
% 1.04/0.99      ( sK3 = sK2
% 1.04/0.99      | v1_partfun1(sK2,sK0) != iProver_top
% 1.04/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 1.04/0.99      inference(superposition,[status(thm)],[c_488,c_633]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_13,negated_conjecture,
% 1.04/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 1.04/0.99      inference(cnf_transformation,[],[f28]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_209,plain,
% 1.04/0.99      ( v1_partfun1(X0,X1)
% 1.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.04/0.99      | ~ v1_funct_1(X0)
% 1.04/0.99      | v1_xboole_0(X2)
% 1.04/0.99      | sK2 != X0
% 1.04/0.99      | sK1 != X2
% 1.04/0.99      | sK0 != X1 ),
% 1.04/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_210,plain,
% 1.04/0.99      ( v1_partfun1(sK2,sK0)
% 1.04/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.04/0.99      | ~ v1_funct_1(sK2)
% 1.04/0.99      | v1_xboole_0(sK1) ),
% 1.04/0.99      inference(unflattening,[status(thm)],[c_209]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_212,plain,
% 1.04/0.99      ( v1_partfun1(sK2,sK0) | v1_xboole_0(sK1) ),
% 1.04/0.99      inference(global_propositional_subsumption,
% 1.04/0.99                [status(thm)],
% 1.04/0.99                [c_210,c_14,c_12]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_214,plain,
% 1.04/0.99      ( v1_partfun1(sK2,sK0) = iProver_top | v1_xboole_0(sK1) = iProver_top ),
% 1.04/0.99      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_866,plain,
% 1.04/0.99      ( sK3 = sK2 | v1_xboole_0(sK1) = iProver_top ),
% 1.04/0.99      inference(global_propositional_subsumption,[status(thm)],[c_694,c_214]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_0,plain,
% 1.04/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.04/0.99      inference(cnf_transformation,[],[f21]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_297,plain,
% 1.04/0.99      ( ~ v1_xboole_0(X0_42) | k1_xboole_0 = X0_42 ),
% 1.04/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_482,plain,
% 1.04/0.99      ( k1_xboole_0 = X0_42 | v1_xboole_0(X0_42) != iProver_top ),
% 1.04/0.99      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_874,plain,
% 1.04/0.99      ( sK3 = sK2 | sK1 = k1_xboole_0 ),
% 1.04/0.99      inference(superposition,[status(thm)],[c_866,c_482]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_2,plain,
% 1.04/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 1.04/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.04/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.04/0.99      inference(cnf_transformation,[],[f23]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_6,negated_conjecture,
% 1.04/0.99      ( ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
% 1.04/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_141,plain,
% 1.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.04/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.04/0.99      | sK3 != X3
% 1.04/0.99      | sK2 != X3
% 1.04/0.99      | sK1 != X2
% 1.04/0.99      | sK0 != X1 ),
% 1.04/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_6]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_142,plain,
% 1.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.04/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.04/0.99      | sK2 != sK3 ),
% 1.04/0.99      inference(unflattening,[status(thm)],[c_141]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_146,plain,
% 1.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK2 != sK3 ),
% 1.04/0.99      inference(global_propositional_subsumption,[status(thm)],[c_142,c_9]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_292,plain,
% 1.04/0.99      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK2 != sK3 ),
% 1.04/0.99      inference(subtyping,[status(esa)],[c_146]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_486,plain,
% 1.04/0.99      ( sK2 != sK3
% 1.04/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 1.04/0.99      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_960,plain,
% 1.04/0.99      ( sK1 = k1_xboole_0
% 1.04/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 1.04/0.99      inference(superposition,[status(thm)],[c_874,c_486]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_1038,plain,
% 1.04/0.99      ( sK1 = k1_xboole_0 ),
% 1.04/0.99      inference(superposition,[status(thm)],[c_484,c_960]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_293,negated_conjecture,
% 1.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.04/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_485,plain,
% 1.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.04/0.99      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_1047,plain,
% 1.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 1.04/0.99      inference(demodulation,[status(thm)],[c_1038,c_485]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_7,negated_conjecture,
% 1.04/0.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 1.04/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_295,negated_conjecture,
% 1.04/0.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 1.04/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_1049,plain,
% 1.04/0.99      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 1.04/0.99      inference(demodulation,[status(thm)],[c_1038,c_295]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_1050,plain,
% 1.04/0.99      ( sK0 = k1_xboole_0 ),
% 1.04/0.99      inference(equality_resolution_simp,[status(thm)],[c_1049]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_1056,plain,
% 1.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 1.04/0.99      inference(light_normalisation,[status(thm)],[c_1047,c_1050]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_1046,plain,
% 1.04/0.99      ( sK3 != sK2
% 1.04/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 1.04/0.99      inference(demodulation,[status(thm)],[c_1038,c_486]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_1059,plain,
% 1.04/0.99      ( sK3 != sK2
% 1.04/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 1.04/0.99      inference(light_normalisation,[status(thm)],[c_1046,c_1050]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_1,plain,
% 1.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.04/0.99      | ~ v1_xboole_0(X2)
% 1.04/0.99      | v1_xboole_0(X0) ),
% 1.04/0.99      inference(cnf_transformation,[],[f22]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_296,plain,
% 1.04/0.99      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42)))
% 1.04/0.99      | ~ v1_xboole_0(X2_42)
% 1.04/0.99      | v1_xboole_0(X0_42) ),
% 1.04/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_483,plain,
% 1.04/0.99      ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X1_42,X2_42))) != iProver_top
% 1.04/0.99      | v1_xboole_0(X2_42) != iProver_top
% 1.04/0.99      | v1_xboole_0(X0_42) = iProver_top ),
% 1.04/0.99      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_768,plain,
% 1.04/0.99      ( v1_xboole_0(sK2) = iProver_top | v1_xboole_0(sK1) != iProver_top ),
% 1.04/0.99      inference(superposition,[status(thm)],[c_485,c_483]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_872,plain,
% 1.04/0.99      ( sK3 = sK2 | v1_xboole_0(sK2) = iProver_top ),
% 1.04/0.99      inference(superposition,[status(thm)],[c_866,c_768]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_892,plain,
% 1.04/0.99      ( sK3 = sK2 | sK2 = k1_xboole_0 ),
% 1.04/0.99      inference(superposition,[status(thm)],[c_872,c_482]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_302,plain,
% 1.04/0.99      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 1.04/0.99      theory(equality) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_556,plain,
% 1.04/0.99      ( sK3 != X0_42 | sK2 != X0_42 | sK2 = sK3 ),
% 1.04/0.99      inference(instantiation,[status(thm)],[c_302]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_903,plain,
% 1.04/0.99      ( sK3 != k1_xboole_0 | sK2 = sK3 | sK2 != k1_xboole_0 ),
% 1.04/0.99      inference(instantiation,[status(thm)],[c_556]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_767,plain,
% 1.04/0.99      ( v1_xboole_0(sK3) = iProver_top | v1_xboole_0(sK1) != iProver_top ),
% 1.04/0.99      inference(superposition,[status(thm)],[c_484,c_483]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_873,plain,
% 1.04/0.99      ( sK3 = sK2 | v1_xboole_0(sK3) = iProver_top ),
% 1.04/0.99      inference(superposition,[status(thm)],[c_866,c_767]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_953,plain,
% 1.04/0.99      ( sK3 = sK2 | sK3 = k1_xboole_0 ),
% 1.04/0.99      inference(superposition,[status(thm)],[c_873,c_482]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_1216,plain,
% 1.04/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK2 != sK3 ),
% 1.04/0.99      inference(instantiation,[status(thm)],[c_292]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_1243,plain,
% 1.04/0.99      ( sK3 = sK2 ),
% 1.04/0.99      inference(global_propositional_subsumption,
% 1.04/0.99                [status(thm)],
% 1.04/0.99                [c_892,c_9,c_903,c_953,c_1216]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_1303,plain,
% 1.04/0.99      ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 1.04/0.99      inference(global_propositional_subsumption,
% 1.04/0.99                [status(thm)],
% 1.04/0.99                [c_1059,c_9,c_892,c_903,c_953,c_1216]) ).
% 1.04/0.99  
% 1.04/0.99  cnf(c_1310,plain,
% 1.04/0.99      ( $false ),
% 1.04/0.99      inference(superposition,[status(thm)],[c_1056,c_1303]) ).
% 1.04/0.99  
% 1.04/0.99  
% 1.04/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.04/0.99  
% 1.04/0.99  ------                               Statistics
% 1.04/0.99  
% 1.04/0.99  ------ General
% 1.04/0.99  
% 1.04/0.99  abstr_ref_over_cycles:                  0
% 1.04/0.99  abstr_ref_under_cycles:                 0
% 1.04/0.99  gc_basic_clause_elim:                   0
% 1.04/0.99  forced_gc_time:                         0
% 1.04/0.99  parsing_time:                           0.012
% 1.04/0.99  unif_index_cands_time:                  0.
% 1.04/0.99  unif_index_add_time:                    0.
% 1.04/0.99  orderings_time:                         0.
% 1.04/0.99  out_proof_time:                         0.01
% 1.04/0.99  total_time:                             0.086
% 1.04/0.99  num_of_symbols:                         45
% 1.04/0.99  num_of_terms:                           938
% 1.04/0.99  
% 1.04/0.99  ------ Preprocessing
% 1.04/0.99  
% 1.04/0.99  num_of_splits:                          0
% 1.04/0.99  num_of_split_atoms:                     0
% 1.04/0.99  num_of_reused_defs:                     0
% 1.04/0.99  num_eq_ax_congr_red:                    3
% 1.04/0.99  num_of_sem_filtered_clauses:            1
% 1.04/0.99  num_of_subtypes:                        3
% 1.04/0.99  monotx_restored_types:                  1
% 1.04/0.99  sat_num_of_epr_types:                   0
% 1.04/0.99  sat_num_of_non_cyclic_types:            0
% 1.04/0.99  sat_guarded_non_collapsed_types:        0
% 1.04/0.99  num_pure_diseq_elim:                    0
% 1.04/0.99  simp_replaced_by:                       0
% 1.04/0.99  res_preprocessed:                       60
% 1.04/0.99  prep_upred:                             0
% 1.04/0.99  prep_unflattend:                        11
% 1.04/0.99  smt_new_axioms:                         0
% 1.04/0.99  pred_elim_cands:                        3
% 1.04/0.99  pred_elim:                              4
% 1.04/0.99  pred_elim_cl:                           5
% 1.04/0.99  pred_elim_cycles:                       6
% 1.04/0.99  merged_defs:                            0
% 1.04/0.99  merged_defs_ncl:                        0
% 1.04/0.99  bin_hyper_res:                          0
% 1.04/0.99  prep_cycles:                            4
% 1.04/0.99  pred_elim_time:                         0.002
% 1.04/0.99  splitting_time:                         0.
% 1.04/0.99  sem_filter_time:                        0.
% 1.04/0.99  monotx_time:                            0.
% 1.04/0.99  subtype_inf_time:                       0.001
% 1.04/0.99  
% 1.04/0.99  ------ Problem properties
% 1.04/0.99  
% 1.04/0.99  clauses:                                9
% 1.04/0.99  conjectures:                            3
% 1.04/0.99  epr:                                    4
% 1.04/0.99  horn:                                   7
% 1.04/0.99  ground:                                 5
% 1.04/0.99  unary:                                  2
% 1.04/0.99  binary:                                 5
% 1.04/0.99  lits:                                   20
% 1.04/0.99  lits_eq:                                5
% 1.04/0.99  fd_pure:                                0
% 1.04/0.99  fd_pseudo:                              0
% 1.04/0.99  fd_cond:                                1
% 1.04/0.99  fd_pseudo_cond:                         0
% 1.04/0.99  ac_symbols:                             0
% 1.04/0.99  
% 1.04/0.99  ------ Propositional Solver
% 1.04/0.99  
% 1.04/0.99  prop_solver_calls:                      28
% 1.04/0.99  prop_fast_solver_calls:                 361
% 1.04/0.99  smt_solver_calls:                       0
% 1.04/0.99  smt_fast_solver_calls:                  0
% 1.04/0.99  prop_num_of_clauses:                    459
% 1.04/0.99  prop_preprocess_simplified:             1710
% 1.04/0.99  prop_fo_subsumed:                       13
% 1.04/0.99  prop_solver_time:                       0.
% 1.04/0.99  smt_solver_time:                        0.
% 1.04/0.99  smt_fast_solver_time:                   0.
% 1.04/0.99  prop_fast_solver_time:                  0.
% 1.04/0.99  prop_unsat_core_time:                   0.
% 1.04/0.99  
% 1.04/0.99  ------ QBF
% 1.04/0.99  
% 1.04/0.99  qbf_q_res:                              0
% 1.04/0.99  qbf_num_tautologies:                    0
% 1.04/0.99  qbf_prep_cycles:                        0
% 1.04/0.99  
% 1.04/0.99  ------ BMC1
% 1.04/0.99  
% 1.04/0.99  bmc1_current_bound:                     -1
% 1.04/0.99  bmc1_last_solved_bound:                 -1
% 1.04/0.99  bmc1_unsat_core_size:                   -1
% 1.04/0.99  bmc1_unsat_core_parents_size:           -1
% 1.04/0.99  bmc1_merge_next_fun:                    0
% 1.04/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.04/0.99  
% 1.04/0.99  ------ Instantiation
% 1.04/0.99  
% 1.04/0.99  inst_num_of_clauses:                    139
% 1.04/0.99  inst_num_in_passive:                    34
% 1.04/0.99  inst_num_in_active:                     83
% 1.04/0.99  inst_num_in_unprocessed:                22
% 1.04/0.99  inst_num_of_loops:                      120
% 1.04/0.99  inst_num_of_learning_restarts:          0
% 1.04/0.99  inst_num_moves_active_passive:          32
% 1.04/0.99  inst_lit_activity:                      0
% 1.04/0.99  inst_lit_activity_moves:                0
% 1.04/0.99  inst_num_tautologies:                   0
% 1.04/0.99  inst_num_prop_implied:                  0
% 1.04/0.99  inst_num_existing_simplified:           0
% 1.04/0.99  inst_num_eq_res_simplified:             0
% 1.04/0.99  inst_num_child_elim:                    0
% 1.04/0.99  inst_num_of_dismatching_blockings:      3
% 1.04/0.99  inst_num_of_non_proper_insts:           97
% 1.04/0.99  inst_num_of_duplicates:                 0
% 1.04/0.99  inst_inst_num_from_inst_to_res:         0
% 1.04/0.99  inst_dismatching_checking_time:         0.
% 1.04/0.99  
% 1.04/0.99  ------ Resolution
% 1.04/0.99  
% 1.04/0.99  res_num_of_clauses:                     0
% 1.04/0.99  res_num_in_passive:                     0
% 1.04/0.99  res_num_in_active:                      0
% 1.04/0.99  res_num_of_loops:                       64
% 1.04/0.99  res_forward_subset_subsumed:            19
% 1.04/0.99  res_backward_subset_subsumed:           0
% 1.04/0.99  res_forward_subsumed:                   0
% 1.04/0.99  res_backward_subsumed:                  0
% 1.04/0.99  res_forward_subsumption_resolution:     0
% 1.04/0.99  res_backward_subsumption_resolution:    0
% 1.04/0.99  res_clause_to_clause_subsumption:       24
% 1.04/0.99  res_orphan_elimination:                 0
% 1.04/0.99  res_tautology_del:                      22
% 1.04/0.99  res_num_eq_res_simplified:              0
% 1.04/0.99  res_num_sel_changes:                    0
% 1.04/0.99  res_moves_from_active_to_pass:          0
% 1.04/0.99  
% 1.04/0.99  ------ Superposition
% 1.04/0.99  
% 1.04/0.99  sup_time_total:                         0.
% 1.04/0.99  sup_time_generating:                    0.
% 1.04/0.99  sup_time_sim_full:                      0.
% 1.04/0.99  sup_time_sim_immed:                     0.
% 1.04/0.99  
% 1.04/0.99  sup_num_of_clauses:                     10
% 1.04/0.99  sup_num_in_active:                      8
% 1.04/0.99  sup_num_in_passive:                     2
% 1.04/0.99  sup_num_of_loops:                       23
% 1.04/0.99  sup_fw_superposition:                   6
% 1.04/0.99  sup_bw_superposition:                   15
% 1.04/0.99  sup_immediate_simplified:               13
% 1.04/0.99  sup_given_eliminated:                   0
% 1.04/0.99  comparisons_done:                       0
% 1.04/0.99  comparisons_avoided:                    3
% 1.04/0.99  
% 1.04/0.99  ------ Simplifications
% 1.04/0.99  
% 1.04/0.99  
% 1.04/0.99  sim_fw_subset_subsumed:                 7
% 1.04/0.99  sim_bw_subset_subsumed:                 9
% 1.04/0.99  sim_fw_subsumed:                        0
% 1.04/0.99  sim_bw_subsumed:                        0
% 1.04/0.99  sim_fw_subsumption_res:                 0
% 1.04/0.99  sim_bw_subsumption_res:                 0
% 1.04/0.99  sim_tautology_del:                      0
% 1.04/0.99  sim_eq_tautology_del:                   0
% 1.04/0.99  sim_eq_res_simp:                        1
% 1.04/0.99  sim_fw_demodulated:                     0
% 1.04/0.99  sim_bw_demodulated:                     11
% 1.04/0.99  sim_light_normalised:                   5
% 1.04/0.99  sim_joinable_taut:                      0
% 1.04/0.99  sim_joinable_simp:                      0
% 1.04/0.99  sim_ac_normalised:                      0
% 1.04/0.99  sim_smt_subsumption:                    0
% 1.04/0.99  
%------------------------------------------------------------------------------
