%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:48 EST 2020

% Result     : Theorem 11.80s
% Output     : CNFRefutation 11.80s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 882 expanded)
%              Number of clauses        :   67 ( 316 expanded)
%              Number of leaves         :   12 ( 158 expanded)
%              Depth                    :   24
%              Number of atoms          :  354 (3123 expanded)
%              Number of equality atoms :  109 ( 491 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f29])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

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
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f44])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_32053,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_32041,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_15,c_13])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_259,plain,
    ( r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_16,c_14])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_259])).

cnf(c_32033,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
    | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_32454,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_32041,c_32033])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_32685,plain,
    ( r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32454,c_20])).

cnf(c_32686,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_32685])).

cnf(c_32694,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(k5_partfun1(sK1,sK2,sK3),X0),k1_funct_2(sK1,sK2)) = iProver_top
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_32053,c_32686])).

cnf(c_10,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_141,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_142,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_141])).

cnf(c_182,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_142])).

cnf(c_32039,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_182])).

cnf(c_32794,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),X0) = iProver_top
    | r1_tarski(k1_funct_2(sK1,sK2),X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_32694,c_32039])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_22,plain,
    ( r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_32054,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_32792,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_32694,c_32054])).

cnf(c_32823,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32794,c_22,c_32792])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_32045,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_32608,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(k5_partfun1(sK1,sK2,sK3)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_32041,c_32045])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_32049,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_32288,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_32053,c_32039])).

cnf(c_32334,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_32049,c_32288])).

cnf(c_32042,plain,
    ( r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_32354,plain,
    ( v1_xboole_0(k5_partfun1(sK1,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_32334,c_32042])).

cnf(c_32661,plain,
    ( v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32608,c_20,c_32354])).

cnf(c_32828,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_32823,c_32661])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_52,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_32955,plain,
    ( v1_xboole_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32828,c_52])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_32048,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_32050,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_32353,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_32334,c_32050])).

cnf(c_32417,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_32048,c_32353])).

cnf(c_32960,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_32955,c_32417])).

cnf(c_32837,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32823,c_32041])).

cnf(c_33287,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32960,c_32837])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(k1_xboole_0,X4))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | X5 != X3
    | X2 != X4
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r2_hidden(X0,k5_partfun1(k1_xboole_0,X1,X2))
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0))
    | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_280,c_16,c_14])).

cnf(c_32032,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0)) != iProver_top
    | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_33535,plain,
    ( r2_hidden(X0,k5_partfun1(k1_xboole_0,k1_xboole_0,sK3)) != iProver_top
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_33287,c_32032])).

cnf(c_33781,plain,
    ( r2_hidden(X0,k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,k5_partfun1(k1_xboole_0,k1_xboole_0,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33535,c_20])).

cnf(c_33782,plain,
    ( r2_hidden(X0,k5_partfun1(k1_xboole_0,k1_xboole_0,sK3)) != iProver_top
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_33781])).

cnf(c_33789,plain,
    ( r2_hidden(sK0(k5_partfun1(k1_xboole_0,k1_xboole_0,sK3),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_32053,c_33782])).

cnf(c_33929,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK3),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_33789,c_32054])).

cnf(c_32836,plain,
    ( r1_tarski(k5_partfun1(sK1,k1_xboole_0,sK3),k1_funct_2(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_32823,c_32042])).

cnf(c_33286,plain,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK3),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_32960,c_32836])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33929,c_33286])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:32:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.80/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.80/1.99  
% 11.80/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.80/1.99  
% 11.80/1.99  ------  iProver source info
% 11.80/1.99  
% 11.80/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.80/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.80/1.99  git: non_committed_changes: false
% 11.80/1.99  git: last_make_outside_of_git: false
% 11.80/1.99  
% 11.80/1.99  ------ 
% 11.80/1.99  ------ Parsing...
% 11.80/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  ------ Proving...
% 11.80/1.99  ------ Problem Properties 
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  clauses                                 18
% 11.80/1.99  conjectures                             4
% 11.80/1.99  EPR                                     7
% 11.80/1.99  Horn                                    15
% 11.80/1.99  unary                                   6
% 11.80/1.99  binary                                  4
% 11.80/1.99  lits                                    45
% 11.80/1.99  lits eq                                 2
% 11.80/1.99  fd_pure                                 0
% 11.80/1.99  fd_pseudo                               0
% 11.80/1.99  fd_cond                                 1
% 11.80/1.99  fd_pseudo_cond                          1
% 11.80/1.99  AC symbols                              0
% 11.80/1.99  
% 11.80/1.99  ------ Input Options Time Limit: Unbounded
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 11.80/1.99  Current options:
% 11.80/1.99  ------ 
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  % SZS status Theorem for theBenchmark.p
% 11.80/1.99  
% 11.80/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.80/1.99  
% 11.80/1.99  fof(f1,axiom,(
% 11.80/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f12,plain,(
% 11.80/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.80/1.99    inference(ennf_transformation,[],[f1])).
% 11.80/1.99  
% 11.80/1.99  fof(f22,plain,(
% 11.80/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.80/1.99    inference(nnf_transformation,[],[f12])).
% 11.80/1.99  
% 11.80/1.99  fof(f23,plain,(
% 11.80/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.80/1.99    inference(rectify,[],[f22])).
% 11.80/1.99  
% 11.80/1.99  fof(f24,plain,(
% 11.80/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.80/1.99    introduced(choice_axiom,[])).
% 11.80/1.99  
% 11.80/1.99  fof(f25,plain,(
% 11.80/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.80/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 11.80/1.99  
% 11.80/1.99  fof(f32,plain,(
% 11.80/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f25])).
% 11.80/1.99  
% 11.80/1.99  fof(f10,conjecture,(
% 11.80/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f11,negated_conjecture,(
% 11.80/1.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 11.80/1.99    inference(negated_conjecture,[],[f10])).
% 11.80/1.99  
% 11.80/1.99  fof(f20,plain,(
% 11.80/1.99    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 11.80/1.99    inference(ennf_transformation,[],[f11])).
% 11.80/1.99  
% 11.80/1.99  fof(f21,plain,(
% 11.80/1.99    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 11.80/1.99    inference(flattening,[],[f20])).
% 11.80/1.99  
% 11.80/1.99  fof(f29,plain,(
% 11.80/1.99    ? [X0,X1,X2] : (~r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3))),
% 11.80/1.99    introduced(choice_axiom,[])).
% 11.80/1.99  
% 11.80/1.99  fof(f30,plain,(
% 11.80/1.99    ~r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK3)),
% 11.80/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f29])).
% 11.80/1.99  
% 11.80/1.99  fof(f49,plain,(
% 11.80/1.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 11.80/1.99    inference(cnf_transformation,[],[f30])).
% 11.80/1.99  
% 11.80/1.99  fof(f9,axiom,(
% 11.80/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f18,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.80/1.99    inference(ennf_transformation,[],[f9])).
% 11.80/1.99  
% 11.80/1.99  fof(f19,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.80/1.99    inference(flattening,[],[f18])).
% 11.80/1.99  
% 11.80/1.99  fof(f46,plain,(
% 11.80/1.99    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X1) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f19])).
% 11.80/1.99  
% 11.80/1.99  fof(f8,axiom,(
% 11.80/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => r2_hidden(X2,k1_funct_2(X0,X1))))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f16,plain,(
% 11.80/1.99    ! [X0,X1,X2] : ((r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.80/1.99    inference(ennf_transformation,[],[f8])).
% 11.80/1.99  
% 11.80/1.99  fof(f17,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.80/1.99    inference(flattening,[],[f16])).
% 11.80/1.99  
% 11.80/1.99  fof(f43,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f17])).
% 11.80/1.99  
% 11.80/1.99  fof(f45,plain,(
% 11.80/1.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(X3) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f19])).
% 11.80/1.99  
% 11.80/1.99  fof(f47,plain,(
% 11.80/1.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f19])).
% 11.80/1.99  
% 11.80/1.99  fof(f48,plain,(
% 11.80/1.99    v1_funct_1(sK3)),
% 11.80/1.99    inference(cnf_transformation,[],[f30])).
% 11.80/1.99  
% 11.80/1.99  fof(f6,axiom,(
% 11.80/1.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f13,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.80/1.99    inference(ennf_transformation,[],[f6])).
% 11.80/1.99  
% 11.80/1.99  fof(f41,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f13])).
% 11.80/1.99  
% 11.80/1.99  fof(f5,axiom,(
% 11.80/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f28,plain,(
% 11.80/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.80/1.99    inference(nnf_transformation,[],[f5])).
% 11.80/1.99  
% 11.80/1.99  fof(f40,plain,(
% 11.80/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f28])).
% 11.80/1.99  
% 11.80/1.99  fof(f50,plain,(
% 11.80/1.99    ~r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))),
% 11.80/1.99    inference(cnf_transformation,[],[f30])).
% 11.80/1.99  
% 11.80/1.99  fof(f33,plain,(
% 11.80/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f25])).
% 11.80/1.99  
% 11.80/1.99  fof(f7,axiom,(
% 11.80/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2) & v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k5_partfun1(X0,X1,X2)))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f14,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.80/1.99    inference(ennf_transformation,[],[f7])).
% 11.80/1.99  
% 11.80/1.99  fof(f15,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.80/1.99    inference(flattening,[],[f14])).
% 11.80/1.99  
% 11.80/1.99  fof(f42,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f15])).
% 11.80/1.99  
% 11.80/1.99  fof(f3,axiom,(
% 11.80/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f26,plain,(
% 11.80/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.80/1.99    inference(nnf_transformation,[],[f3])).
% 11.80/1.99  
% 11.80/1.99  fof(f27,plain,(
% 11.80/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.80/1.99    inference(flattening,[],[f26])).
% 11.80/1.99  
% 11.80/1.99  fof(f35,plain,(
% 11.80/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.80/1.99    inference(cnf_transformation,[],[f27])).
% 11.80/1.99  
% 11.80/1.99  fof(f52,plain,(
% 11.80/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.80/1.99    inference(equality_resolution,[],[f35])).
% 11.80/1.99  
% 11.80/1.99  fof(f2,axiom,(
% 11.80/1.99    v1_xboole_0(k1_xboole_0)),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f34,plain,(
% 11.80/1.99    v1_xboole_0(k1_xboole_0)),
% 11.80/1.99    inference(cnf_transformation,[],[f2])).
% 11.80/1.99  
% 11.80/1.99  fof(f4,axiom,(
% 11.80/1.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f38,plain,(
% 11.80/1.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f4])).
% 11.80/1.99  
% 11.80/1.99  fof(f37,plain,(
% 11.80/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f27])).
% 11.80/1.99  
% 11.80/1.99  fof(f44,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_funct_2(X0,X1)) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f17])).
% 11.80/1.99  
% 11.80/1.99  fof(f53,plain,(
% 11.80/1.99    ( ! [X2,X1] : (r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(equality_resolution,[],[f44])).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1,plain,
% 11.80/1.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.80/1.99      inference(cnf_transformation,[],[f32]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32053,plain,
% 11.80/1.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.80/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_18,negated_conjecture,
% 11.80/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 11.80/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32041,plain,
% 11.80/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_15,plain,
% 11.80/1.99      ( v1_funct_2(X0,X1,X2)
% 11.80/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
% 11.80/1.99      | ~ v1_funct_1(X3) ),
% 11.80/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_13,plain,
% 11.80/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.80/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | r2_hidden(X0,k1_funct_2(X1,X2))
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | k1_xboole_0 = X2 ),
% 11.80/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_255,plain,
% 11.80/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 11.80/1.99      | r2_hidden(X3,k1_funct_2(X1,X2))
% 11.80/1.99      | ~ v1_funct_1(X3)
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | k1_xboole_0 = X2 ),
% 11.80/1.99      inference(resolution,[status(thm)],[c_15,c_13]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_16,plain,
% 11.80/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | v1_funct_1(X3) ),
% 11.80/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_14,plain,
% 11.80/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 11.80/1.99      | ~ v1_funct_1(X0) ),
% 11.80/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_259,plain,
% 11.80/1.99      ( r2_hidden(X3,k1_funct_2(X1,X2))
% 11.80/1.99      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 11.80/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | k1_xboole_0 = X2 ),
% 11.80/1.99      inference(global_propositional_subsumption,
% 11.80/1.99                [status(thm)],
% 11.80/1.99                [c_255,c_16,c_14]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_260,plain,
% 11.80/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
% 11.80/1.99      | r2_hidden(X3,k1_funct_2(X1,X2))
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | k1_xboole_0 = X2 ),
% 11.80/1.99      inference(renaming,[status(thm)],[c_259]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32033,plain,
% 11.80/1.99      ( k1_xboole_0 = X0
% 11.80/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 11.80/1.99      | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
% 11.80/1.99      | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
% 11.80/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32454,plain,
% 11.80/1.99      ( sK2 = k1_xboole_0
% 11.80/1.99      | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
% 11.80/1.99      | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
% 11.80/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_32041,c_32033]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_19,negated_conjecture,
% 11.80/1.99      ( v1_funct_1(sK3) ),
% 11.80/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_20,plain,
% 11.80/1.99      ( v1_funct_1(sK3) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32685,plain,
% 11.80/1.99      ( r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
% 11.80/1.99      | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
% 11.80/1.99      | sK2 = k1_xboole_0 ),
% 11.80/1.99      inference(global_propositional_subsumption,
% 11.80/1.99                [status(thm)],
% 11.80/1.99                [c_32454,c_20]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32686,plain,
% 11.80/1.99      ( sK2 = k1_xboole_0
% 11.80/1.99      | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
% 11.80/1.99      | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top ),
% 11.80/1.99      inference(renaming,[status(thm)],[c_32685]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32694,plain,
% 11.80/1.99      ( sK2 = k1_xboole_0
% 11.80/1.99      | r2_hidden(sK0(k5_partfun1(sK1,sK2,sK3),X0),k1_funct_2(sK1,sK2)) = iProver_top
% 11.80/1.99      | r1_tarski(k5_partfun1(sK1,sK2,sK3),X0) = iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_32053,c_32686]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_10,negated_conjecture,
% 11.80/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.80/1.99      | ~ r2_hidden(X2,X0)
% 11.80/1.99      | ~ v1_xboole_0(X1) ),
% 11.80/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_8,plain,
% 11.80/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.80/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_141,plain,
% 11.80/1.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.80/1.99      inference(prop_impl,[status(thm)],[c_8]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_142,plain,
% 11.80/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.80/1.99      inference(renaming,[status(thm)],[c_141]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_182,negated_conjecture,
% 11.80/1.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 11.80/1.99      inference(bin_hyper_res,[status(thm)],[c_10,c_142]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32039,plain,
% 11.80/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.80/1.99      | r1_tarski(X1,X2) != iProver_top
% 11.80/1.99      | v1_xboole_0(X2) != iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_182]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32794,plain,
% 11.80/1.99      ( sK2 = k1_xboole_0
% 11.80/1.99      | r1_tarski(k5_partfun1(sK1,sK2,sK3),X0) = iProver_top
% 11.80/1.99      | r1_tarski(k1_funct_2(sK1,sK2),X1) != iProver_top
% 11.80/1.99      | v1_xboole_0(X1) != iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_32694,c_32039]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_17,negated_conjecture,
% 11.80/1.99      ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) ),
% 11.80/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_22,plain,
% 11.80/1.99      ( r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) != iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_0,plain,
% 11.80/1.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.80/1.99      inference(cnf_transformation,[],[f33]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32054,plain,
% 11.80/1.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.80/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32792,plain,
% 11.80/1.99      ( sK2 = k1_xboole_0
% 11.80/1.99      | r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) = iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_32694,c_32054]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32823,plain,
% 11.80/1.99      ( sK2 = k1_xboole_0 ),
% 11.80/1.99      inference(global_propositional_subsumption,
% 11.80/1.99                [status(thm)],
% 11.80/1.99                [c_32794,c_22,c_32792]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_11,plain,
% 11.80/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | ~ v1_xboole_0(X2)
% 11.80/1.99      | v1_xboole_0(X1)
% 11.80/1.99      | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
% 11.80/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32045,plain,
% 11.80/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.80/1.99      | v1_funct_1(X0) != iProver_top
% 11.80/1.99      | v1_xboole_0(X2) != iProver_top
% 11.80/1.99      | v1_xboole_0(X1) = iProver_top
% 11.80/1.99      | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32608,plain,
% 11.80/1.99      ( v1_funct_1(sK3) != iProver_top
% 11.80/1.99      | v1_xboole_0(k5_partfun1(sK1,sK2,sK3)) = iProver_top
% 11.80/1.99      | v1_xboole_0(sK2) != iProver_top
% 11.80/1.99      | v1_xboole_0(sK1) = iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_32041,c_32045]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_6,plain,
% 11.80/1.99      ( r1_tarski(X0,X0) ),
% 11.80/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32049,plain,
% 11.80/1.99      ( r1_tarski(X0,X0) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32288,plain,
% 11.80/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.80/1.99      | r1_tarski(X0,X2) = iProver_top
% 11.80/1.99      | v1_xboole_0(X1) != iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_32053,c_32039]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32334,plain,
% 11.80/1.99      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_32049,c_32288]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32042,plain,
% 11.80/1.99      ( r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) != iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32354,plain,
% 11.80/1.99      ( v1_xboole_0(k5_partfun1(sK1,sK2,sK3)) != iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_32334,c_32042]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32661,plain,
% 11.80/1.99      ( v1_xboole_0(sK2) != iProver_top
% 11.80/1.99      | v1_xboole_0(sK1) = iProver_top ),
% 11.80/1.99      inference(global_propositional_subsumption,
% 11.80/1.99                [status(thm)],
% 11.80/1.99                [c_32608,c_20,c_32354]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32828,plain,
% 11.80/1.99      ( v1_xboole_0(sK1) = iProver_top
% 11.80/1.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.80/1.99      inference(demodulation,[status(thm)],[c_32823,c_32661]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_3,plain,
% 11.80/1.99      ( v1_xboole_0(k1_xboole_0) ),
% 11.80/1.99      inference(cnf_transformation,[],[f34]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_52,plain,
% 11.80/1.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32955,plain,
% 11.80/1.99      ( v1_xboole_0(sK1) = iProver_top ),
% 11.80/1.99      inference(global_propositional_subsumption,
% 11.80/1.99                [status(thm)],
% 11.80/1.99                [c_32828,c_52]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_7,plain,
% 11.80/1.99      ( r1_tarski(k1_xboole_0,X0) ),
% 11.80/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32048,plain,
% 11.80/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_4,plain,
% 11.80/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.80/1.99      inference(cnf_transformation,[],[f37]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32050,plain,
% 11.80/1.99      ( X0 = X1
% 11.80/1.99      | r1_tarski(X1,X0) != iProver_top
% 11.80/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32353,plain,
% 11.80/1.99      ( X0 = X1
% 11.80/1.99      | r1_tarski(X0,X1) != iProver_top
% 11.80/1.99      | v1_xboole_0(X1) != iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_32334,c_32050]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32417,plain,
% 11.80/1.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_32048,c_32353]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32960,plain,
% 11.80/1.99      ( sK1 = k1_xboole_0 ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_32955,c_32417]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32837,plain,
% 11.80/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 11.80/1.99      inference(demodulation,[status(thm)],[c_32823,c_32041]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_33287,plain,
% 11.80/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.80/1.99      inference(demodulation,[status(thm)],[c_32960,c_32837]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_12,plain,
% 11.80/1.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 11.80/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.80/1.99      | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
% 11.80/1.99      | ~ v1_funct_1(X0) ),
% 11.80/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_279,plain,
% 11.80/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 11.80/1.99      | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
% 11.80/1.99      | r2_hidden(X3,k1_funct_2(k1_xboole_0,X4))
% 11.80/1.99      | ~ v1_funct_1(X3)
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | X5 != X3
% 11.80/1.99      | X2 != X4
% 11.80/1.99      | k1_xboole_0 != X1 ),
% 11.80/1.99      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_280,plain,
% 11.80/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.80/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.80/1.99      | ~ r2_hidden(X0,k5_partfun1(k1_xboole_0,X1,X2))
% 11.80/1.99      | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | ~ v1_funct_1(X2) ),
% 11.80/1.99      inference(unflattening,[status(thm)],[c_279]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_296,plain,
% 11.80/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.80/1.99      | ~ r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0))
% 11.80/1.99      | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
% 11.80/1.99      | ~ v1_funct_1(X0) ),
% 11.80/1.99      inference(forward_subsumption_resolution,
% 11.80/1.99                [status(thm)],
% 11.80/1.99                [c_280,c_16,c_14]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32032,plain,
% 11.80/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 11.80/1.99      | r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0)) != iProver_top
% 11.80/1.99      | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) = iProver_top
% 11.80/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_33535,plain,
% 11.80/1.99      ( r2_hidden(X0,k5_partfun1(k1_xboole_0,k1_xboole_0,sK3)) != iProver_top
% 11.80/1.99      | r2_hidden(X0,k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top
% 11.80/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_33287,c_32032]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_33781,plain,
% 11.80/1.99      ( r2_hidden(X0,k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top
% 11.80/1.99      | r2_hidden(X0,k5_partfun1(k1_xboole_0,k1_xboole_0,sK3)) != iProver_top ),
% 11.80/1.99      inference(global_propositional_subsumption,
% 11.80/1.99                [status(thm)],
% 11.80/1.99                [c_33535,c_20]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_33782,plain,
% 11.80/1.99      ( r2_hidden(X0,k5_partfun1(k1_xboole_0,k1_xboole_0,sK3)) != iProver_top
% 11.80/1.99      | r2_hidden(X0,k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 11.80/1.99      inference(renaming,[status(thm)],[c_33781]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_33789,plain,
% 11.80/1.99      ( r2_hidden(sK0(k5_partfun1(k1_xboole_0,k1_xboole_0,sK3),X0),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top
% 11.80/1.99      | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK3),X0) = iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_32053,c_33782]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_33929,plain,
% 11.80/1.99      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK3),k1_funct_2(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_33789,c_32054]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_32836,plain,
% 11.80/1.99      ( r1_tarski(k5_partfun1(sK1,k1_xboole_0,sK3),k1_funct_2(sK1,k1_xboole_0)) != iProver_top ),
% 11.80/1.99      inference(demodulation,[status(thm)],[c_32823,c_32042]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_33286,plain,
% 11.80/1.99      ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,sK3),k1_funct_2(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 11.80/1.99      inference(demodulation,[status(thm)],[c_32960,c_32836]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(contradiction,plain,
% 11.80/1.99      ( $false ),
% 11.80/1.99      inference(minisat,[status(thm)],[c_33929,c_33286]) ).
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.80/1.99  
% 11.80/1.99  ------                               Statistics
% 11.80/1.99  
% 11.80/1.99  ------ Selected
% 11.80/1.99  
% 11.80/1.99  total_time:                             1.236
% 11.80/1.99  
%------------------------------------------------------------------------------
