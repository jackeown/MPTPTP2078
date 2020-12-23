%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:17 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 595 expanded)
%              Number of clauses        :   81 ( 206 expanded)
%              Number of leaves         :   15 ( 128 expanded)
%              Depth                    :   21
%              Number of atoms          :  354 (2343 expanded)
%              Number of equality atoms :  141 ( 329 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(sK1,k2_tops_1(X0,sK1))
          | ~ v2_tops_1(sK1,X0) )
        & ( r1_tarski(sK1,k2_tops_1(X0,sK1))
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_714,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_720,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1964,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_720])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_917,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_918,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_917])).

cnf(c_920,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_2328,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1964,c_19,c_20,c_920])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_730,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2334,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2328,c_730])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_726,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2450,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2334,c_726])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_928,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_930,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_928])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1071,plain,
    ( r1_xboole_0(k2_tops_1(sK0,X0),k1_tops_1(sK0,X0))
    | ~ r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1072,plain,
    ( r1_xboole_0(k2_tops_1(sK0,X0),k1_tops_1(sK0,X0)) = iProver_top
    | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1071])).

cnf(c_1074,plain,
    ( r1_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = iProver_top
    | r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1288,plain,
    ( ~ r1_tarski(X0,k2_tops_1(sK0,X1))
    | r1_xboole_0(X0,k1_tops_1(sK0,X1))
    | ~ r1_xboole_0(k2_tops_1(sK0,X1),k1_tops_1(sK0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1289,plain,
    ( r1_tarski(X0,k2_tops_1(sK0,X1)) != iProver_top
    | r1_xboole_0(X0,k1_tops_1(sK0,X1)) = iProver_top
    | r1_xboole_0(k2_tops_1(sK0,X1),k1_tops_1(sK0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1288])).

cnf(c_1291,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top
    | r1_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) != iProver_top
    | r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1289])).

cnf(c_16,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_715,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1307,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_730])).

cnf(c_14,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_717,plain,
    ( k1_tops_1(X0,X1) = k1_xboole_0
    | v2_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1103,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_717])).

cnf(c_1455,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1103,c_19])).

cnf(c_1456,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1455])).

cnf(c_1464,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1307,c_1456])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_729,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1583,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_729])).

cnf(c_2048,plain,
    ( ~ r1_xboole_0(X0,k1_tops_1(sK0,X1))
    | r1_xboole_0(k1_tops_1(sK0,X1),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2049,plain,
    ( r1_xboole_0(X0,k1_tops_1(sK0,X1)) != iProver_top
    | r1_xboole_0(k1_tops_1(sK0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2048])).

cnf(c_2051,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2049])).

cnf(c_3067,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2450,c_19,c_20,c_930,c_1074,c_1291,c_1583,c_2051])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_725,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3073,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3067,c_725])).

cnf(c_3075,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3073,c_2334])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_721,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2797,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_721])).

cnf(c_981,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_983,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_981])).

cnf(c_3063,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2797,c_18,c_17,c_983])).

cnf(c_3191,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3075,c_3063])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_723,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_724,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2757,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X2) = k4_xboole_0(k2_pre_topc(X0,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_723,c_724])).

cnf(c_5752,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_2757])).

cnf(c_5852,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5752,c_19])).

cnf(c_5856,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3191,c_5852])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_727,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1012,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_727,c_725])).

cnf(c_5858,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5856,c_1012])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_716,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5862,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5858,c_716])).

cnf(c_13,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1161,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1162,plain,
    ( k1_tops_1(sK0,X0) != k1_xboole_0
    | v2_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1161])).

cnf(c_1164,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_912,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_913,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_915,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5862,c_3075,c_1164,c_915,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:39:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.73/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/1.01  
% 3.73/1.01  ------  iProver source info
% 3.73/1.01  
% 3.73/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.73/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/1.01  git: non_committed_changes: false
% 3.73/1.01  git: last_make_outside_of_git: false
% 3.73/1.01  
% 3.73/1.01  ------ 
% 3.73/1.01  ------ Parsing...
% 3.73/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  ------ Proving...
% 3.73/1.01  ------ Problem Properties 
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  clauses                                 19
% 3.73/1.01  conjectures                             4
% 3.73/1.01  EPR                                     4
% 3.73/1.01  Horn                                    18
% 3.73/1.01  unary                                   3
% 3.73/1.01  binary                                  8
% 3.73/1.01  lits                                    45
% 3.73/1.01  lits eq                                 8
% 3.73/1.01  fd_pure                                 0
% 3.73/1.01  fd_pseudo                               0
% 3.73/1.01  fd_cond                                 0
% 3.73/1.01  fd_pseudo_cond                          0
% 3.73/1.01  AC symbols                              0
% 3.73/1.01  
% 3.73/1.01  ------ Input Options Time Limit: Unbounded
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ 
% 3.73/1.01  Current options:
% 3.73/1.01  ------ 
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  % SZS status Theorem for theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  fof(f13,conjecture,(
% 3.73/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f14,negated_conjecture,(
% 3.73/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.73/1.01    inference(negated_conjecture,[],[f13])).
% 3.73/1.01  
% 3.73/1.01  fof(f26,plain,(
% 3.73/1.01    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.73/1.01    inference(ennf_transformation,[],[f14])).
% 3.73/1.01  
% 3.73/1.01  fof(f30,plain,(
% 3.73/1.01    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.73/1.01    inference(nnf_transformation,[],[f26])).
% 3.73/1.01  
% 3.73/1.01  fof(f31,plain,(
% 3.73/1.01    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.73/1.01    inference(flattening,[],[f30])).
% 3.73/1.01  
% 3.73/1.01  fof(f33,plain,(
% 3.73/1.01    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~r1_tarski(sK1,k2_tops_1(X0,sK1)) | ~v2_tops_1(sK1,X0)) & (r1_tarski(sK1,k2_tops_1(X0,sK1)) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.73/1.01    introduced(choice_axiom,[])).
% 3.73/1.01  
% 3.73/1.01  fof(f32,plain,(
% 3.73/1.01    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.73/1.01    introduced(choice_axiom,[])).
% 3.73/1.01  
% 3.73/1.01  fof(f34,plain,(
% 3.73/1.01    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.73/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 3.73/1.01  
% 3.73/1.01  fof(f51,plain,(
% 3.73/1.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.73/1.01    inference(cnf_transformation,[],[f34])).
% 3.73/1.01  
% 3.73/1.01  fof(f10,axiom,(
% 3.73/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f23,plain,(
% 3.73/1.01    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.73/1.01    inference(ennf_transformation,[],[f10])).
% 3.73/1.01  
% 3.73/1.01  fof(f46,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f23])).
% 3.73/1.01  
% 3.73/1.01  fof(f50,plain,(
% 3.73/1.01    l1_pre_topc(sK0)),
% 3.73/1.01    inference(cnf_transformation,[],[f34])).
% 3.73/1.01  
% 3.73/1.01  fof(f2,axiom,(
% 3.73/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f27,plain,(
% 3.73/1.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.73/1.01    inference(nnf_transformation,[],[f2])).
% 3.73/1.01  
% 3.73/1.01  fof(f37,plain,(
% 3.73/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f27])).
% 3.73/1.01  
% 3.73/1.01  fof(f5,axiom,(
% 3.73/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f28,plain,(
% 3.73/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.73/1.01    inference(nnf_transformation,[],[f5])).
% 3.73/1.01  
% 3.73/1.01  fof(f41,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.73/1.01    inference(cnf_transformation,[],[f28])).
% 3.73/1.01  
% 3.73/1.01  fof(f11,axiom,(
% 3.73/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f24,plain,(
% 3.73/1.01    ! [X0] : (! [X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.73/1.01    inference(ennf_transformation,[],[f11])).
% 3.73/1.01  
% 3.73/1.01  fof(f47,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f24])).
% 3.73/1.01  
% 3.73/1.01  fof(f1,axiom,(
% 3.73/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f15,plain,(
% 3.73/1.01    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.73/1.01    inference(ennf_transformation,[],[f1])).
% 3.73/1.01  
% 3.73/1.01  fof(f35,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f15])).
% 3.73/1.01  
% 3.73/1.01  fof(f3,axiom,(
% 3.73/1.01    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f16,plain,(
% 3.73/1.01    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.73/1.01    inference(ennf_transformation,[],[f3])).
% 3.73/1.01  
% 3.73/1.01  fof(f17,plain,(
% 3.73/1.01    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 3.73/1.01    inference(flattening,[],[f16])).
% 3.73/1.01  
% 3.73/1.01  fof(f38,plain,(
% 3.73/1.01    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f17])).
% 3.73/1.01  
% 3.73/1.01  fof(f52,plain,(
% 3.73/1.01    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 3.73/1.01    inference(cnf_transformation,[],[f34])).
% 3.73/1.01  
% 3.73/1.01  fof(f12,axiom,(
% 3.73/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f25,plain,(
% 3.73/1.01    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.73/1.01    inference(ennf_transformation,[],[f12])).
% 3.73/1.01  
% 3.73/1.01  fof(f29,plain,(
% 3.73/1.01    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.73/1.01    inference(nnf_transformation,[],[f25])).
% 3.73/1.01  
% 3.73/1.01  fof(f48,plain,(
% 3.73/1.01    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f29])).
% 3.73/1.01  
% 3.73/1.01  fof(f36,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.73/1.01    inference(cnf_transformation,[],[f27])).
% 3.73/1.01  
% 3.73/1.01  fof(f40,plain,(
% 3.73/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f28])).
% 3.73/1.01  
% 3.73/1.01  fof(f9,axiom,(
% 3.73/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f22,plain,(
% 3.73/1.01    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.73/1.01    inference(ennf_transformation,[],[f9])).
% 3.73/1.01  
% 3.73/1.01  fof(f45,plain,(
% 3.73/1.01    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f22])).
% 3.73/1.01  
% 3.73/1.01  fof(f7,axiom,(
% 3.73/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f19,plain,(
% 3.73/1.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.73/1.01    inference(ennf_transformation,[],[f7])).
% 3.73/1.01  
% 3.73/1.01  fof(f20,plain,(
% 3.73/1.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.73/1.01    inference(flattening,[],[f19])).
% 3.73/1.01  
% 3.73/1.01  fof(f43,plain,(
% 3.73/1.01    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f20])).
% 3.73/1.01  
% 3.73/1.01  fof(f6,axiom,(
% 3.73/1.01    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f18,plain,(
% 3.73/1.01    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.73/1.01    inference(ennf_transformation,[],[f6])).
% 3.73/1.01  
% 3.73/1.01  fof(f42,plain,(
% 3.73/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.73/1.01    inference(cnf_transformation,[],[f18])).
% 3.73/1.01  
% 3.73/1.01  fof(f4,axiom,(
% 3.73/1.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f39,plain,(
% 3.73/1.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f4])).
% 3.73/1.01  
% 3.73/1.01  fof(f53,plain,(
% 3.73/1.01    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 3.73/1.01    inference(cnf_transformation,[],[f34])).
% 3.73/1.01  
% 3.73/1.01  fof(f49,plain,(
% 3.73/1.01    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f29])).
% 3.73/1.01  
% 3.73/1.01  fof(f8,axiom,(
% 3.73/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f21,plain,(
% 3.73/1.01    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.73/1.01    inference(ennf_transformation,[],[f8])).
% 3.73/1.01  
% 3.73/1.01  fof(f44,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f21])).
% 3.73/1.01  
% 3.73/1.01  cnf(c_17,negated_conjecture,
% 3.73/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.73/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_714,plain,
% 3.73/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.01      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.73/1.01      | ~ l1_pre_topc(X1) ),
% 3.73/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_720,plain,
% 3.73/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.73/1.01      | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
% 3.73/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1964,plain,
% 3.73/1.01      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 3.73/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_714,c_720]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_18,negated_conjecture,
% 3.73/1.01      ( l1_pre_topc(sK0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_19,plain,
% 3.73/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_20,plain,
% 3.73/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_917,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.73/1.01      | r1_tarski(k1_tops_1(sK0,X0),X0)
% 3.73/1.01      | ~ l1_pre_topc(sK0) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_918,plain,
% 3.73/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.73/1.01      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top
% 3.73/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_917]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_920,plain,
% 3.73/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.73/1.01      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 3.73/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_918]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_2328,plain,
% 3.73/1.01      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.73/1.01      inference(global_propositional_subsumption,
% 3.73/1.01                [status(thm)],
% 3.73/1.01                [c_1964,c_19,c_20,c_920]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1,plain,
% 3.73/1.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.73/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_730,plain,
% 3.73/1.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.73/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_2334,plain,
% 3.73/1.01      ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_2328,c_730]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_5,plain,
% 3.73/1.01      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.73/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_726,plain,
% 3.73/1.01      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_2450,plain,
% 3.73/1.01      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 3.73/1.01      | r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_2334,c_726]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_12,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.01      | r1_xboole_0(k1_tops_1(X1,X0),k2_tops_1(X1,X0))
% 3.73/1.01      | ~ l1_pre_topc(X1) ),
% 3.73/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_927,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.73/1.01      | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0))
% 3.73/1.01      | ~ l1_pre_topc(sK0) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_928,plain,
% 3.73/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.73/1.01      | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) = iProver_top
% 3.73/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_930,plain,
% 3.73/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.73/1.01      | r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = iProver_top
% 3.73/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_928]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_0,plain,
% 3.73/1.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1071,plain,
% 3.73/1.01      ( r1_xboole_0(k2_tops_1(sK0,X0),k1_tops_1(sK0,X0))
% 3.73/1.01      | ~ r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1072,plain,
% 3.73/1.01      ( r1_xboole_0(k2_tops_1(sK0,X0),k1_tops_1(sK0,X0)) = iProver_top
% 3.73/1.01      | r1_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_1071]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1074,plain,
% 3.73/1.01      ( r1_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = iProver_top
% 3.73/1.01      | r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) != iProver_top ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_1072]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_3,plain,
% 3.73/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 3.73/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1288,plain,
% 3.73/1.01      ( ~ r1_tarski(X0,k2_tops_1(sK0,X1))
% 3.73/1.01      | r1_xboole_0(X0,k1_tops_1(sK0,X1))
% 3.73/1.01      | ~ r1_xboole_0(k2_tops_1(sK0,X1),k1_tops_1(sK0,X1)) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1289,plain,
% 3.73/1.01      ( r1_tarski(X0,k2_tops_1(sK0,X1)) != iProver_top
% 3.73/1.01      | r1_xboole_0(X0,k1_tops_1(sK0,X1)) = iProver_top
% 3.73/1.01      | r1_xboole_0(k2_tops_1(sK0,X1),k1_tops_1(sK0,X1)) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_1288]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1291,plain,
% 3.73/1.01      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top
% 3.73/1.01      | r1_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) != iProver_top
% 3.73/1.01      | r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) = iProver_top ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_1289]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_16,negated_conjecture,
% 3.73/1.01      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 3.73/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_715,plain,
% 3.73/1.01      ( v2_tops_1(sK1,sK0) = iProver_top
% 3.73/1.01      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1307,plain,
% 3.73/1.01      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_xboole_0
% 3.73/1.01      | v2_tops_1(sK1,sK0) = iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_715,c_730]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_14,plain,
% 3.73/1.01      ( ~ v2_tops_1(X0,X1)
% 3.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.01      | ~ l1_pre_topc(X1)
% 3.73/1.01      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.73/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_717,plain,
% 3.73/1.01      ( k1_tops_1(X0,X1) = k1_xboole_0
% 3.73/1.01      | v2_tops_1(X1,X0) != iProver_top
% 3.73/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.73/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1103,plain,
% 3.73/1.01      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.73/1.01      | v2_tops_1(sK1,sK0) != iProver_top
% 3.73/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_714,c_717]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1455,plain,
% 3.73/1.01      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.73/1.01      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.73/1.01      inference(global_propositional_subsumption,
% 3.73/1.01                [status(thm)],
% 3.73/1.01                [c_1103,c_19]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1456,plain,
% 3.73/1.01      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.73/1.01      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.73/1.01      inference(renaming,[status(thm)],[c_1455]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1464,plain,
% 3.73/1.01      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.73/1.01      | k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_1307,c_1456]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_2,plain,
% 3.73/1.01      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.73/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_729,plain,
% 3.73/1.01      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 3.73/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1583,plain,
% 3.73/1.01      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.73/1.01      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_1464,c_729]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_2048,plain,
% 3.73/1.01      ( ~ r1_xboole_0(X0,k1_tops_1(sK0,X1))
% 3.73/1.01      | r1_xboole_0(k1_tops_1(sK0,X1),X0) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_2049,plain,
% 3.73/1.01      ( r1_xboole_0(X0,k1_tops_1(sK0,X1)) != iProver_top
% 3.73/1.01      | r1_xboole_0(k1_tops_1(sK0,X1),X0) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_2048]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_2051,plain,
% 3.73/1.01      ( r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 3.73/1.01      | r1_xboole_0(sK1,k1_tops_1(sK0,sK1)) != iProver_top ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_2049]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_3067,plain,
% 3.73/1.01      ( r1_xboole_0(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.73/1.01      inference(global_propositional_subsumption,
% 3.73/1.01                [status(thm)],
% 3.73/1.01                [c_2450,c_19,c_20,c_930,c_1074,c_1291,c_1583,c_2051]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_6,plain,
% 3.73/1.01      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.73/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_725,plain,
% 3.73/1.01      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_3073,plain,
% 3.73/1.01      ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_tops_1(sK0,sK1) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_3067,c_725]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_3075,plain,
% 3.73/1.01      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.73/1.01      inference(light_normalisation,[status(thm)],[c_3073,c_2334]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_10,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.01      | ~ l1_pre_topc(X1)
% 3.73/1.01      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_721,plain,
% 3.73/1.01      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 3.73/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.73/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_2797,plain,
% 3.73/1.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.73/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_714,c_721]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_981,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.73/1.01      | ~ l1_pre_topc(sK0)
% 3.73/1.01      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_983,plain,
% 3.73/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.73/1.01      | ~ l1_pre_topc(sK0)
% 3.73/1.01      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_981]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_3063,plain,
% 3.73/1.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.73/1.01      inference(global_propositional_subsumption,
% 3.73/1.01                [status(thm)],
% 3.73/1.01                [c_2797,c_18,c_17,c_983]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_3191,plain,
% 3.73/1.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 3.73/1.01      inference(demodulation,[status(thm)],[c_3075,c_3063]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_8,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.01      | ~ l1_pre_topc(X1) ),
% 3.73/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_723,plain,
% 3.73/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.73/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.73/1.01      | l1_pre_topc(X1) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_7,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/1.01      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.73/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_724,plain,
% 3.73/1.01      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.73/1.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_2757,plain,
% 3.73/1.01      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X2) = k4_xboole_0(k2_pre_topc(X0,X1),X2)
% 3.73/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.73/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_723,c_724]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_5752,plain,
% 3.73/1.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)
% 3.73/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_714,c_2757]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_5852,plain,
% 3.73/1.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
% 3.73/1.01      inference(global_propositional_subsumption,
% 3.73/1.01                [status(thm)],
% 3.73/1.01                [c_5752,c_19]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_5856,plain,
% 3.73/1.01      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_3191,c_5852]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_4,plain,
% 3.73/1.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_727,plain,
% 3.73/1.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1012,plain,
% 3.73/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_727,c_725]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_5858,plain,
% 3.73/1.01      ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
% 3.73/1.01      inference(demodulation,[status(thm)],[c_5856,c_1012]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_15,negated_conjecture,
% 3.73/1.01      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 3.73/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_716,plain,
% 3.73/1.01      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.73/1.01      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_5862,plain,
% 3.73/1.01      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.73/1.01      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 3.73/1.01      inference(demodulation,[status(thm)],[c_5858,c_716]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_13,plain,
% 3.73/1.01      ( v2_tops_1(X0,X1)
% 3.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.01      | ~ l1_pre_topc(X1)
% 3.73/1.01      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.73/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1161,plain,
% 3.73/1.01      ( v2_tops_1(X0,sK0)
% 3.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.73/1.01      | ~ l1_pre_topc(sK0)
% 3.73/1.01      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1162,plain,
% 3.73/1.01      ( k1_tops_1(sK0,X0) != k1_xboole_0
% 3.73/1.01      | v2_tops_1(X0,sK0) = iProver_top
% 3.73/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.73/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_1161]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1164,plain,
% 3.73/1.01      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 3.73/1.01      | v2_tops_1(sK1,sK0) = iProver_top
% 3.73/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.73/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_1162]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_9,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.01      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.73/1.01      | ~ l1_pre_topc(X1) ),
% 3.73/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_912,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.73/1.01      | r1_tarski(X0,k2_pre_topc(sK0,X0))
% 3.73/1.01      | ~ l1_pre_topc(sK0) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_913,plain,
% 3.73/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.73/1.01      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top
% 3.73/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_915,plain,
% 3.73/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.73/1.01      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
% 3.73/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_913]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(contradiction,plain,
% 3.73/1.01      ( $false ),
% 3.73/1.01      inference(minisat,
% 3.73/1.01                [status(thm)],
% 3.73/1.01                [c_5862,c_3075,c_1164,c_915,c_20,c_19]) ).
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  ------                               Statistics
% 3.73/1.01  
% 3.73/1.01  ------ Selected
% 3.73/1.01  
% 3.73/1.01  total_time:                             0.196
% 3.73/1.01  
%------------------------------------------------------------------------------
