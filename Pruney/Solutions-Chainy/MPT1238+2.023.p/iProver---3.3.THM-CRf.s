%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:50 EST 2020

% Result     : Theorem 35.25s
% Output     : CNFRefutation 35.25s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 488 expanded)
%              Number of clauses        :   70 ( 184 expanded)
%              Number of leaves         :   12 ( 118 expanded)
%              Depth                    :   17
%              Number of atoms          :  281 (1489 expanded)
%              Number of equality atoms :  129 ( 334 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f27,f26,f25])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_419,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_412,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_416,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_413,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_417,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1630,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X2)) = k2_xboole_0(X1,k1_tops_1(X0,X2))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_416,c_417])).

cnf(c_7203,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0,k1_tops_1(sK0,sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_1630])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7863,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0,k1_tops_1(sK0,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7203,c_14])).

cnf(c_7864,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0,k1_tops_1(sK0,sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7863])).

cnf(c_7872,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_416,c_7864])).

cnf(c_110802,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7872,c_14])).

cnf(c_110803,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_110802])).

cnf(c_110813,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_412,c_110803])).

cnf(c_1631,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_417])).

cnf(c_1732,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_412,c_1631])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_414,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1970,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1732,c_414])).

cnf(c_110876,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_110813,c_1970])).

cnf(c_117438,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_419,c_110876])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_418,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1972,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_418])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3906,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1972,c_15,c_16])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_415,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_420,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_423,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1005,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_420,c_423])).

cnf(c_3121,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_419,c_1005])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_37,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3419,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3121,c_37])).

cnf(c_3429,plain,
    ( k2_xboole_0(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_3419])).

cnf(c_26848,plain,
    ( k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_412,c_3429])).

cnf(c_27553,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26848,c_14])).

cnf(c_27554,plain,
    ( k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_27553])).

cnf(c_27566,plain,
    ( k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3906,c_27554])).

cnf(c_27982,plain,
    ( k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27566,c_420])).

cnf(c_422,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_421,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3428,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = X0
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_419,c_3419])).

cnf(c_7785,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(X0,X1)
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X3,k2_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_3428])).

cnf(c_47799,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X1)
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_420,c_7785])).

cnf(c_48006,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_422,c_47799])).

cnf(c_48168,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_48006,c_421])).

cnf(c_49603,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_420,c_48168])).

cnf(c_49713,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_27982,c_49603])).

cnf(c_26847,plain,
    ( k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_3429])).

cnf(c_27394,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26847,c_14])).

cnf(c_27395,plain,
    ( k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_27394])).

cnf(c_27407,plain,
    ( k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3906,c_27395])).

cnf(c_27744,plain,
    ( k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_27407])).

cnf(c_821,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_824,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_28725,plain,
    ( k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27744,c_824])).

cnf(c_49709,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_28725,c_49603])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_117438,c_49713,c_49709])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.25/5.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.25/5.00  
% 35.25/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.25/5.00  
% 35.25/5.00  ------  iProver source info
% 35.25/5.00  
% 35.25/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.25/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.25/5.00  git: non_committed_changes: false
% 35.25/5.00  git: last_make_outside_of_git: false
% 35.25/5.00  
% 35.25/5.00  ------ 
% 35.25/5.00  ------ Parsing...
% 35.25/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.25/5.00  
% 35.25/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 35.25/5.00  
% 35.25/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.25/5.00  
% 35.25/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.25/5.00  ------ Proving...
% 35.25/5.00  ------ Problem Properties 
% 35.25/5.00  
% 35.25/5.00  
% 35.25/5.00  clauses                                 13
% 35.25/5.00  conjectures                             4
% 35.25/5.00  EPR                                     3
% 35.25/5.00  Horn                                    13
% 35.25/5.00  unary                                   6
% 35.25/5.00  binary                                  1
% 35.25/5.00  lits                                    28
% 35.25/5.00  lits eq                                 2
% 35.25/5.00  fd_pure                                 0
% 35.25/5.00  fd_pseudo                               0
% 35.25/5.00  fd_cond                                 0
% 35.25/5.00  fd_pseudo_cond                          1
% 35.25/5.00  AC symbols                              0
% 35.25/5.00  
% 35.25/5.00  ------ Input Options Time Limit: Unbounded
% 35.25/5.00  
% 35.25/5.00  
% 35.25/5.00  ------ 
% 35.25/5.00  Current options:
% 35.25/5.00  ------ 
% 35.25/5.00  
% 35.25/5.00  
% 35.25/5.00  
% 35.25/5.00  
% 35.25/5.00  ------ Proving...
% 35.25/5.00  
% 35.25/5.00  
% 35.25/5.00  % SZS status Theorem for theBenchmark.p
% 35.25/5.00  
% 35.25/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.25/5.00  
% 35.25/5.00  fof(f4,axiom,(
% 35.25/5.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f12,plain,(
% 35.25/5.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 35.25/5.00    inference(ennf_transformation,[],[f4])).
% 35.25/5.00  
% 35.25/5.00  fof(f13,plain,(
% 35.25/5.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 35.25/5.00    inference(flattening,[],[f12])).
% 35.25/5.00  
% 35.25/5.00  fof(f34,plain,(
% 35.25/5.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.25/5.00    inference(cnf_transformation,[],[f13])).
% 35.25/5.00  
% 35.25/5.00  fof(f9,conjecture,(
% 35.25/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f10,negated_conjecture,(
% 35.25/5.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 35.25/5.00    inference(negated_conjecture,[],[f9])).
% 35.25/5.00  
% 35.25/5.00  fof(f22,plain,(
% 35.25/5.00    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 35.25/5.00    inference(ennf_transformation,[],[f10])).
% 35.25/5.00  
% 35.25/5.00  fof(f27,plain,(
% 35.25/5.00    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.25/5.00    introduced(choice_axiom,[])).
% 35.25/5.00  
% 35.25/5.00  fof(f26,plain,(
% 35.25/5.00    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.25/5.00    introduced(choice_axiom,[])).
% 35.25/5.00  
% 35.25/5.00  fof(f25,plain,(
% 35.25/5.00    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 35.25/5.00    introduced(choice_axiom,[])).
% 35.25/5.00  
% 35.25/5.00  fof(f28,plain,(
% 35.25/5.00    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 35.25/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f27,f26,f25])).
% 35.25/5.00  
% 35.25/5.00  fof(f40,plain,(
% 35.25/5.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 35.25/5.00    inference(cnf_transformation,[],[f28])).
% 35.25/5.00  
% 35.25/5.00  fof(f7,axiom,(
% 35.25/5.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f18,plain,(
% 35.25/5.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 35.25/5.00    inference(ennf_transformation,[],[f7])).
% 35.25/5.00  
% 35.25/5.00  fof(f19,plain,(
% 35.25/5.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 35.25/5.00    inference(flattening,[],[f18])).
% 35.25/5.00  
% 35.25/5.00  fof(f37,plain,(
% 35.25/5.00    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.25/5.00    inference(cnf_transformation,[],[f19])).
% 35.25/5.00  
% 35.25/5.00  fof(f41,plain,(
% 35.25/5.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 35.25/5.00    inference(cnf_transformation,[],[f28])).
% 35.25/5.00  
% 35.25/5.00  fof(f6,axiom,(
% 35.25/5.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f16,plain,(
% 35.25/5.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 35.25/5.00    inference(ennf_transformation,[],[f6])).
% 35.25/5.00  
% 35.25/5.00  fof(f17,plain,(
% 35.25/5.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.25/5.00    inference(flattening,[],[f16])).
% 35.25/5.00  
% 35.25/5.00  fof(f36,plain,(
% 35.25/5.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.25/5.00    inference(cnf_transformation,[],[f17])).
% 35.25/5.00  
% 35.25/5.00  fof(f39,plain,(
% 35.25/5.00    l1_pre_topc(sK0)),
% 35.25/5.00    inference(cnf_transformation,[],[f28])).
% 35.25/5.00  
% 35.25/5.00  fof(f42,plain,(
% 35.25/5.00    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 35.25/5.00    inference(cnf_transformation,[],[f28])).
% 35.25/5.00  
% 35.25/5.00  fof(f5,axiom,(
% 35.25/5.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f14,plain,(
% 35.25/5.00    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 35.25/5.00    inference(ennf_transformation,[],[f5])).
% 35.25/5.00  
% 35.25/5.00  fof(f15,plain,(
% 35.25/5.00    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.25/5.00    inference(flattening,[],[f14])).
% 35.25/5.00  
% 35.25/5.00  fof(f35,plain,(
% 35.25/5.00    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.25/5.00    inference(cnf_transformation,[],[f15])).
% 35.25/5.00  
% 35.25/5.00  fof(f8,axiom,(
% 35.25/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f20,plain,(
% 35.25/5.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.25/5.00    inference(ennf_transformation,[],[f8])).
% 35.25/5.00  
% 35.25/5.00  fof(f21,plain,(
% 35.25/5.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.25/5.00    inference(flattening,[],[f20])).
% 35.25/5.00  
% 35.25/5.00  fof(f38,plain,(
% 35.25/5.00    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.25/5.00    inference(cnf_transformation,[],[f21])).
% 35.25/5.00  
% 35.25/5.00  fof(f3,axiom,(
% 35.25/5.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f33,plain,(
% 35.25/5.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 35.25/5.00    inference(cnf_transformation,[],[f3])).
% 35.25/5.00  
% 35.25/5.00  fof(f1,axiom,(
% 35.25/5.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f23,plain,(
% 35.25/5.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.25/5.00    inference(nnf_transformation,[],[f1])).
% 35.25/5.00  
% 35.25/5.00  fof(f24,plain,(
% 35.25/5.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.25/5.00    inference(flattening,[],[f23])).
% 35.25/5.00  
% 35.25/5.00  fof(f31,plain,(
% 35.25/5.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.25/5.00    inference(cnf_transformation,[],[f24])).
% 35.25/5.00  
% 35.25/5.00  fof(f29,plain,(
% 35.25/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.25/5.00    inference(cnf_transformation,[],[f24])).
% 35.25/5.00  
% 35.25/5.00  fof(f44,plain,(
% 35.25/5.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.25/5.00    inference(equality_resolution,[],[f29])).
% 35.25/5.00  
% 35.25/5.00  fof(f2,axiom,(
% 35.25/5.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 35.25/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.25/5.00  
% 35.25/5.00  fof(f11,plain,(
% 35.25/5.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 35.25/5.00    inference(ennf_transformation,[],[f2])).
% 35.25/5.00  
% 35.25/5.00  fof(f32,plain,(
% 35.25/5.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 35.25/5.00    inference(cnf_transformation,[],[f11])).
% 35.25/5.00  
% 35.25/5.00  cnf(c_5,plain,
% 35.25/5.00      ( ~ r1_tarski(X0,X1)
% 35.25/5.00      | ~ r1_tarski(X2,X1)
% 35.25/5.00      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 35.25/5.00      inference(cnf_transformation,[],[f34]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_419,plain,
% 35.25/5.00      ( r1_tarski(X0,X1) != iProver_top
% 35.25/5.00      | r1_tarski(X2,X1) != iProver_top
% 35.25/5.00      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_12,negated_conjecture,
% 35.25/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.25/5.00      inference(cnf_transformation,[],[f40]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_412,plain,
% 35.25/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_8,plain,
% 35.25/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.25/5.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 35.25/5.00      | ~ l1_pre_topc(X1) ),
% 35.25/5.00      inference(cnf_transformation,[],[f37]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_416,plain,
% 35.25/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.25/5.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 35.25/5.00      | l1_pre_topc(X1) != iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_11,negated_conjecture,
% 35.25/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.25/5.00      inference(cnf_transformation,[],[f41]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_413,plain,
% 35.25/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_7,plain,
% 35.25/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.25/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.25/5.00      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 35.25/5.00      inference(cnf_transformation,[],[f36]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_417,plain,
% 35.25/5.00      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 35.25/5.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 35.25/5.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1630,plain,
% 35.25/5.00      ( k4_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X2)) = k2_xboole_0(X1,k1_tops_1(X0,X2))
% 35.25/5.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.25/5.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.25/5.00      | l1_pre_topc(X0) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_416,c_417]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_7203,plain,
% 35.25/5.00      ( k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0,k1_tops_1(sK0,sK2))
% 35.25/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.25/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_413,c_1630]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_13,negated_conjecture,
% 35.25/5.00      ( l1_pre_topc(sK0) ),
% 35.25/5.00      inference(cnf_transformation,[],[f39]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_14,plain,
% 35.25/5.00      ( l1_pre_topc(sK0) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_7863,plain,
% 35.25/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.25/5.00      | k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0,k1_tops_1(sK0,sK2)) ),
% 35.25/5.00      inference(global_propositional_subsumption,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_7203,c_14]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_7864,plain,
% 35.25/5.00      ( k4_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0,k1_tops_1(sK0,sK2))
% 35.25/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 35.25/5.00      inference(renaming,[status(thm)],[c_7863]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_7872,plain,
% 35.25/5.00      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2))
% 35.25/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.25/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_416,c_7864]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_110802,plain,
% 35.25/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.25/5.00      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) ),
% 35.25/5.00      inference(global_propositional_subsumption,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_7872,c_14]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_110803,plain,
% 35.25/5.00      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2))
% 35.25/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 35.25/5.00      inference(renaming,[status(thm)],[c_110802]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_110813,plain,
% 35.25/5.00      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_412,c_110803]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1631,plain,
% 35.25/5.00      ( k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)
% 35.25/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_413,c_417]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1732,plain,
% 35.25/5.00      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_412,c_1631]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_10,negated_conjecture,
% 35.25/5.00      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 35.25/5.00      inference(cnf_transformation,[],[f42]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_414,plain,
% 35.25/5.00      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1970,plain,
% 35.25/5.00      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_1732,c_414]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_110876,plain,
% 35.25/5.00      ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
% 35.25/5.00      inference(demodulation,[status(thm)],[c_110813,c_1970]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_117438,plain,
% 35.25/5.00      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top
% 35.25/5.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_419,c_110876]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_6,plain,
% 35.25/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.25/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.25/5.00      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 35.25/5.00      inference(cnf_transformation,[],[f35]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_418,plain,
% 35.25/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.25/5.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 35.25/5.00      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1972,plain,
% 35.25/5.00      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 35.25/5.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.25/5.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_1732,c_418]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_15,plain,
% 35.25/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_16,plain,
% 35.25/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_3906,plain,
% 35.25/5.00      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.25/5.00      inference(global_propositional_subsumption,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_1972,c_15,c_16]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_9,plain,
% 35.25/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.25/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 35.25/5.00      | ~ r1_tarski(X0,X2)
% 35.25/5.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 35.25/5.00      | ~ l1_pre_topc(X1) ),
% 35.25/5.00      inference(cnf_transformation,[],[f38]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_415,plain,
% 35.25/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.25/5.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.25/5.00      | r1_tarski(X0,X2) != iProver_top
% 35.25/5.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
% 35.25/5.00      | l1_pre_topc(X1) != iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_4,plain,
% 35.25/5.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 35.25/5.00      inference(cnf_transformation,[],[f33]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_420,plain,
% 35.25/5.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_0,plain,
% 35.25/5.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 35.25/5.00      inference(cnf_transformation,[],[f31]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_423,plain,
% 35.25/5.00      ( X0 = X1
% 35.25/5.00      | r1_tarski(X0,X1) != iProver_top
% 35.25/5.00      | r1_tarski(X1,X0) != iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_1005,plain,
% 35.25/5.00      ( k2_xboole_0(X0,X1) = X0
% 35.25/5.00      | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_420,c_423]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_3121,plain,
% 35.25/5.00      ( k2_xboole_0(X0,X1) = X0
% 35.25/5.00      | r1_tarski(X0,X0) != iProver_top
% 35.25/5.00      | r1_tarski(X1,X0) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_419,c_1005]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_2,plain,
% 35.25/5.00      ( r1_tarski(X0,X0) ),
% 35.25/5.00      inference(cnf_transformation,[],[f44]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_37,plain,
% 35.25/5.00      ( r1_tarski(X0,X0) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_3419,plain,
% 35.25/5.00      ( k2_xboole_0(X0,X1) = X0 | r1_tarski(X1,X0) != iProver_top ),
% 35.25/5.00      inference(global_propositional_subsumption,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_3121,c_37]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_3429,plain,
% 35.25/5.00      ( k2_xboole_0(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,X1)
% 35.25/5.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.25/5.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.25/5.00      | r1_tarski(X2,X1) != iProver_top
% 35.25/5.00      | l1_pre_topc(X0) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_415,c_3419]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26848,plain,
% 35.25/5.00      ( k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,X0)
% 35.25/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.25/5.00      | r1_tarski(sK1,X0) != iProver_top
% 35.25/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_412,c_3429]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_27553,plain,
% 35.25/5.00      ( r1_tarski(sK1,X0) != iProver_top
% 35.25/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.25/5.00      | k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,X0) ),
% 35.25/5.00      inference(global_propositional_subsumption,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_26848,c_14]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_27554,plain,
% 35.25/5.00      ( k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,X0)
% 35.25/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.25/5.00      | r1_tarski(sK1,X0) != iProver_top ),
% 35.25/5.00      inference(renaming,[status(thm)],[c_27553]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_27566,plain,
% 35.25/5.00      ( k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 35.25/5.00      | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_3906,c_27554]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_27982,plain,
% 35.25/5.00      ( k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 35.25/5.00      inference(forward_subsumption_resolution,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_27566,c_420]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_422,plain,
% 35.25/5.00      ( r1_tarski(X0,X0) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_3,plain,
% 35.25/5.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 35.25/5.00      inference(cnf_transformation,[],[f32]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_421,plain,
% 35.25/5.00      ( r1_tarski(X0,X1) != iProver_top
% 35.25/5.00      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_3428,plain,
% 35.25/5.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = X0
% 35.25/5.00      | r1_tarski(X1,X0) != iProver_top
% 35.25/5.00      | r1_tarski(X2,X0) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_419,c_3419]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_7785,plain,
% 35.25/5.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(X0,X1)
% 35.25/5.00      | r1_tarski(X2,X1) != iProver_top
% 35.25/5.00      | r1_tarski(X3,k2_xboole_0(X0,X1)) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_421,c_3428]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_47799,plain,
% 35.25/5.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X1)
% 35.25/5.00      | r1_tarski(X2,X1) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_420,c_7785]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_48006,plain,
% 35.25/5.00      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_422,c_47799]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_48168,plain,
% 35.25/5.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 35.25/5.00      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_48006,c_421]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_49603,plain,
% 35.25/5.00      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_420,c_48168]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_49713,plain,
% 35.25/5.00      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_27982,c_49603]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_26847,plain,
% 35.25/5.00      ( k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,X0)
% 35.25/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.25/5.00      | r1_tarski(sK2,X0) != iProver_top
% 35.25/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_413,c_3429]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_27394,plain,
% 35.25/5.00      ( r1_tarski(sK2,X0) != iProver_top
% 35.25/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.25/5.00      | k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,X0) ),
% 35.25/5.00      inference(global_propositional_subsumption,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_26847,c_14]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_27395,plain,
% 35.25/5.00      ( k2_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,X0)
% 35.25/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.25/5.00      | r1_tarski(sK2,X0) != iProver_top ),
% 35.25/5.00      inference(renaming,[status(thm)],[c_27394]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_27407,plain,
% 35.25/5.00      ( k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 35.25/5.00      | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_3906,c_27395]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_27744,plain,
% 35.25/5.00      ( k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 35.25/5.00      | r1_tarski(sK2,sK2) != iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_421,c_27407]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_821,plain,
% 35.25/5.00      ( r1_tarski(sK2,sK2) ),
% 35.25/5.00      inference(instantiation,[status(thm)],[c_2]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_824,plain,
% 35.25/5.00      ( r1_tarski(sK2,sK2) = iProver_top ),
% 35.25/5.00      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_28725,plain,
% 35.25/5.00      ( k2_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 35.25/5.00      inference(global_propositional_subsumption,
% 35.25/5.00                [status(thm)],
% 35.25/5.00                [c_27744,c_824]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(c_49709,plain,
% 35.25/5.00      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = iProver_top ),
% 35.25/5.00      inference(superposition,[status(thm)],[c_28725,c_49603]) ).
% 35.25/5.00  
% 35.25/5.00  cnf(contradiction,plain,
% 35.25/5.00      ( $false ),
% 35.25/5.00      inference(minisat,[status(thm)],[c_117438,c_49713,c_49709]) ).
% 35.25/5.00  
% 35.25/5.00  
% 35.25/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.25/5.00  
% 35.25/5.00  ------                               Statistics
% 35.25/5.00  
% 35.25/5.00  ------ Selected
% 35.25/5.00  
% 35.25/5.00  total_time:                             4.12
% 35.25/5.00  
%------------------------------------------------------------------------------
