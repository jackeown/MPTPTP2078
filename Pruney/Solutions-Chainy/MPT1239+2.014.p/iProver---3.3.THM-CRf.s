%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:55 EST 2020

% Result     : Theorem 55.59s
% Output     : CNFRefutation 55.59s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 361 expanded)
%              Number of clauses        :   86 ( 151 expanded)
%              Number of leaves         :   14 (  81 expanded)
%              Depth                    :   20
%              Number of atoms          :  316 (1099 expanded)
%              Number of equality atoms :   76 ( 108 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),sK1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f32,f31,f30])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_787,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_783,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_1065,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_787,c_783])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_793,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2121,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK2),X0) = iProver_top
    | r1_xboole_0(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1065,c_793])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_798,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3025,plain,
    ( r1_xboole_0(X0,k1_tops_1(sK0,sK2)) = iProver_top
    | r1_xboole_0(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2121,c_798])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_791,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_786,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_789,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1589,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_786,c_789])).

cnf(c_1066,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_786,c_783])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_795,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2250,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_795])).

cnf(c_3135,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2250,c_795])).

cnf(c_7285,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_3135])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_836,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_837,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_911,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1273,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_1274,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_919,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1516,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_2368,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_2369,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2368])).

cnf(c_7424,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7285,c_19,c_837,c_1274,c_2369])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_133,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_134,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_133])).

cnf(c_163,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_134])).

cnf(c_785,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_163])).

cnf(c_7433,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_7424,c_785])).

cnf(c_1741,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1589,c_785])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_788,plain,
    ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1817,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1741,c_788])).

cnf(c_182323,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7433,c_1817])).

cnf(c_183649,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top
    | r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_791,c_182323])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_231,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_902,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_985,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_24864,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_24869,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(k4_xboole_0(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24864])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1182,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_34141,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_1182])).

cnf(c_34142,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34141])).

cnf(c_839,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4189,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_40482,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4189])).

cnf(c_40483,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40482])).

cnf(c_2372,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_46750,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2372])).

cnf(c_46751,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k4_xboole_0(sK1,sK2),sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46750])).

cnf(c_184315,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_183649,c_19,c_1274,c_24869,c_34142,c_40483,c_46751])).

cnf(c_184320,plain,
    ( r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3025,c_184315])).

cnf(c_3800,plain,
    ( ~ r1_xboole_0(X0,sK2)
    | r1_xboole_0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_61763,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_3800])).

cnf(c_61764,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) != iProver_top
    | r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61763])).

cnf(c_8995,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_19252,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8995])).

cnf(c_19255,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19252])).

cnf(c_4353,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,sK2)
    | r1_xboole_0(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_11195,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,sK2))
    | r1_xboole_0(X0,sK2)
    | ~ r1_xboole_0(k4_xboole_0(X1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_4353])).

cnf(c_19251,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
    | r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
    | ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_11195])).

cnf(c_19253,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) != iProver_top
    | r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) = iProver_top
    | r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19251])).

cnf(c_7,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5265,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,X0),X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_12750,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_5265])).

cnf(c_12752,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12750])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_184320,c_61764,c_46751,c_40483,c_34142,c_19255,c_19253,c_12752,c_1274,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:53:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 55.59/7.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.59/7.50  
% 55.59/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.59/7.50  
% 55.59/7.50  ------  iProver source info
% 55.59/7.50  
% 55.59/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.59/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.59/7.50  git: non_committed_changes: false
% 55.59/7.50  git: last_make_outside_of_git: false
% 55.59/7.50  
% 55.59/7.50  ------ 
% 55.59/7.50  
% 55.59/7.50  ------ Input Options
% 55.59/7.50  
% 55.59/7.50  --out_options                           all
% 55.59/7.50  --tptp_safe_out                         true
% 55.59/7.50  --problem_path                          ""
% 55.59/7.50  --include_path                          ""
% 55.59/7.50  --clausifier                            res/vclausify_rel
% 55.59/7.50  --clausifier_options                    ""
% 55.59/7.50  --stdin                                 false
% 55.59/7.50  --stats_out                             all
% 55.59/7.50  
% 55.59/7.50  ------ General Options
% 55.59/7.50  
% 55.59/7.50  --fof                                   false
% 55.59/7.50  --time_out_real                         305.
% 55.59/7.50  --time_out_virtual                      -1.
% 55.59/7.50  --symbol_type_check                     false
% 55.59/7.50  --clausify_out                          false
% 55.59/7.50  --sig_cnt_out                           false
% 55.59/7.50  --trig_cnt_out                          false
% 55.59/7.50  --trig_cnt_out_tolerance                1.
% 55.59/7.50  --trig_cnt_out_sk_spl                   false
% 55.59/7.50  --abstr_cl_out                          false
% 55.59/7.50  
% 55.59/7.50  ------ Global Options
% 55.59/7.50  
% 55.59/7.50  --schedule                              default
% 55.59/7.50  --add_important_lit                     false
% 55.59/7.50  --prop_solver_per_cl                    1000
% 55.59/7.50  --min_unsat_core                        false
% 55.59/7.50  --soft_assumptions                      false
% 55.59/7.50  --soft_lemma_size                       3
% 55.59/7.50  --prop_impl_unit_size                   0
% 55.59/7.50  --prop_impl_unit                        []
% 55.59/7.50  --share_sel_clauses                     true
% 55.59/7.50  --reset_solvers                         false
% 55.59/7.50  --bc_imp_inh                            [conj_cone]
% 55.59/7.50  --conj_cone_tolerance                   3.
% 55.59/7.50  --extra_neg_conj                        none
% 55.59/7.50  --large_theory_mode                     true
% 55.59/7.50  --prolific_symb_bound                   200
% 55.59/7.50  --lt_threshold                          2000
% 55.59/7.50  --clause_weak_htbl                      true
% 55.59/7.50  --gc_record_bc_elim                     false
% 55.59/7.50  
% 55.59/7.50  ------ Preprocessing Options
% 55.59/7.50  
% 55.59/7.50  --preprocessing_flag                    true
% 55.59/7.50  --time_out_prep_mult                    0.1
% 55.59/7.50  --splitting_mode                        input
% 55.59/7.50  --splitting_grd                         true
% 55.59/7.50  --splitting_cvd                         false
% 55.59/7.50  --splitting_cvd_svl                     false
% 55.59/7.50  --splitting_nvd                         32
% 55.59/7.50  --sub_typing                            true
% 55.59/7.50  --prep_gs_sim                           true
% 55.59/7.50  --prep_unflatten                        true
% 55.59/7.50  --prep_res_sim                          true
% 55.59/7.50  --prep_upred                            true
% 55.59/7.50  --prep_sem_filter                       exhaustive
% 55.59/7.50  --prep_sem_filter_out                   false
% 55.59/7.50  --pred_elim                             true
% 55.59/7.50  --res_sim_input                         true
% 55.59/7.50  --eq_ax_congr_red                       true
% 55.59/7.50  --pure_diseq_elim                       true
% 55.59/7.50  --brand_transform                       false
% 55.59/7.50  --non_eq_to_eq                          false
% 55.59/7.50  --prep_def_merge                        true
% 55.59/7.50  --prep_def_merge_prop_impl              false
% 55.59/7.50  --prep_def_merge_mbd                    true
% 55.59/7.50  --prep_def_merge_tr_red                 false
% 55.59/7.50  --prep_def_merge_tr_cl                  false
% 55.59/7.50  --smt_preprocessing                     true
% 55.59/7.50  --smt_ac_axioms                         fast
% 55.59/7.50  --preprocessed_out                      false
% 55.59/7.50  --preprocessed_stats                    false
% 55.59/7.50  
% 55.59/7.50  ------ Abstraction refinement Options
% 55.59/7.50  
% 55.59/7.50  --abstr_ref                             []
% 55.59/7.50  --abstr_ref_prep                        false
% 55.59/7.50  --abstr_ref_until_sat                   false
% 55.59/7.50  --abstr_ref_sig_restrict                funpre
% 55.59/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.59/7.50  --abstr_ref_under                       []
% 55.59/7.50  
% 55.59/7.50  ------ SAT Options
% 55.59/7.50  
% 55.59/7.50  --sat_mode                              false
% 55.59/7.50  --sat_fm_restart_options                ""
% 55.59/7.50  --sat_gr_def                            false
% 55.59/7.50  --sat_epr_types                         true
% 55.59/7.50  --sat_non_cyclic_types                  false
% 55.59/7.50  --sat_finite_models                     false
% 55.59/7.50  --sat_fm_lemmas                         false
% 55.59/7.50  --sat_fm_prep                           false
% 55.59/7.50  --sat_fm_uc_incr                        true
% 55.59/7.50  --sat_out_model                         small
% 55.59/7.50  --sat_out_clauses                       false
% 55.59/7.50  
% 55.59/7.50  ------ QBF Options
% 55.59/7.50  
% 55.59/7.50  --qbf_mode                              false
% 55.59/7.50  --qbf_elim_univ                         false
% 55.59/7.50  --qbf_dom_inst                          none
% 55.59/7.50  --qbf_dom_pre_inst                      false
% 55.59/7.50  --qbf_sk_in                             false
% 55.59/7.50  --qbf_pred_elim                         true
% 55.59/7.50  --qbf_split                             512
% 55.59/7.50  
% 55.59/7.50  ------ BMC1 Options
% 55.59/7.50  
% 55.59/7.50  --bmc1_incremental                      false
% 55.59/7.50  --bmc1_axioms                           reachable_all
% 55.59/7.50  --bmc1_min_bound                        0
% 55.59/7.50  --bmc1_max_bound                        -1
% 55.59/7.50  --bmc1_max_bound_default                -1
% 55.59/7.50  --bmc1_symbol_reachability              true
% 55.59/7.50  --bmc1_property_lemmas                  false
% 55.59/7.50  --bmc1_k_induction                      false
% 55.59/7.50  --bmc1_non_equiv_states                 false
% 55.59/7.50  --bmc1_deadlock                         false
% 55.59/7.50  --bmc1_ucm                              false
% 55.59/7.50  --bmc1_add_unsat_core                   none
% 55.59/7.50  --bmc1_unsat_core_children              false
% 55.59/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.59/7.50  --bmc1_out_stat                         full
% 55.59/7.50  --bmc1_ground_init                      false
% 55.59/7.50  --bmc1_pre_inst_next_state              false
% 55.59/7.50  --bmc1_pre_inst_state                   false
% 55.59/7.50  --bmc1_pre_inst_reach_state             false
% 55.59/7.50  --bmc1_out_unsat_core                   false
% 55.59/7.50  --bmc1_aig_witness_out                  false
% 55.59/7.50  --bmc1_verbose                          false
% 55.59/7.50  --bmc1_dump_clauses_tptp                false
% 55.59/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.59/7.50  --bmc1_dump_file                        -
% 55.59/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.59/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.59/7.50  --bmc1_ucm_extend_mode                  1
% 55.59/7.50  --bmc1_ucm_init_mode                    2
% 55.59/7.50  --bmc1_ucm_cone_mode                    none
% 55.59/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.59/7.50  --bmc1_ucm_relax_model                  4
% 55.59/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.59/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.59/7.50  --bmc1_ucm_layered_model                none
% 55.59/7.50  --bmc1_ucm_max_lemma_size               10
% 55.59/7.50  
% 55.59/7.50  ------ AIG Options
% 55.59/7.50  
% 55.59/7.50  --aig_mode                              false
% 55.59/7.50  
% 55.59/7.50  ------ Instantiation Options
% 55.59/7.50  
% 55.59/7.50  --instantiation_flag                    true
% 55.59/7.50  --inst_sos_flag                         true
% 55.59/7.50  --inst_sos_phase                        true
% 55.59/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.59/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.59/7.50  --inst_lit_sel_side                     num_symb
% 55.59/7.50  --inst_solver_per_active                1400
% 55.59/7.50  --inst_solver_calls_frac                1.
% 55.59/7.50  --inst_passive_queue_type               priority_queues
% 55.59/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.59/7.50  --inst_passive_queues_freq              [25;2]
% 55.59/7.50  --inst_dismatching                      true
% 55.59/7.50  --inst_eager_unprocessed_to_passive     true
% 55.59/7.50  --inst_prop_sim_given                   true
% 55.59/7.50  --inst_prop_sim_new                     false
% 55.59/7.50  --inst_subs_new                         false
% 55.59/7.50  --inst_eq_res_simp                      false
% 55.59/7.50  --inst_subs_given                       false
% 55.59/7.50  --inst_orphan_elimination               true
% 55.59/7.50  --inst_learning_loop_flag               true
% 55.59/7.50  --inst_learning_start                   3000
% 55.59/7.50  --inst_learning_factor                  2
% 55.59/7.50  --inst_start_prop_sim_after_learn       3
% 55.59/7.50  --inst_sel_renew                        solver
% 55.59/7.50  --inst_lit_activity_flag                true
% 55.59/7.50  --inst_restr_to_given                   false
% 55.59/7.50  --inst_activity_threshold               500
% 55.59/7.50  --inst_out_proof                        true
% 55.59/7.50  
% 55.59/7.50  ------ Resolution Options
% 55.59/7.50  
% 55.59/7.50  --resolution_flag                       true
% 55.59/7.50  --res_lit_sel                           adaptive
% 55.59/7.50  --res_lit_sel_side                      none
% 55.59/7.50  --res_ordering                          kbo
% 55.59/7.50  --res_to_prop_solver                    active
% 55.59/7.50  --res_prop_simpl_new                    false
% 55.59/7.50  --res_prop_simpl_given                  true
% 55.59/7.50  --res_passive_queue_type                priority_queues
% 55.59/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.59/7.50  --res_passive_queues_freq               [15;5]
% 55.59/7.50  --res_forward_subs                      full
% 55.59/7.50  --res_backward_subs                     full
% 55.59/7.50  --res_forward_subs_resolution           true
% 55.59/7.50  --res_backward_subs_resolution          true
% 55.59/7.50  --res_orphan_elimination                true
% 55.59/7.50  --res_time_limit                        2.
% 55.59/7.50  --res_out_proof                         true
% 55.59/7.50  
% 55.59/7.50  ------ Superposition Options
% 55.59/7.50  
% 55.59/7.50  --superposition_flag                    true
% 55.59/7.50  --sup_passive_queue_type                priority_queues
% 55.59/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.59/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.59/7.50  --demod_completeness_check              fast
% 55.59/7.50  --demod_use_ground                      true
% 55.59/7.50  --sup_to_prop_solver                    passive
% 55.59/7.50  --sup_prop_simpl_new                    true
% 55.59/7.50  --sup_prop_simpl_given                  true
% 55.59/7.50  --sup_fun_splitting                     true
% 55.59/7.50  --sup_smt_interval                      50000
% 55.59/7.50  
% 55.59/7.50  ------ Superposition Simplification Setup
% 55.59/7.50  
% 55.59/7.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.59/7.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.59/7.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.59/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.59/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.59/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.59/7.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.59/7.50  --sup_immed_triv                        [TrivRules]
% 55.59/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.59/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.59/7.50  --sup_immed_bw_main                     []
% 55.59/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.59/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.59/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.59/7.50  --sup_input_bw                          []
% 55.59/7.50  
% 55.59/7.50  ------ Combination Options
% 55.59/7.50  
% 55.59/7.50  --comb_res_mult                         3
% 55.59/7.50  --comb_sup_mult                         2
% 55.59/7.50  --comb_inst_mult                        10
% 55.59/7.50  
% 55.59/7.50  ------ Debug Options
% 55.59/7.50  
% 55.59/7.50  --dbg_backtrace                         false
% 55.59/7.50  --dbg_dump_prop_clauses                 false
% 55.59/7.50  --dbg_dump_prop_clauses_file            -
% 55.59/7.50  --dbg_out_stat                          false
% 55.59/7.50  ------ Parsing...
% 55.59/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.59/7.50  
% 55.59/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 55.59/7.50  
% 55.59/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.59/7.50  
% 55.59/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.59/7.50  ------ Proving...
% 55.59/7.50  ------ Problem Properties 
% 55.59/7.50  
% 55.59/7.50  
% 55.59/7.50  clauses                                 16
% 55.59/7.50  conjectures                             3
% 55.59/7.50  EPR                                     5
% 55.59/7.50  Horn                                    16
% 55.59/7.50  unary                                   6
% 55.59/7.50  binary                                  5
% 55.59/7.50  lits                                    32
% 55.59/7.50  lits eq                                 2
% 55.59/7.50  fd_pure                                 0
% 55.59/7.50  fd_pseudo                               0
% 55.59/7.50  fd_cond                                 0
% 55.59/7.50  fd_pseudo_cond                          1
% 55.59/7.50  AC symbols                              0
% 55.59/7.50  
% 55.59/7.50  ------ Schedule dynamic 5 is on 
% 55.59/7.50  
% 55.59/7.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.59/7.50  
% 55.59/7.50  
% 55.59/7.50  ------ 
% 55.59/7.50  Current options:
% 55.59/7.50  ------ 
% 55.59/7.50  
% 55.59/7.50  ------ Input Options
% 55.59/7.50  
% 55.59/7.50  --out_options                           all
% 55.59/7.50  --tptp_safe_out                         true
% 55.59/7.50  --problem_path                          ""
% 55.59/7.50  --include_path                          ""
% 55.59/7.50  --clausifier                            res/vclausify_rel
% 55.59/7.50  --clausifier_options                    ""
% 55.59/7.50  --stdin                                 false
% 55.59/7.50  --stats_out                             all
% 55.59/7.50  
% 55.59/7.50  ------ General Options
% 55.59/7.50  
% 55.59/7.50  --fof                                   false
% 55.59/7.50  --time_out_real                         305.
% 55.59/7.50  --time_out_virtual                      -1.
% 55.59/7.50  --symbol_type_check                     false
% 55.59/7.50  --clausify_out                          false
% 55.59/7.50  --sig_cnt_out                           false
% 55.59/7.50  --trig_cnt_out                          false
% 55.59/7.50  --trig_cnt_out_tolerance                1.
% 55.59/7.50  --trig_cnt_out_sk_spl                   false
% 55.59/7.50  --abstr_cl_out                          false
% 55.59/7.50  
% 55.59/7.50  ------ Global Options
% 55.59/7.50  
% 55.59/7.50  --schedule                              default
% 55.59/7.50  --add_important_lit                     false
% 55.59/7.50  --prop_solver_per_cl                    1000
% 55.59/7.50  --min_unsat_core                        false
% 55.59/7.50  --soft_assumptions                      false
% 55.59/7.50  --soft_lemma_size                       3
% 55.59/7.50  --prop_impl_unit_size                   0
% 55.59/7.50  --prop_impl_unit                        []
% 55.59/7.50  --share_sel_clauses                     true
% 55.59/7.50  --reset_solvers                         false
% 55.59/7.50  --bc_imp_inh                            [conj_cone]
% 55.59/7.50  --conj_cone_tolerance                   3.
% 55.59/7.50  --extra_neg_conj                        none
% 55.59/7.50  --large_theory_mode                     true
% 55.59/7.50  --prolific_symb_bound                   200
% 55.59/7.50  --lt_threshold                          2000
% 55.59/7.50  --clause_weak_htbl                      true
% 55.59/7.50  --gc_record_bc_elim                     false
% 55.59/7.50  
% 55.59/7.50  ------ Preprocessing Options
% 55.59/7.50  
% 55.59/7.50  --preprocessing_flag                    true
% 55.59/7.50  --time_out_prep_mult                    0.1
% 55.59/7.50  --splitting_mode                        input
% 55.59/7.50  --splitting_grd                         true
% 55.59/7.50  --splitting_cvd                         false
% 55.59/7.50  --splitting_cvd_svl                     false
% 55.59/7.50  --splitting_nvd                         32
% 55.59/7.50  --sub_typing                            true
% 55.59/7.50  --prep_gs_sim                           true
% 55.59/7.50  --prep_unflatten                        true
% 55.59/7.50  --prep_res_sim                          true
% 55.59/7.50  --prep_upred                            true
% 55.59/7.50  --prep_sem_filter                       exhaustive
% 55.59/7.50  --prep_sem_filter_out                   false
% 55.59/7.50  --pred_elim                             true
% 55.59/7.50  --res_sim_input                         true
% 55.59/7.50  --eq_ax_congr_red                       true
% 55.59/7.50  --pure_diseq_elim                       true
% 55.59/7.50  --brand_transform                       false
% 55.59/7.50  --non_eq_to_eq                          false
% 55.59/7.50  --prep_def_merge                        true
% 55.59/7.50  --prep_def_merge_prop_impl              false
% 55.59/7.50  --prep_def_merge_mbd                    true
% 55.59/7.50  --prep_def_merge_tr_red                 false
% 55.59/7.50  --prep_def_merge_tr_cl                  false
% 55.59/7.50  --smt_preprocessing                     true
% 55.59/7.50  --smt_ac_axioms                         fast
% 55.59/7.50  --preprocessed_out                      false
% 55.59/7.50  --preprocessed_stats                    false
% 55.59/7.50  
% 55.59/7.50  ------ Abstraction refinement Options
% 55.59/7.50  
% 55.59/7.50  --abstr_ref                             []
% 55.59/7.50  --abstr_ref_prep                        false
% 55.59/7.50  --abstr_ref_until_sat                   false
% 55.59/7.50  --abstr_ref_sig_restrict                funpre
% 55.59/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.59/7.50  --abstr_ref_under                       []
% 55.59/7.50  
% 55.59/7.50  ------ SAT Options
% 55.59/7.50  
% 55.59/7.50  --sat_mode                              false
% 55.59/7.50  --sat_fm_restart_options                ""
% 55.59/7.50  --sat_gr_def                            false
% 55.59/7.50  --sat_epr_types                         true
% 55.59/7.50  --sat_non_cyclic_types                  false
% 55.59/7.50  --sat_finite_models                     false
% 55.59/7.50  --sat_fm_lemmas                         false
% 55.59/7.50  --sat_fm_prep                           false
% 55.59/7.50  --sat_fm_uc_incr                        true
% 55.59/7.50  --sat_out_model                         small
% 55.59/7.50  --sat_out_clauses                       false
% 55.59/7.50  
% 55.59/7.50  ------ QBF Options
% 55.59/7.50  
% 55.59/7.50  --qbf_mode                              false
% 55.59/7.50  --qbf_elim_univ                         false
% 55.59/7.50  --qbf_dom_inst                          none
% 55.59/7.50  --qbf_dom_pre_inst                      false
% 55.59/7.50  --qbf_sk_in                             false
% 55.59/7.50  --qbf_pred_elim                         true
% 55.59/7.50  --qbf_split                             512
% 55.59/7.50  
% 55.59/7.50  ------ BMC1 Options
% 55.59/7.50  
% 55.59/7.50  --bmc1_incremental                      false
% 55.59/7.50  --bmc1_axioms                           reachable_all
% 55.59/7.50  --bmc1_min_bound                        0
% 55.59/7.50  --bmc1_max_bound                        -1
% 55.59/7.50  --bmc1_max_bound_default                -1
% 55.59/7.50  --bmc1_symbol_reachability              true
% 55.59/7.50  --bmc1_property_lemmas                  false
% 55.59/7.50  --bmc1_k_induction                      false
% 55.59/7.50  --bmc1_non_equiv_states                 false
% 55.59/7.50  --bmc1_deadlock                         false
% 55.59/7.50  --bmc1_ucm                              false
% 55.59/7.50  --bmc1_add_unsat_core                   none
% 55.59/7.50  --bmc1_unsat_core_children              false
% 55.59/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.59/7.50  --bmc1_out_stat                         full
% 55.59/7.50  --bmc1_ground_init                      false
% 55.59/7.50  --bmc1_pre_inst_next_state              false
% 55.59/7.50  --bmc1_pre_inst_state                   false
% 55.59/7.50  --bmc1_pre_inst_reach_state             false
% 55.59/7.50  --bmc1_out_unsat_core                   false
% 55.59/7.50  --bmc1_aig_witness_out                  false
% 55.59/7.50  --bmc1_verbose                          false
% 55.59/7.50  --bmc1_dump_clauses_tptp                false
% 55.59/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.59/7.50  --bmc1_dump_file                        -
% 55.59/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.59/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.59/7.50  --bmc1_ucm_extend_mode                  1
% 55.59/7.50  --bmc1_ucm_init_mode                    2
% 55.59/7.50  --bmc1_ucm_cone_mode                    none
% 55.59/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.59/7.50  --bmc1_ucm_relax_model                  4
% 55.59/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.59/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.59/7.50  --bmc1_ucm_layered_model                none
% 55.59/7.50  --bmc1_ucm_max_lemma_size               10
% 55.59/7.50  
% 55.59/7.50  ------ AIG Options
% 55.59/7.50  
% 55.59/7.50  --aig_mode                              false
% 55.59/7.50  
% 55.59/7.50  ------ Instantiation Options
% 55.59/7.50  
% 55.59/7.50  --instantiation_flag                    true
% 55.59/7.50  --inst_sos_flag                         true
% 55.59/7.50  --inst_sos_phase                        true
% 55.59/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.59/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.59/7.50  --inst_lit_sel_side                     none
% 55.59/7.50  --inst_solver_per_active                1400
% 55.59/7.50  --inst_solver_calls_frac                1.
% 55.59/7.50  --inst_passive_queue_type               priority_queues
% 55.59/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.59/7.50  --inst_passive_queues_freq              [25;2]
% 55.59/7.50  --inst_dismatching                      true
% 55.59/7.50  --inst_eager_unprocessed_to_passive     true
% 55.59/7.50  --inst_prop_sim_given                   true
% 55.59/7.50  --inst_prop_sim_new                     false
% 55.59/7.50  --inst_subs_new                         false
% 55.59/7.50  --inst_eq_res_simp                      false
% 55.59/7.50  --inst_subs_given                       false
% 55.59/7.50  --inst_orphan_elimination               true
% 55.59/7.50  --inst_learning_loop_flag               true
% 55.59/7.50  --inst_learning_start                   3000
% 55.59/7.50  --inst_learning_factor                  2
% 55.59/7.50  --inst_start_prop_sim_after_learn       3
% 55.59/7.50  --inst_sel_renew                        solver
% 55.59/7.50  --inst_lit_activity_flag                true
% 55.59/7.50  --inst_restr_to_given                   false
% 55.59/7.50  --inst_activity_threshold               500
% 55.59/7.50  --inst_out_proof                        true
% 55.59/7.50  
% 55.59/7.50  ------ Resolution Options
% 55.59/7.50  
% 55.59/7.50  --resolution_flag                       false
% 55.59/7.50  --res_lit_sel                           adaptive
% 55.59/7.50  --res_lit_sel_side                      none
% 55.59/7.50  --res_ordering                          kbo
% 55.59/7.50  --res_to_prop_solver                    active
% 55.59/7.50  --res_prop_simpl_new                    false
% 55.59/7.50  --res_prop_simpl_given                  true
% 55.59/7.50  --res_passive_queue_type                priority_queues
% 55.59/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.59/7.50  --res_passive_queues_freq               [15;5]
% 55.59/7.50  --res_forward_subs                      full
% 55.59/7.50  --res_backward_subs                     full
% 55.59/7.50  --res_forward_subs_resolution           true
% 55.59/7.50  --res_backward_subs_resolution          true
% 55.59/7.50  --res_orphan_elimination                true
% 55.59/7.50  --res_time_limit                        2.
% 55.59/7.50  --res_out_proof                         true
% 55.59/7.50  
% 55.59/7.50  ------ Superposition Options
% 55.59/7.50  
% 55.59/7.50  --superposition_flag                    true
% 55.59/7.50  --sup_passive_queue_type                priority_queues
% 55.59/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.59/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.59/7.50  --demod_completeness_check              fast
% 55.59/7.50  --demod_use_ground                      true
% 55.59/7.50  --sup_to_prop_solver                    passive
% 55.59/7.50  --sup_prop_simpl_new                    true
% 55.59/7.50  --sup_prop_simpl_given                  true
% 55.59/7.50  --sup_fun_splitting                     true
% 55.59/7.50  --sup_smt_interval                      50000
% 55.59/7.50  
% 55.59/7.50  ------ Superposition Simplification Setup
% 55.59/7.50  
% 55.59/7.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.59/7.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.59/7.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.59/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.59/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.59/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.59/7.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.59/7.50  --sup_immed_triv                        [TrivRules]
% 55.59/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.59/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.59/7.50  --sup_immed_bw_main                     []
% 55.59/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.59/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.59/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.59/7.50  --sup_input_bw                          []
% 55.59/7.50  
% 55.59/7.50  ------ Combination Options
% 55.59/7.50  
% 55.59/7.50  --comb_res_mult                         3
% 55.59/7.50  --comb_sup_mult                         2
% 55.59/7.50  --comb_inst_mult                        10
% 55.59/7.50  
% 55.59/7.50  ------ Debug Options
% 55.59/7.50  
% 55.59/7.50  --dbg_backtrace                         false
% 55.59/7.50  --dbg_dump_prop_clauses                 false
% 55.59/7.50  --dbg_dump_prop_clauses_file            -
% 55.59/7.50  --dbg_out_stat                          false
% 55.59/7.50  
% 55.59/7.50  
% 55.59/7.50  
% 55.59/7.50  
% 55.59/7.50  ------ Proving...
% 55.59/7.50  
% 55.59/7.50  
% 55.59/7.50  % SZS status Theorem for theBenchmark.p
% 55.59/7.50  
% 55.59/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.59/7.50  
% 55.59/7.50  fof(f12,conjecture,(
% 55.59/7.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 55.59/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.59/7.50  
% 55.59/7.50  fof(f13,negated_conjecture,(
% 55.59/7.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 55.59/7.50    inference(negated_conjecture,[],[f12])).
% 55.59/7.50  
% 55.59/7.50  fof(f14,plain,(
% 55.59/7.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 55.59/7.50    inference(pure_predicate_removal,[],[f13])).
% 55.59/7.50  
% 55.59/7.50  fof(f26,plain,(
% 55.59/7.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 55.59/7.50    inference(ennf_transformation,[],[f14])).
% 55.59/7.50  
% 55.59/7.50  fof(f32,plain,(
% 55.59/7.50    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 55.59/7.50    introduced(choice_axiom,[])).
% 55.59/7.50  
% 55.59/7.50  fof(f31,plain,(
% 55.59/7.50    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),sK1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 55.59/7.50    introduced(choice_axiom,[])).
% 55.59/7.50  
% 55.59/7.50  fof(f30,plain,(
% 55.59/7.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 55.59/7.50    introduced(choice_axiom,[])).
% 55.59/7.50  
% 55.59/7.50  fof(f33,plain,(
% 55.59/7.50    ((~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 55.59/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f32,f31,f30])).
% 55.59/7.50  
% 55.59/7.50  fof(f50,plain,(
% 55.59/7.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 55.59/7.50    inference(cnf_transformation,[],[f33])).
% 55.59/7.50  
% 55.59/7.50  fof(f10,axiom,(
% 55.59/7.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 55.59/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.59/7.50  
% 55.59/7.50  fof(f23,plain,(
% 55.59/7.50    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.59/7.50    inference(ennf_transformation,[],[f10])).
% 55.59/7.50  
% 55.59/7.50  fof(f46,plain,(
% 55.59/7.50    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.59/7.50    inference(cnf_transformation,[],[f23])).
% 55.59/7.50  
% 55.59/7.50  fof(f48,plain,(
% 55.59/7.50    l1_pre_topc(sK0)),
% 55.59/7.50    inference(cnf_transformation,[],[f33])).
% 55.59/7.50  
% 55.59/7.50  fof(f5,axiom,(
% 55.59/7.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 55.59/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.59/7.50  
% 55.59/7.50  fof(f18,plain,(
% 55.59/7.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 55.59/7.50    inference(ennf_transformation,[],[f5])).
% 55.59/7.50  
% 55.59/7.50  fof(f19,plain,(
% 55.59/7.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 55.59/7.50    inference(flattening,[],[f18])).
% 55.59/7.50  
% 55.59/7.50  fof(f40,plain,(
% 55.59/7.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 55.59/7.50    inference(cnf_transformation,[],[f19])).
% 55.59/7.50  
% 55.59/7.50  fof(f1,axiom,(
% 55.59/7.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 55.59/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.59/7.50  
% 55.59/7.50  fof(f15,plain,(
% 55.59/7.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 55.59/7.50    inference(ennf_transformation,[],[f1])).
% 55.59/7.50  
% 55.59/7.50  fof(f34,plain,(
% 55.59/7.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 55.59/7.50    inference(cnf_transformation,[],[f15])).
% 55.59/7.50  
% 55.59/7.50  fof(f7,axiom,(
% 55.59/7.50    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 55.59/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.59/7.50  
% 55.59/7.50  fof(f20,plain,(
% 55.59/7.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 55.59/7.50    inference(ennf_transformation,[],[f7])).
% 55.59/7.50  
% 55.59/7.50  fof(f21,plain,(
% 55.59/7.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 55.59/7.50    inference(flattening,[],[f20])).
% 55.59/7.50  
% 55.59/7.50  fof(f42,plain,(
% 55.59/7.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 55.59/7.50    inference(cnf_transformation,[],[f21])).
% 55.59/7.50  
% 55.59/7.50  fof(f49,plain,(
% 55.59/7.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 55.59/7.50    inference(cnf_transformation,[],[f33])).
% 55.59/7.50  
% 55.59/7.50  fof(f9,axiom,(
% 55.59/7.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 55.59/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.59/7.50  
% 55.59/7.50  fof(f29,plain,(
% 55.59/7.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 55.59/7.50    inference(nnf_transformation,[],[f9])).
% 55.59/7.50  
% 55.59/7.50  fof(f44,plain,(
% 55.59/7.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 55.59/7.50    inference(cnf_transformation,[],[f29])).
% 55.59/7.50  
% 55.59/7.50  fof(f3,axiom,(
% 55.59/7.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 55.59/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.59/7.50  
% 55.59/7.50  fof(f16,plain,(
% 55.59/7.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 55.59/7.50    inference(ennf_transformation,[],[f3])).
% 55.59/7.50  
% 55.59/7.50  fof(f17,plain,(
% 55.59/7.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 55.59/7.50    inference(flattening,[],[f16])).
% 55.59/7.50  
% 55.59/7.50  fof(f38,plain,(
% 55.59/7.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 55.59/7.50    inference(cnf_transformation,[],[f17])).
% 55.59/7.50  
% 55.59/7.50  fof(f8,axiom,(
% 55.59/7.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 55.59/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.59/7.50  
% 55.59/7.50  fof(f22,plain,(
% 55.59/7.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 55.59/7.50    inference(ennf_transformation,[],[f8])).
% 55.59/7.50  
% 55.59/7.50  fof(f43,plain,(
% 55.59/7.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 55.59/7.50    inference(cnf_transformation,[],[f22])).
% 55.59/7.50  
% 55.59/7.50  fof(f45,plain,(
% 55.59/7.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 55.59/7.50    inference(cnf_transformation,[],[f29])).
% 55.59/7.50  
% 55.59/7.50  fof(f51,plain,(
% 55.59/7.50    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 55.59/7.50    inference(cnf_transformation,[],[f33])).
% 55.59/7.50  
% 55.59/7.50  fof(f11,axiom,(
% 55.59/7.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 55.59/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.59/7.50  
% 55.59/7.50  fof(f24,plain,(
% 55.59/7.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.59/7.50    inference(ennf_transformation,[],[f11])).
% 55.59/7.50  
% 55.59/7.50  fof(f25,plain,(
% 55.59/7.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.59/7.50    inference(flattening,[],[f24])).
% 55.59/7.50  
% 55.59/7.50  fof(f47,plain,(
% 55.59/7.50    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.59/7.50    inference(cnf_transformation,[],[f25])).
% 55.59/7.50  
% 55.59/7.50  fof(f4,axiom,(
% 55.59/7.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 55.59/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.59/7.50  
% 55.59/7.50  fof(f39,plain,(
% 55.59/7.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 55.59/7.50    inference(cnf_transformation,[],[f4])).
% 55.59/7.50  
% 55.59/7.50  fof(f6,axiom,(
% 55.59/7.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 55.59/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.59/7.50  
% 55.59/7.50  fof(f41,plain,(
% 55.59/7.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 55.59/7.50    inference(cnf_transformation,[],[f6])).
% 55.59/7.50  
% 55.59/7.50  cnf(c_15,negated_conjecture,
% 55.59/7.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 55.59/7.50      inference(cnf_transformation,[],[f50]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_787,plain,
% 55.59/7.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_12,plain,
% 55.59/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.59/7.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 55.59/7.50      | ~ l1_pre_topc(X1) ),
% 55.59/7.50      inference(cnf_transformation,[],[f46]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_17,negated_conjecture,
% 55.59/7.50      ( l1_pre_topc(sK0) ),
% 55.59/7.50      inference(cnf_transformation,[],[f48]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_248,plain,
% 55.59/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.59/7.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 55.59/7.50      | sK0 != X1 ),
% 55.59/7.50      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_249,plain,
% 55.59/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 55.59/7.50      inference(unflattening,[status(thm)],[c_248]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_783,plain,
% 55.59/7.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_1065,plain,
% 55.59/7.50      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 55.59/7.50      inference(superposition,[status(thm)],[c_787,c_783]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_6,plain,
% 55.59/7.50      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 55.59/7.50      inference(cnf_transformation,[],[f40]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_793,plain,
% 55.59/7.50      ( r1_tarski(X0,X1) != iProver_top
% 55.59/7.50      | r1_xboole_0(X1,X2) != iProver_top
% 55.59/7.50      | r1_xboole_0(X0,X2) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_2121,plain,
% 55.59/7.50      ( r1_xboole_0(k1_tops_1(sK0,sK2),X0) = iProver_top
% 55.59/7.50      | r1_xboole_0(sK2,X0) != iProver_top ),
% 55.59/7.50      inference(superposition,[status(thm)],[c_1065,c_793]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_0,plain,
% 55.59/7.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 55.59/7.50      inference(cnf_transformation,[],[f34]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_798,plain,
% 55.59/7.50      ( r1_xboole_0(X0,X1) != iProver_top
% 55.59/7.50      | r1_xboole_0(X1,X0) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_3025,plain,
% 55.59/7.50      ( r1_xboole_0(X0,k1_tops_1(sK0,sK2)) = iProver_top
% 55.59/7.50      | r1_xboole_0(sK2,X0) != iProver_top ),
% 55.59/7.50      inference(superposition,[status(thm)],[c_2121,c_798]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_8,plain,
% 55.59/7.50      ( ~ r1_tarski(X0,X1)
% 55.59/7.50      | r1_tarski(X0,k4_xboole_0(X1,X2))
% 55.59/7.50      | ~ r1_xboole_0(X0,X2) ),
% 55.59/7.50      inference(cnf_transformation,[],[f42]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_791,plain,
% 55.59/7.50      ( r1_tarski(X0,X1) != iProver_top
% 55.59/7.50      | r1_tarski(X0,k4_xboole_0(X1,X2)) = iProver_top
% 55.59/7.50      | r1_xboole_0(X0,X2) != iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_16,negated_conjecture,
% 55.59/7.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 55.59/7.50      inference(cnf_transformation,[],[f49]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_786,plain,
% 55.59/7.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_11,plain,
% 55.59/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 55.59/7.50      inference(cnf_transformation,[],[f44]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_789,plain,
% 55.59/7.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 55.59/7.50      | r1_tarski(X0,X1) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_1589,plain,
% 55.59/7.50      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 55.59/7.50      inference(superposition,[status(thm)],[c_786,c_789]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_1066,plain,
% 55.59/7.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 55.59/7.50      inference(superposition,[status(thm)],[c_786,c_783]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_4,plain,
% 55.59/7.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 55.59/7.50      inference(cnf_transformation,[],[f38]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_795,plain,
% 55.59/7.50      ( r1_tarski(X0,X1) != iProver_top
% 55.59/7.50      | r1_tarski(X1,X2) != iProver_top
% 55.59/7.50      | r1_tarski(X0,X2) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_2250,plain,
% 55.59/7.50      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 55.59/7.50      | r1_tarski(sK1,X0) != iProver_top ),
% 55.59/7.50      inference(superposition,[status(thm)],[c_1066,c_795]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_3135,plain,
% 55.59/7.50      ( r1_tarski(X0,X1) != iProver_top
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 55.59/7.50      | r1_tarski(sK1,X0) != iProver_top ),
% 55.59/7.50      inference(superposition,[status(thm)],[c_2250,c_795]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_7285,plain,
% 55.59/7.50      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 55.59/7.50      | r1_tarski(sK1,sK1) != iProver_top ),
% 55.59/7.50      inference(superposition,[status(thm)],[c_1589,c_3135]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_19,plain,
% 55.59/7.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_836,plain,
% 55.59/7.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_249]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_837,plain,
% 55.59/7.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_911,plain,
% 55.59/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_11]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_1273,plain,
% 55.59/7.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_911]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_1274,plain,
% 55.59/7.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.59/7.50      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_919,plain,
% 55.59/7.50      ( ~ r1_tarski(X0,X1)
% 55.59/7.50      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 55.59/7.50      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_4]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_1516,plain,
% 55.59/7.50      ( r1_tarski(X0,u1_struct_0(sK0))
% 55.59/7.50      | ~ r1_tarski(X0,sK1)
% 55.59/7.50      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_919]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_2368,plain,
% 55.59/7.50      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 55.59/7.50      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 55.59/7.50      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_1516]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_2369,plain,
% 55.59/7.50      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 55.59/7.50      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_2368]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_7424,plain,
% 55.59/7.50      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 55.59/7.50      inference(global_propositional_subsumption,
% 55.59/7.50                [status(thm)],
% 55.59/7.50                [c_7285,c_19,c_837,c_1274,c_2369]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_9,plain,
% 55.59/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.59/7.50      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 55.59/7.50      inference(cnf_transformation,[],[f43]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_10,plain,
% 55.59/7.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 55.59/7.50      inference(cnf_transformation,[],[f45]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_133,plain,
% 55.59/7.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 55.59/7.50      inference(prop_impl,[status(thm)],[c_10]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_134,plain,
% 55.59/7.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 55.59/7.50      inference(renaming,[status(thm)],[c_133]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_163,plain,
% 55.59/7.50      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 55.59/7.50      inference(bin_hyper_res,[status(thm)],[c_9,c_134]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_785,plain,
% 55.59/7.50      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 55.59/7.50      | r1_tarski(X1,X0) != iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_163]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_7433,plain,
% 55.59/7.50      ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0) ),
% 55.59/7.50      inference(superposition,[status(thm)],[c_7424,c_785]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_1741,plain,
% 55.59/7.50      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 55.59/7.50      inference(superposition,[status(thm)],[c_1589,c_785]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_14,negated_conjecture,
% 55.59/7.50      ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 55.59/7.50      inference(cnf_transformation,[],[f51]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_788,plain,
% 55.59/7.50      ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_1817,plain,
% 55.59/7.50      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 55.59/7.50      inference(demodulation,[status(thm)],[c_1741,c_788]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_182323,plain,
% 55.59/7.50      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 55.59/7.50      inference(demodulation,[status(thm)],[c_7433,c_1817]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_183649,plain,
% 55.59/7.50      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top
% 55.59/7.50      | r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top ),
% 55.59/7.50      inference(superposition,[status(thm)],[c_791,c_182323]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_13,plain,
% 55.59/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.59/7.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 55.59/7.50      | ~ r1_tarski(X0,X2)
% 55.59/7.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 55.59/7.50      | ~ l1_pre_topc(X1) ),
% 55.59/7.50      inference(cnf_transformation,[],[f47]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_230,plain,
% 55.59/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.59/7.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 55.59/7.50      | ~ r1_tarski(X0,X2)
% 55.59/7.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 55.59/7.50      | sK0 != X1 ),
% 55.59/7.50      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_231,plain,
% 55.59/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | ~ r1_tarski(X1,X0)
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 55.59/7.50      inference(unflattening,[status(thm)],[c_230]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_902,plain,
% 55.59/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | ~ r1_tarski(X0,sK1)
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_231]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_985,plain,
% 55.59/7.50      ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k1_tops_1(sK0,sK1))
% 55.59/7.50      | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_902]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_24864,plain,
% 55.59/7.50      ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
% 55.59/7.50      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_985]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_24869,plain,
% 55.59/7.50      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.59/7.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) = iProver_top
% 55.59/7.50      | r1_tarski(k4_xboole_0(sK1,sK2),sK1) != iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_24864]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_5,plain,
% 55.59/7.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 55.59/7.50      inference(cnf_transformation,[],[f39]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_1182,plain,
% 55.59/7.50      ( r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_5]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_34141,plain,
% 55.59/7.50      ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_1182]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_34142,plain,
% 55.59/7.50      ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_34141]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_839,plain,
% 55.59/7.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_10]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_4189,plain,
% 55.59/7.50      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | ~ r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_839]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_40482,plain,
% 55.59/7.50      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_4189]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_40483,plain,
% 55.59/7.50      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 55.59/7.50      | r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) != iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_40482]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_2372,plain,
% 55.59/7.50      ( r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))
% 55.59/7.50      | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1)
% 55.59/7.50      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_1516]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_46750,plain,
% 55.59/7.50      ( r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
% 55.59/7.50      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
% 55.59/7.50      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_2372]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_46751,plain,
% 55.59/7.50      ( r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) = iProver_top
% 55.59/7.50      | r1_tarski(k4_xboole_0(sK1,sK2),sK1) != iProver_top
% 55.59/7.50      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_46750]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_184315,plain,
% 55.59/7.50      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top ),
% 55.59/7.50      inference(global_propositional_subsumption,
% 55.59/7.50                [status(thm)],
% 55.59/7.50                [c_183649,c_19,c_1274,c_24869,c_34142,c_40483,c_46751]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_184320,plain,
% 55.59/7.50      ( r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) != iProver_top ),
% 55.59/7.50      inference(superposition,[status(thm)],[c_3025,c_184315]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_3800,plain,
% 55.59/7.50      ( ~ r1_xboole_0(X0,sK2) | r1_xboole_0(sK2,X0) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_0]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_61763,plain,
% 55.59/7.50      ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
% 55.59/7.50      | r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_3800]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_61764,plain,
% 55.59/7.50      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) != iProver_top
% 55.59/7.50      | r1_xboole_0(sK2,k1_tops_1(sK0,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_61763]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_8995,plain,
% 55.59/7.50      ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_249]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_19252,plain,
% 55.59/7.50      ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_8995]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_19255,plain,
% 55.59/7.50      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.59/7.50      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_19252]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_4353,plain,
% 55.59/7.50      ( ~ r1_tarski(X0,X1)
% 55.59/7.50      | ~ r1_xboole_0(X1,sK2)
% 55.59/7.50      | r1_xboole_0(X0,sK2) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_6]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_11195,plain,
% 55.59/7.50      ( ~ r1_tarski(X0,k4_xboole_0(X1,sK2))
% 55.59/7.50      | r1_xboole_0(X0,sK2)
% 55.59/7.50      | ~ r1_xboole_0(k4_xboole_0(X1,sK2),sK2) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_4353]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_19251,plain,
% 55.59/7.50      ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
% 55.59/7.50      | r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)
% 55.59/7.50      | ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_11195]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_19253,plain,
% 55.59/7.50      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) != iProver_top
% 55.59/7.50      | r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) = iProver_top
% 55.59/7.50      | r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) != iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_19251]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_7,plain,
% 55.59/7.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 55.59/7.50      inference(cnf_transformation,[],[f41]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_5265,plain,
% 55.59/7.50      ( r1_xboole_0(k4_xboole_0(sK1,X0),X0) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_7]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_12750,plain,
% 55.59/7.50      ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
% 55.59/7.50      inference(instantiation,[status(thm)],[c_5265]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(c_12752,plain,
% 55.59/7.50      ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) = iProver_top ),
% 55.59/7.50      inference(predicate_to_equality,[status(thm)],[c_12750]) ).
% 55.59/7.50  
% 55.59/7.50  cnf(contradiction,plain,
% 55.59/7.50      ( $false ),
% 55.59/7.50      inference(minisat,
% 55.59/7.50                [status(thm)],
% 55.59/7.50                [c_184320,c_61764,c_46751,c_40483,c_34142,c_19255,
% 55.59/7.50                 c_19253,c_12752,c_1274,c_19]) ).
% 55.59/7.50  
% 55.59/7.50  
% 55.59/7.50  % SZS output end CNFRefutation for theBenchmark.p
% 55.59/7.50  
% 55.59/7.50  ------                               Statistics
% 55.59/7.50  
% 55.59/7.50  ------ General
% 55.59/7.50  
% 55.59/7.50  abstr_ref_over_cycles:                  0
% 55.59/7.50  abstr_ref_under_cycles:                 0
% 55.59/7.50  gc_basic_clause_elim:                   0
% 55.59/7.50  forced_gc_time:                         0
% 55.59/7.50  parsing_time:                           0.007
% 55.59/7.50  unif_index_cands_time:                  0.
% 55.59/7.50  unif_index_add_time:                    0.
% 55.59/7.50  orderings_time:                         0.
% 55.59/7.50  out_proof_time:                         0.026
% 55.59/7.50  total_time:                             6.823
% 55.59/7.50  num_of_symbols:                         43
% 55.59/7.50  num_of_terms:                           100117
% 55.59/7.50  
% 55.59/7.50  ------ Preprocessing
% 55.59/7.50  
% 55.59/7.50  num_of_splits:                          0
% 55.59/7.50  num_of_split_atoms:                     0
% 55.59/7.50  num_of_reused_defs:                     0
% 55.59/7.50  num_eq_ax_congr_red:                    9
% 55.59/7.50  num_of_sem_filtered_clauses:            1
% 55.59/7.50  num_of_subtypes:                        0
% 55.59/7.50  monotx_restored_types:                  0
% 55.59/7.50  sat_num_of_epr_types:                   0
% 55.59/7.50  sat_num_of_non_cyclic_types:            0
% 55.59/7.50  sat_guarded_non_collapsed_types:        0
% 55.59/7.50  num_pure_diseq_elim:                    0
% 55.59/7.50  simp_replaced_by:                       0
% 55.59/7.50  res_preprocessed:                       84
% 55.59/7.50  prep_upred:                             0
% 55.59/7.50  prep_unflattend:                        2
% 55.59/7.50  smt_new_axioms:                         0
% 55.59/7.50  pred_elim_cands:                        3
% 55.59/7.50  pred_elim:                              1
% 55.59/7.50  pred_elim_cl:                           1
% 55.59/7.50  pred_elim_cycles:                       3
% 55.59/7.50  merged_defs:                            8
% 55.59/7.50  merged_defs_ncl:                        0
% 55.59/7.50  bin_hyper_res:                          9
% 55.59/7.50  prep_cycles:                            4
% 55.59/7.50  pred_elim_time:                         0.
% 55.59/7.50  splitting_time:                         0.
% 55.59/7.50  sem_filter_time:                        0.
% 55.59/7.50  monotx_time:                            0.001
% 55.59/7.50  subtype_inf_time:                       0.
% 55.59/7.50  
% 55.59/7.50  ------ Problem properties
% 55.59/7.50  
% 55.59/7.50  clauses:                                16
% 55.59/7.50  conjectures:                            3
% 55.59/7.50  epr:                                    5
% 55.59/7.50  horn:                                   16
% 55.59/7.50  ground:                                 3
% 55.59/7.50  unary:                                  6
% 55.59/7.50  binary:                                 5
% 55.59/7.50  lits:                                   32
% 55.59/7.50  lits_eq:                                2
% 55.59/7.50  fd_pure:                                0
% 55.59/7.50  fd_pseudo:                              0
% 55.59/7.50  fd_cond:                                0
% 55.59/7.50  fd_pseudo_cond:                         1
% 55.59/7.50  ac_symbols:                             0
% 55.59/7.50  
% 55.59/7.50  ------ Propositional Solver
% 55.59/7.50  
% 55.59/7.50  prop_solver_calls:                      96
% 55.59/7.50  prop_fast_solver_calls:                 5318
% 55.59/7.50  smt_solver_calls:                       0
% 55.59/7.50  smt_fast_solver_calls:                  0
% 55.59/7.50  prop_num_of_clauses:                    95656
% 55.59/7.50  prop_preprocess_simplified:             113834
% 55.59/7.50  prop_fo_subsumed:                       348
% 55.59/7.50  prop_solver_time:                       0.
% 55.59/7.50  smt_solver_time:                        0.
% 55.59/7.50  smt_fast_solver_time:                   0.
% 55.59/7.50  prop_fast_solver_time:                  0.
% 55.59/7.50  prop_unsat_core_time:                   0.008
% 55.59/7.50  
% 55.59/7.50  ------ QBF
% 55.59/7.50  
% 55.59/7.50  qbf_q_res:                              0
% 55.59/7.50  qbf_num_tautologies:                    0
% 55.59/7.50  qbf_prep_cycles:                        0
% 55.59/7.50  
% 55.59/7.50  ------ BMC1
% 55.59/7.50  
% 55.59/7.50  bmc1_current_bound:                     -1
% 55.59/7.50  bmc1_last_solved_bound:                 -1
% 55.59/7.50  bmc1_unsat_core_size:                   -1
% 55.59/7.50  bmc1_unsat_core_parents_size:           -1
% 55.59/7.50  bmc1_merge_next_fun:                    0
% 55.59/7.50  bmc1_unsat_core_clauses_time:           0.
% 55.59/7.50  
% 55.59/7.50  ------ Instantiation
% 55.59/7.50  
% 55.59/7.50  inst_num_of_clauses:                    7415
% 55.59/7.50  inst_num_in_passive:                    2225
% 55.59/7.50  inst_num_in_active:                     5775
% 55.59/7.50  inst_num_in_unprocessed:                2263
% 55.59/7.50  inst_num_of_loops:                      5999
% 55.59/7.50  inst_num_of_learning_restarts:          1
% 55.59/7.50  inst_num_moves_active_passive:          221
% 55.59/7.50  inst_lit_activity:                      0
% 55.59/7.50  inst_lit_activity_moves:                2
% 55.59/7.50  inst_num_tautologies:                   0
% 55.59/7.50  inst_num_prop_implied:                  0
% 55.59/7.50  inst_num_existing_simplified:           0
% 55.59/7.50  inst_num_eq_res_simplified:             0
% 55.59/7.50  inst_num_child_elim:                    0
% 55.59/7.50  inst_num_of_dismatching_blockings:      13277
% 55.59/7.50  inst_num_of_non_proper_insts:           21717
% 55.59/7.50  inst_num_of_duplicates:                 0
% 55.59/7.50  inst_inst_num_from_inst_to_res:         0
% 55.59/7.50  inst_dismatching_checking_time:         0.
% 55.59/7.50  
% 55.59/7.50  ------ Resolution
% 55.59/7.50  
% 55.59/7.50  res_num_of_clauses:                     25
% 55.59/7.50  res_num_in_passive:                     25
% 55.59/7.50  res_num_in_active:                      0
% 55.59/7.50  res_num_of_loops:                       88
% 55.59/7.50  res_forward_subset_subsumed:            874
% 55.59/7.50  res_backward_subset_subsumed:           10
% 55.59/7.50  res_forward_subsumed:                   0
% 55.59/7.50  res_backward_subsumed:                  0
% 55.59/7.50  res_forward_subsumption_resolution:     0
% 55.59/7.50  res_backward_subsumption_resolution:    0
% 55.59/7.50  res_clause_to_clause_subsumption:       311477
% 55.59/7.50  res_orphan_elimination:                 0
% 55.59/7.50  res_tautology_del:                      2738
% 55.59/7.50  res_num_eq_res_simplified:              0
% 55.59/7.50  res_num_sel_changes:                    0
% 55.59/7.50  res_moves_from_active_to_pass:          0
% 55.59/7.50  
% 55.59/7.50  ------ Superposition
% 55.59/7.50  
% 55.59/7.50  sup_time_total:                         0.
% 55.59/7.50  sup_time_generating:                    0.
% 55.59/7.50  sup_time_sim_full:                      0.
% 55.59/7.50  sup_time_sim_immed:                     0.
% 55.59/7.50  
% 55.59/7.50  sup_num_of_clauses:                     15717
% 55.59/7.50  sup_num_in_active:                      1149
% 55.59/7.50  sup_num_in_passive:                     14568
% 55.59/7.50  sup_num_of_loops:                       1198
% 55.59/7.50  sup_fw_superposition:                   19400
% 55.59/7.50  sup_bw_superposition:                   10273
% 55.59/7.50  sup_immediate_simplified:               10799
% 55.59/7.50  sup_given_eliminated:                   5
% 55.59/7.50  comparisons_done:                       0
% 55.59/7.50  comparisons_avoided:                    0
% 55.59/7.50  
% 55.59/7.50  ------ Simplifications
% 55.59/7.50  
% 55.59/7.50  
% 55.59/7.50  sim_fw_subset_subsumed:                 3918
% 55.59/7.50  sim_bw_subset_subsumed:                 366
% 55.59/7.50  sim_fw_subsumed:                        4717
% 55.59/7.50  sim_bw_subsumed:                        1456
% 55.59/7.50  sim_fw_subsumption_res:                 0
% 55.59/7.50  sim_bw_subsumption_res:                 0
% 55.59/7.50  sim_tautology_del:                      143
% 55.59/7.50  sim_eq_tautology_del:                   212
% 55.59/7.50  sim_eq_res_simp:                        0
% 55.59/7.50  sim_fw_demodulated:                     1026
% 55.59/7.50  sim_bw_demodulated:                     2
% 55.59/7.50  sim_light_normalised:                   228
% 55.59/7.50  sim_joinable_taut:                      0
% 55.59/7.50  sim_joinable_simp:                      0
% 55.59/7.50  sim_ac_normalised:                      0
% 55.59/7.50  sim_smt_subsumption:                    0
% 55.59/7.50  
%------------------------------------------------------------------------------
