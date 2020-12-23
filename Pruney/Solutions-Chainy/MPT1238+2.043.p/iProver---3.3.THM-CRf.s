%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:53 EST 2020

% Result     : Theorem 35.19s
% Output     : CNFRefutation 35.19s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 390 expanded)
%              Number of clauses        :   90 ( 165 expanded)
%              Number of leaves         :   17 (  98 expanded)
%              Depth                    :   19
%              Number of atoms          :  322 (1130 expanded)
%              Number of equality atoms :  131 ( 209 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f27,f26,f25])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_371,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_125024,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_125057,plain,
    ( ~ r1_tarski(X0,k1_tops_1(X1,X2))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_125024])).

cnf(c_125143,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_125057])).

cnf(c_133555,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_125143])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_697,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_699,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1318,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_699])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_696,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1319,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_696,c_699])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_701,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_705,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1716,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = X2
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_705])).

cnf(c_12923,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,X0),u1_struct_0(sK0)) = u1_struct_0(sK0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_1716])).

cnf(c_15538,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1318,c_12923])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_702,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_15573,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15538,c_702])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_695,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_202])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_700,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12924,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,X0),X1),k1_tops_1(sK0,X2)) = k1_tops_1(sK0,X2)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,k1_tops_1(sK0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_695,c_1716])).

cnf(c_18077,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_696,c_12924])).

cnf(c_18539,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_700,c_18077])).

cnf(c_23889,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_695,c_18539])).

cnf(c_53034,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_23889])).

cnf(c_745,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_746,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_55170,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_53034,c_746])).

cnf(c_55192,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15573,c_55170])).

cnf(c_14840,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_14841,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14840])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9206,plain,
    ( r1_tarski(X0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(k4_xboole_0(X0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_19633,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK1),sK2)
    | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_9206])).

cnf(c_19635,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK2) != iProver_top
    | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19633])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1052,plain,
    ( r1_tarski(k4_xboole_0(sK2,X0),sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_19634,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_19637,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19634])).

cnf(c_56121,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_55192,c_14841,c_19635,c_19637])).

cnf(c_56160,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_56121,c_702])).

cnf(c_56249,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_56160])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_220,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_219])).

cnf(c_694,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_975,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_696,c_694])).

cnf(c_1311,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_975,c_705])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_706,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1802,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_706])).

cnf(c_10632,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),X0) = X0
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_705])).

cnf(c_12081,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1319,c_10632])).

cnf(c_12251,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12081,c_702])).

cnf(c_974,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_694])).

cnf(c_1310,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_974,c_705])).

cnf(c_1801,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1310,c_706])).

cnf(c_9932,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),X0) = X0
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_705])).

cnf(c_11099,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1318,c_9932])).

cnf(c_11205,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11099,c_702])).

cnf(c_375,plain,
    ( X0 != X1
    | X2 != X3
    | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
    theory(equality)).

cnf(c_1285,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_1734,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,sK2))
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_1735,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1734])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_117,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_118,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_117])).

cnf(c_143,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_118])).

cnf(c_289,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_290,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_289])).

cnf(c_314,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_143,c_290])).

cnf(c_693,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_1407,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1318,c_693])).

cnf(c_1707,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1319,c_1407])).

cnf(c_1449,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_1450,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_369,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_384,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_133555,c_56249,c_12251,c_11205,c_1735,c_1707,c_1450,c_384,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 35.19/5.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.19/5.04  
% 35.19/5.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.19/5.04  
% 35.19/5.04  ------  iProver source info
% 35.19/5.04  
% 35.19/5.04  git: date: 2020-06-30 10:37:57 +0100
% 35.19/5.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.19/5.04  git: non_committed_changes: false
% 35.19/5.04  git: last_make_outside_of_git: false
% 35.19/5.04  
% 35.19/5.04  ------ 
% 35.19/5.04  
% 35.19/5.04  ------ Input Options
% 35.19/5.04  
% 35.19/5.04  --out_options                           all
% 35.19/5.04  --tptp_safe_out                         true
% 35.19/5.04  --problem_path                          ""
% 35.19/5.04  --include_path                          ""
% 35.19/5.04  --clausifier                            res/vclausify_rel
% 35.19/5.04  --clausifier_options                    ""
% 35.19/5.04  --stdin                                 false
% 35.19/5.04  --stats_out                             all
% 35.19/5.04  
% 35.19/5.04  ------ General Options
% 35.19/5.04  
% 35.19/5.04  --fof                                   false
% 35.19/5.04  --time_out_real                         305.
% 35.19/5.04  --time_out_virtual                      -1.
% 35.19/5.04  --symbol_type_check                     false
% 35.19/5.04  --clausify_out                          false
% 35.19/5.04  --sig_cnt_out                           false
% 35.19/5.04  --trig_cnt_out                          false
% 35.19/5.04  --trig_cnt_out_tolerance                1.
% 35.19/5.04  --trig_cnt_out_sk_spl                   false
% 35.19/5.04  --abstr_cl_out                          false
% 35.19/5.04  
% 35.19/5.04  ------ Global Options
% 35.19/5.04  
% 35.19/5.04  --schedule                              default
% 35.19/5.04  --add_important_lit                     false
% 35.19/5.04  --prop_solver_per_cl                    1000
% 35.19/5.04  --min_unsat_core                        false
% 35.19/5.04  --soft_assumptions                      false
% 35.19/5.04  --soft_lemma_size                       3
% 35.19/5.04  --prop_impl_unit_size                   0
% 35.19/5.04  --prop_impl_unit                        []
% 35.19/5.04  --share_sel_clauses                     true
% 35.19/5.04  --reset_solvers                         false
% 35.19/5.04  --bc_imp_inh                            [conj_cone]
% 35.19/5.04  --conj_cone_tolerance                   3.
% 35.19/5.04  --extra_neg_conj                        none
% 35.19/5.04  --large_theory_mode                     true
% 35.19/5.04  --prolific_symb_bound                   200
% 35.19/5.04  --lt_threshold                          2000
% 35.19/5.04  --clause_weak_htbl                      true
% 35.19/5.04  --gc_record_bc_elim                     false
% 35.19/5.04  
% 35.19/5.04  ------ Preprocessing Options
% 35.19/5.04  
% 35.19/5.04  --preprocessing_flag                    true
% 35.19/5.04  --time_out_prep_mult                    0.1
% 35.19/5.04  --splitting_mode                        input
% 35.19/5.04  --splitting_grd                         true
% 35.19/5.04  --splitting_cvd                         false
% 35.19/5.04  --splitting_cvd_svl                     false
% 35.19/5.04  --splitting_nvd                         32
% 35.19/5.04  --sub_typing                            true
% 35.19/5.04  --prep_gs_sim                           true
% 35.19/5.04  --prep_unflatten                        true
% 35.19/5.04  --prep_res_sim                          true
% 35.19/5.04  --prep_upred                            true
% 35.19/5.04  --prep_sem_filter                       exhaustive
% 35.19/5.04  --prep_sem_filter_out                   false
% 35.19/5.04  --pred_elim                             true
% 35.19/5.04  --res_sim_input                         true
% 35.19/5.04  --eq_ax_congr_red                       true
% 35.19/5.04  --pure_diseq_elim                       true
% 35.19/5.04  --brand_transform                       false
% 35.19/5.04  --non_eq_to_eq                          false
% 35.19/5.04  --prep_def_merge                        true
% 35.19/5.04  --prep_def_merge_prop_impl              false
% 35.19/5.04  --prep_def_merge_mbd                    true
% 35.19/5.04  --prep_def_merge_tr_red                 false
% 35.19/5.04  --prep_def_merge_tr_cl                  false
% 35.19/5.04  --smt_preprocessing                     true
% 35.19/5.04  --smt_ac_axioms                         fast
% 35.19/5.04  --preprocessed_out                      false
% 35.19/5.04  --preprocessed_stats                    false
% 35.19/5.04  
% 35.19/5.04  ------ Abstraction refinement Options
% 35.19/5.04  
% 35.19/5.04  --abstr_ref                             []
% 35.19/5.04  --abstr_ref_prep                        false
% 35.19/5.04  --abstr_ref_until_sat                   false
% 35.19/5.04  --abstr_ref_sig_restrict                funpre
% 35.19/5.04  --abstr_ref_af_restrict_to_split_sk     false
% 35.19/5.04  --abstr_ref_under                       []
% 35.19/5.04  
% 35.19/5.04  ------ SAT Options
% 35.19/5.04  
% 35.19/5.04  --sat_mode                              false
% 35.19/5.04  --sat_fm_restart_options                ""
% 35.19/5.04  --sat_gr_def                            false
% 35.19/5.04  --sat_epr_types                         true
% 35.19/5.04  --sat_non_cyclic_types                  false
% 35.19/5.04  --sat_finite_models                     false
% 35.19/5.04  --sat_fm_lemmas                         false
% 35.19/5.04  --sat_fm_prep                           false
% 35.19/5.04  --sat_fm_uc_incr                        true
% 35.19/5.04  --sat_out_model                         small
% 35.19/5.04  --sat_out_clauses                       false
% 35.19/5.04  
% 35.19/5.04  ------ QBF Options
% 35.19/5.04  
% 35.19/5.04  --qbf_mode                              false
% 35.19/5.04  --qbf_elim_univ                         false
% 35.19/5.04  --qbf_dom_inst                          none
% 35.19/5.04  --qbf_dom_pre_inst                      false
% 35.19/5.04  --qbf_sk_in                             false
% 35.19/5.04  --qbf_pred_elim                         true
% 35.19/5.04  --qbf_split                             512
% 35.19/5.04  
% 35.19/5.04  ------ BMC1 Options
% 35.19/5.04  
% 35.19/5.04  --bmc1_incremental                      false
% 35.19/5.04  --bmc1_axioms                           reachable_all
% 35.19/5.04  --bmc1_min_bound                        0
% 35.19/5.04  --bmc1_max_bound                        -1
% 35.19/5.04  --bmc1_max_bound_default                -1
% 35.19/5.04  --bmc1_symbol_reachability              true
% 35.19/5.04  --bmc1_property_lemmas                  false
% 35.19/5.04  --bmc1_k_induction                      false
% 35.19/5.04  --bmc1_non_equiv_states                 false
% 35.19/5.04  --bmc1_deadlock                         false
% 35.19/5.04  --bmc1_ucm                              false
% 35.19/5.04  --bmc1_add_unsat_core                   none
% 35.19/5.04  --bmc1_unsat_core_children              false
% 35.19/5.04  --bmc1_unsat_core_extrapolate_axioms    false
% 35.19/5.04  --bmc1_out_stat                         full
% 35.19/5.04  --bmc1_ground_init                      false
% 35.19/5.04  --bmc1_pre_inst_next_state              false
% 35.19/5.04  --bmc1_pre_inst_state                   false
% 35.19/5.04  --bmc1_pre_inst_reach_state             false
% 35.19/5.04  --bmc1_out_unsat_core                   false
% 35.19/5.04  --bmc1_aig_witness_out                  false
% 35.19/5.04  --bmc1_verbose                          false
% 35.19/5.04  --bmc1_dump_clauses_tptp                false
% 35.19/5.04  --bmc1_dump_unsat_core_tptp             false
% 35.19/5.04  --bmc1_dump_file                        -
% 35.19/5.04  --bmc1_ucm_expand_uc_limit              128
% 35.19/5.04  --bmc1_ucm_n_expand_iterations          6
% 35.19/5.04  --bmc1_ucm_extend_mode                  1
% 35.19/5.04  --bmc1_ucm_init_mode                    2
% 35.19/5.04  --bmc1_ucm_cone_mode                    none
% 35.19/5.04  --bmc1_ucm_reduced_relation_type        0
% 35.19/5.04  --bmc1_ucm_relax_model                  4
% 35.19/5.04  --bmc1_ucm_full_tr_after_sat            true
% 35.19/5.04  --bmc1_ucm_expand_neg_assumptions       false
% 35.19/5.04  --bmc1_ucm_layered_model                none
% 35.19/5.04  --bmc1_ucm_max_lemma_size               10
% 35.19/5.04  
% 35.19/5.04  ------ AIG Options
% 35.19/5.04  
% 35.19/5.04  --aig_mode                              false
% 35.19/5.04  
% 35.19/5.04  ------ Instantiation Options
% 35.19/5.04  
% 35.19/5.04  --instantiation_flag                    true
% 35.19/5.04  --inst_sos_flag                         true
% 35.19/5.04  --inst_sos_phase                        true
% 35.19/5.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.19/5.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.19/5.04  --inst_lit_sel_side                     num_symb
% 35.19/5.04  --inst_solver_per_active                1400
% 35.19/5.04  --inst_solver_calls_frac                1.
% 35.19/5.04  --inst_passive_queue_type               priority_queues
% 35.19/5.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.19/5.04  --inst_passive_queues_freq              [25;2]
% 35.19/5.04  --inst_dismatching                      true
% 35.19/5.04  --inst_eager_unprocessed_to_passive     true
% 35.19/5.04  --inst_prop_sim_given                   true
% 35.19/5.04  --inst_prop_sim_new                     false
% 35.19/5.04  --inst_subs_new                         false
% 35.19/5.04  --inst_eq_res_simp                      false
% 35.19/5.04  --inst_subs_given                       false
% 35.19/5.04  --inst_orphan_elimination               true
% 35.19/5.04  --inst_learning_loop_flag               true
% 35.19/5.04  --inst_learning_start                   3000
% 35.19/5.04  --inst_learning_factor                  2
% 35.19/5.04  --inst_start_prop_sim_after_learn       3
% 35.19/5.04  --inst_sel_renew                        solver
% 35.19/5.04  --inst_lit_activity_flag                true
% 35.19/5.04  --inst_restr_to_given                   false
% 35.19/5.04  --inst_activity_threshold               500
% 35.19/5.04  --inst_out_proof                        true
% 35.19/5.04  
% 35.19/5.04  ------ Resolution Options
% 35.19/5.04  
% 35.19/5.04  --resolution_flag                       true
% 35.19/5.04  --res_lit_sel                           adaptive
% 35.19/5.04  --res_lit_sel_side                      none
% 35.19/5.04  --res_ordering                          kbo
% 35.19/5.04  --res_to_prop_solver                    active
% 35.19/5.04  --res_prop_simpl_new                    false
% 35.19/5.04  --res_prop_simpl_given                  true
% 35.19/5.04  --res_passive_queue_type                priority_queues
% 35.19/5.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.19/5.04  --res_passive_queues_freq               [15;5]
% 35.19/5.04  --res_forward_subs                      full
% 35.19/5.04  --res_backward_subs                     full
% 35.19/5.04  --res_forward_subs_resolution           true
% 35.19/5.04  --res_backward_subs_resolution          true
% 35.19/5.04  --res_orphan_elimination                true
% 35.19/5.04  --res_time_limit                        2.
% 35.19/5.04  --res_out_proof                         true
% 35.19/5.04  
% 35.19/5.04  ------ Superposition Options
% 35.19/5.04  
% 35.19/5.04  --superposition_flag                    true
% 35.19/5.04  --sup_passive_queue_type                priority_queues
% 35.19/5.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.19/5.04  --sup_passive_queues_freq               [8;1;4]
% 35.19/5.04  --demod_completeness_check              fast
% 35.19/5.04  --demod_use_ground                      true
% 35.19/5.04  --sup_to_prop_solver                    passive
% 35.19/5.04  --sup_prop_simpl_new                    true
% 35.19/5.04  --sup_prop_simpl_given                  true
% 35.19/5.04  --sup_fun_splitting                     true
% 35.19/5.04  --sup_smt_interval                      50000
% 35.19/5.04  
% 35.19/5.04  ------ Superposition Simplification Setup
% 35.19/5.04  
% 35.19/5.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.19/5.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.19/5.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.19/5.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.19/5.04  --sup_full_triv                         [TrivRules;PropSubs]
% 35.19/5.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.19/5.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.19/5.04  --sup_immed_triv                        [TrivRules]
% 35.19/5.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.19/5.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.19/5.04  --sup_immed_bw_main                     []
% 35.19/5.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.19/5.04  --sup_input_triv                        [Unflattening;TrivRules]
% 35.19/5.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.19/5.04  --sup_input_bw                          []
% 35.19/5.04  
% 35.19/5.04  ------ Combination Options
% 35.19/5.04  
% 35.19/5.04  --comb_res_mult                         3
% 35.19/5.04  --comb_sup_mult                         2
% 35.19/5.04  --comb_inst_mult                        10
% 35.19/5.04  
% 35.19/5.04  ------ Debug Options
% 35.19/5.04  
% 35.19/5.04  --dbg_backtrace                         false
% 35.19/5.04  --dbg_dump_prop_clauses                 false
% 35.19/5.04  --dbg_dump_prop_clauses_file            -
% 35.19/5.04  --dbg_out_stat                          false
% 35.19/5.04  ------ Parsing...
% 35.19/5.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.19/5.04  
% 35.19/5.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.19/5.04  
% 35.19/5.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.19/5.04  
% 35.19/5.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.19/5.04  ------ Proving...
% 35.19/5.04  ------ Problem Properties 
% 35.19/5.04  
% 35.19/5.04  
% 35.19/5.04  clauses                                 14
% 35.19/5.04  conjectures                             3
% 35.19/5.04  EPR                                     0
% 35.19/5.04  Horn                                    14
% 35.19/5.04  unary                                   5
% 35.19/5.04  binary                                  6
% 35.19/5.04  lits                                    27
% 35.19/5.04  lits eq                                 2
% 35.19/5.04  fd_pure                                 0
% 35.19/5.04  fd_pseudo                               0
% 35.19/5.04  fd_cond                                 0
% 35.19/5.04  fd_pseudo_cond                          0
% 35.19/5.04  AC symbols                              0
% 35.19/5.04  
% 35.19/5.04  ------ Schedule dynamic 5 is on 
% 35.19/5.04  
% 35.19/5.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.19/5.04  
% 35.19/5.04  
% 35.19/5.04  ------ 
% 35.19/5.04  Current options:
% 35.19/5.04  ------ 
% 35.19/5.04  
% 35.19/5.04  ------ Input Options
% 35.19/5.04  
% 35.19/5.04  --out_options                           all
% 35.19/5.04  --tptp_safe_out                         true
% 35.19/5.04  --problem_path                          ""
% 35.19/5.04  --include_path                          ""
% 35.19/5.04  --clausifier                            res/vclausify_rel
% 35.19/5.04  --clausifier_options                    ""
% 35.19/5.04  --stdin                                 false
% 35.19/5.04  --stats_out                             all
% 35.19/5.04  
% 35.19/5.04  ------ General Options
% 35.19/5.04  
% 35.19/5.04  --fof                                   false
% 35.19/5.04  --time_out_real                         305.
% 35.19/5.04  --time_out_virtual                      -1.
% 35.19/5.04  --symbol_type_check                     false
% 35.19/5.04  --clausify_out                          false
% 35.19/5.04  --sig_cnt_out                           false
% 35.19/5.04  --trig_cnt_out                          false
% 35.19/5.04  --trig_cnt_out_tolerance                1.
% 35.19/5.04  --trig_cnt_out_sk_spl                   false
% 35.19/5.04  --abstr_cl_out                          false
% 35.19/5.04  
% 35.19/5.04  ------ Global Options
% 35.19/5.04  
% 35.19/5.04  --schedule                              default
% 35.19/5.04  --add_important_lit                     false
% 35.19/5.04  --prop_solver_per_cl                    1000
% 35.19/5.04  --min_unsat_core                        false
% 35.19/5.04  --soft_assumptions                      false
% 35.19/5.04  --soft_lemma_size                       3
% 35.19/5.04  --prop_impl_unit_size                   0
% 35.19/5.04  --prop_impl_unit                        []
% 35.19/5.04  --share_sel_clauses                     true
% 35.19/5.04  --reset_solvers                         false
% 35.19/5.04  --bc_imp_inh                            [conj_cone]
% 35.19/5.04  --conj_cone_tolerance                   3.
% 35.19/5.04  --extra_neg_conj                        none
% 35.19/5.04  --large_theory_mode                     true
% 35.19/5.04  --prolific_symb_bound                   200
% 35.19/5.04  --lt_threshold                          2000
% 35.19/5.04  --clause_weak_htbl                      true
% 35.19/5.04  --gc_record_bc_elim                     false
% 35.19/5.04  
% 35.19/5.04  ------ Preprocessing Options
% 35.19/5.04  
% 35.19/5.04  --preprocessing_flag                    true
% 35.19/5.04  --time_out_prep_mult                    0.1
% 35.19/5.04  --splitting_mode                        input
% 35.19/5.04  --splitting_grd                         true
% 35.19/5.04  --splitting_cvd                         false
% 35.19/5.04  --splitting_cvd_svl                     false
% 35.19/5.04  --splitting_nvd                         32
% 35.19/5.04  --sub_typing                            true
% 35.19/5.04  --prep_gs_sim                           true
% 35.19/5.04  --prep_unflatten                        true
% 35.19/5.04  --prep_res_sim                          true
% 35.19/5.04  --prep_upred                            true
% 35.19/5.04  --prep_sem_filter                       exhaustive
% 35.19/5.04  --prep_sem_filter_out                   false
% 35.19/5.04  --pred_elim                             true
% 35.19/5.04  --res_sim_input                         true
% 35.19/5.04  --eq_ax_congr_red                       true
% 35.19/5.04  --pure_diseq_elim                       true
% 35.19/5.04  --brand_transform                       false
% 35.19/5.04  --non_eq_to_eq                          false
% 35.19/5.04  --prep_def_merge                        true
% 35.19/5.04  --prep_def_merge_prop_impl              false
% 35.19/5.04  --prep_def_merge_mbd                    true
% 35.19/5.04  --prep_def_merge_tr_red                 false
% 35.19/5.04  --prep_def_merge_tr_cl                  false
% 35.19/5.04  --smt_preprocessing                     true
% 35.19/5.04  --smt_ac_axioms                         fast
% 35.19/5.04  --preprocessed_out                      false
% 35.19/5.04  --preprocessed_stats                    false
% 35.19/5.04  
% 35.19/5.04  ------ Abstraction refinement Options
% 35.19/5.04  
% 35.19/5.04  --abstr_ref                             []
% 35.19/5.04  --abstr_ref_prep                        false
% 35.19/5.04  --abstr_ref_until_sat                   false
% 35.19/5.04  --abstr_ref_sig_restrict                funpre
% 35.19/5.04  --abstr_ref_af_restrict_to_split_sk     false
% 35.19/5.04  --abstr_ref_under                       []
% 35.19/5.04  
% 35.19/5.04  ------ SAT Options
% 35.19/5.04  
% 35.19/5.04  --sat_mode                              false
% 35.19/5.04  --sat_fm_restart_options                ""
% 35.19/5.04  --sat_gr_def                            false
% 35.19/5.04  --sat_epr_types                         true
% 35.19/5.04  --sat_non_cyclic_types                  false
% 35.19/5.04  --sat_finite_models                     false
% 35.19/5.04  --sat_fm_lemmas                         false
% 35.19/5.04  --sat_fm_prep                           false
% 35.19/5.04  --sat_fm_uc_incr                        true
% 35.19/5.04  --sat_out_model                         small
% 35.19/5.04  --sat_out_clauses                       false
% 35.19/5.04  
% 35.19/5.04  ------ QBF Options
% 35.19/5.04  
% 35.19/5.04  --qbf_mode                              false
% 35.19/5.04  --qbf_elim_univ                         false
% 35.19/5.04  --qbf_dom_inst                          none
% 35.19/5.04  --qbf_dom_pre_inst                      false
% 35.19/5.04  --qbf_sk_in                             false
% 35.19/5.04  --qbf_pred_elim                         true
% 35.19/5.04  --qbf_split                             512
% 35.19/5.04  
% 35.19/5.04  ------ BMC1 Options
% 35.19/5.04  
% 35.19/5.04  --bmc1_incremental                      false
% 35.19/5.04  --bmc1_axioms                           reachable_all
% 35.19/5.04  --bmc1_min_bound                        0
% 35.19/5.04  --bmc1_max_bound                        -1
% 35.19/5.04  --bmc1_max_bound_default                -1
% 35.19/5.04  --bmc1_symbol_reachability              true
% 35.19/5.04  --bmc1_property_lemmas                  false
% 35.19/5.04  --bmc1_k_induction                      false
% 35.19/5.04  --bmc1_non_equiv_states                 false
% 35.19/5.04  --bmc1_deadlock                         false
% 35.19/5.04  --bmc1_ucm                              false
% 35.19/5.04  --bmc1_add_unsat_core                   none
% 35.19/5.04  --bmc1_unsat_core_children              false
% 35.19/5.04  --bmc1_unsat_core_extrapolate_axioms    false
% 35.19/5.04  --bmc1_out_stat                         full
% 35.19/5.04  --bmc1_ground_init                      false
% 35.19/5.04  --bmc1_pre_inst_next_state              false
% 35.19/5.04  --bmc1_pre_inst_state                   false
% 35.19/5.04  --bmc1_pre_inst_reach_state             false
% 35.19/5.04  --bmc1_out_unsat_core                   false
% 35.19/5.04  --bmc1_aig_witness_out                  false
% 35.19/5.04  --bmc1_verbose                          false
% 35.19/5.04  --bmc1_dump_clauses_tptp                false
% 35.19/5.04  --bmc1_dump_unsat_core_tptp             false
% 35.19/5.04  --bmc1_dump_file                        -
% 35.19/5.04  --bmc1_ucm_expand_uc_limit              128
% 35.19/5.04  --bmc1_ucm_n_expand_iterations          6
% 35.19/5.04  --bmc1_ucm_extend_mode                  1
% 35.19/5.04  --bmc1_ucm_init_mode                    2
% 35.19/5.04  --bmc1_ucm_cone_mode                    none
% 35.19/5.04  --bmc1_ucm_reduced_relation_type        0
% 35.19/5.04  --bmc1_ucm_relax_model                  4
% 35.19/5.04  --bmc1_ucm_full_tr_after_sat            true
% 35.19/5.04  --bmc1_ucm_expand_neg_assumptions       false
% 35.19/5.04  --bmc1_ucm_layered_model                none
% 35.19/5.04  --bmc1_ucm_max_lemma_size               10
% 35.19/5.04  
% 35.19/5.04  ------ AIG Options
% 35.19/5.04  
% 35.19/5.04  --aig_mode                              false
% 35.19/5.04  
% 35.19/5.04  ------ Instantiation Options
% 35.19/5.04  
% 35.19/5.04  --instantiation_flag                    true
% 35.19/5.04  --inst_sos_flag                         true
% 35.19/5.04  --inst_sos_phase                        true
% 35.19/5.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.19/5.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.19/5.04  --inst_lit_sel_side                     none
% 35.19/5.04  --inst_solver_per_active                1400
% 35.19/5.04  --inst_solver_calls_frac                1.
% 35.19/5.04  --inst_passive_queue_type               priority_queues
% 35.19/5.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.19/5.04  --inst_passive_queues_freq              [25;2]
% 35.19/5.04  --inst_dismatching                      true
% 35.19/5.04  --inst_eager_unprocessed_to_passive     true
% 35.19/5.04  --inst_prop_sim_given                   true
% 35.19/5.04  --inst_prop_sim_new                     false
% 35.19/5.04  --inst_subs_new                         false
% 35.19/5.04  --inst_eq_res_simp                      false
% 35.19/5.04  --inst_subs_given                       false
% 35.19/5.04  --inst_orphan_elimination               true
% 35.19/5.04  --inst_learning_loop_flag               true
% 35.19/5.04  --inst_learning_start                   3000
% 35.19/5.04  --inst_learning_factor                  2
% 35.19/5.04  --inst_start_prop_sim_after_learn       3
% 35.19/5.04  --inst_sel_renew                        solver
% 35.19/5.04  --inst_lit_activity_flag                true
% 35.19/5.04  --inst_restr_to_given                   false
% 35.19/5.04  --inst_activity_threshold               500
% 35.19/5.04  --inst_out_proof                        true
% 35.19/5.04  
% 35.19/5.04  ------ Resolution Options
% 35.19/5.04  
% 35.19/5.04  --resolution_flag                       false
% 35.19/5.04  --res_lit_sel                           adaptive
% 35.19/5.04  --res_lit_sel_side                      none
% 35.19/5.04  --res_ordering                          kbo
% 35.19/5.04  --res_to_prop_solver                    active
% 35.19/5.04  --res_prop_simpl_new                    false
% 35.19/5.04  --res_prop_simpl_given                  true
% 35.19/5.04  --res_passive_queue_type                priority_queues
% 35.19/5.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.19/5.04  --res_passive_queues_freq               [15;5]
% 35.19/5.04  --res_forward_subs                      full
% 35.19/5.04  --res_backward_subs                     full
% 35.19/5.04  --res_forward_subs_resolution           true
% 35.19/5.04  --res_backward_subs_resolution          true
% 35.19/5.04  --res_orphan_elimination                true
% 35.19/5.04  --res_time_limit                        2.
% 35.19/5.04  --res_out_proof                         true
% 35.19/5.04  
% 35.19/5.04  ------ Superposition Options
% 35.19/5.04  
% 35.19/5.04  --superposition_flag                    true
% 35.19/5.04  --sup_passive_queue_type                priority_queues
% 35.19/5.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.19/5.04  --sup_passive_queues_freq               [8;1;4]
% 35.19/5.04  --demod_completeness_check              fast
% 35.19/5.04  --demod_use_ground                      true
% 35.19/5.04  --sup_to_prop_solver                    passive
% 35.19/5.04  --sup_prop_simpl_new                    true
% 35.19/5.04  --sup_prop_simpl_given                  true
% 35.19/5.04  --sup_fun_splitting                     true
% 35.19/5.04  --sup_smt_interval                      50000
% 35.19/5.04  
% 35.19/5.04  ------ Superposition Simplification Setup
% 35.19/5.04  
% 35.19/5.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.19/5.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.19/5.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.19/5.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.19/5.04  --sup_full_triv                         [TrivRules;PropSubs]
% 35.19/5.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.19/5.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.19/5.04  --sup_immed_triv                        [TrivRules]
% 35.19/5.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.19/5.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.19/5.04  --sup_immed_bw_main                     []
% 35.19/5.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.19/5.04  --sup_input_triv                        [Unflattening;TrivRules]
% 35.19/5.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.19/5.04  --sup_input_bw                          []
% 35.19/5.04  
% 35.19/5.04  ------ Combination Options
% 35.19/5.04  
% 35.19/5.04  --comb_res_mult                         3
% 35.19/5.04  --comb_sup_mult                         2
% 35.19/5.04  --comb_inst_mult                        10
% 35.19/5.04  
% 35.19/5.04  ------ Debug Options
% 35.19/5.04  
% 35.19/5.04  --dbg_backtrace                         false
% 35.19/5.04  --dbg_dump_prop_clauses                 false
% 35.19/5.04  --dbg_dump_prop_clauses_file            -
% 35.19/5.04  --dbg_out_stat                          false
% 35.19/5.04  
% 35.19/5.04  
% 35.19/5.04  
% 35.19/5.04  
% 35.19/5.04  ------ Proving...
% 35.19/5.04  
% 35.19/5.04  
% 35.19/5.04  % SZS status Theorem for theBenchmark.p
% 35.19/5.04  
% 35.19/5.04  % SZS output start CNFRefutation for theBenchmark.p
% 35.19/5.04  
% 35.19/5.04  fof(f11,conjecture,(
% 35.19/5.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 35.19/5.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.19/5.04  
% 35.19/5.04  fof(f12,negated_conjecture,(
% 35.19/5.04    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 35.19/5.04    inference(negated_conjecture,[],[f11])).
% 35.19/5.04  
% 35.19/5.04  fof(f23,plain,(
% 35.19/5.04    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 35.19/5.04    inference(ennf_transformation,[],[f12])).
% 35.19/5.04  
% 35.19/5.04  fof(f27,plain,(
% 35.19/5.04    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.19/5.04    introduced(choice_axiom,[])).
% 35.19/5.04  
% 35.19/5.04  fof(f26,plain,(
% 35.19/5.04    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.19/5.04    introduced(choice_axiom,[])).
% 35.19/5.04  
% 35.19/5.04  fof(f25,plain,(
% 35.19/5.04    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 35.19/5.04    introduced(choice_axiom,[])).
% 35.19/5.04  
% 35.19/5.04  fof(f28,plain,(
% 35.19/5.04    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 35.19/5.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f27,f26,f25])).
% 35.19/5.04  
% 35.19/5.04  fof(f42,plain,(
% 35.19/5.04    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 35.19/5.04    inference(cnf_transformation,[],[f28])).
% 35.19/5.04  
% 35.19/5.04  fof(f8,axiom,(
% 35.19/5.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 35.19/5.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.19/5.04  
% 35.19/5.04  fof(f24,plain,(
% 35.19/5.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 35.19/5.04    inference(nnf_transformation,[],[f8])).
% 35.19/5.04  
% 35.19/5.04  fof(f36,plain,(
% 35.19/5.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 35.19/5.04    inference(cnf_transformation,[],[f24])).
% 35.19/5.04  
% 35.19/5.04  fof(f41,plain,(
% 35.19/5.04    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 35.19/5.04    inference(cnf_transformation,[],[f28])).
% 35.19/5.04  
% 35.19/5.04  fof(f6,axiom,(
% 35.19/5.04    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 35.19/5.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.19/5.04  
% 35.19/5.04  fof(f16,plain,(
% 35.19/5.04    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 35.19/5.04    inference(ennf_transformation,[],[f6])).
% 35.19/5.04  
% 35.19/5.04  fof(f17,plain,(
% 35.19/5.04    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 35.19/5.04    inference(flattening,[],[f16])).
% 35.19/5.04  
% 35.19/5.04  fof(f34,plain,(
% 35.19/5.04    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.19/5.04    inference(cnf_transformation,[],[f17])).
% 35.19/5.04  
% 35.19/5.04  fof(f2,axiom,(
% 35.19/5.04    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 35.19/5.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.19/5.04  
% 35.19/5.04  fof(f14,plain,(
% 35.19/5.04    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 35.19/5.04    inference(ennf_transformation,[],[f2])).
% 35.19/5.04  
% 35.19/5.04  fof(f30,plain,(
% 35.19/5.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 35.19/5.04    inference(cnf_transformation,[],[f14])).
% 35.19/5.04  
% 35.19/5.04  fof(f5,axiom,(
% 35.19/5.04    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 35.19/5.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.19/5.04  
% 35.19/5.04  fof(f33,plain,(
% 35.19/5.04    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 35.19/5.04    inference(cnf_transformation,[],[f5])).
% 35.19/5.04  
% 35.19/5.04  fof(f10,axiom,(
% 35.19/5.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 35.19/5.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.19/5.04  
% 35.19/5.04  fof(f21,plain,(
% 35.19/5.04    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.19/5.04    inference(ennf_transformation,[],[f10])).
% 35.19/5.04  
% 35.19/5.04  fof(f22,plain,(
% 35.19/5.04    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.19/5.04    inference(flattening,[],[f21])).
% 35.19/5.04  
% 35.19/5.04  fof(f39,plain,(
% 35.19/5.04    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.19/5.04    inference(cnf_transformation,[],[f22])).
% 35.19/5.04  
% 35.19/5.04  fof(f40,plain,(
% 35.19/5.04    l1_pre_topc(sK0)),
% 35.19/5.04    inference(cnf_transformation,[],[f28])).
% 35.19/5.04  
% 35.19/5.04  fof(f37,plain,(
% 35.19/5.04    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 35.19/5.04    inference(cnf_transformation,[],[f24])).
% 35.19/5.04  
% 35.19/5.04  fof(f4,axiom,(
% 35.19/5.04    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 35.19/5.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.19/5.04  
% 35.19/5.04  fof(f15,plain,(
% 35.19/5.04    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 35.19/5.04    inference(ennf_transformation,[],[f4])).
% 35.19/5.04  
% 35.19/5.04  fof(f32,plain,(
% 35.19/5.04    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 35.19/5.04    inference(cnf_transformation,[],[f15])).
% 35.19/5.04  
% 35.19/5.04  fof(f3,axiom,(
% 35.19/5.04    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 35.19/5.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.19/5.04  
% 35.19/5.04  fof(f31,plain,(
% 35.19/5.04    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 35.19/5.04    inference(cnf_transformation,[],[f3])).
% 35.19/5.04  
% 35.19/5.04  fof(f9,axiom,(
% 35.19/5.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 35.19/5.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.19/5.04  
% 35.19/5.04  fof(f20,plain,(
% 35.19/5.04    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.19/5.04    inference(ennf_transformation,[],[f9])).
% 35.19/5.04  
% 35.19/5.04  fof(f38,plain,(
% 35.19/5.04    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.19/5.04    inference(cnf_transformation,[],[f20])).
% 35.19/5.04  
% 35.19/5.04  fof(f1,axiom,(
% 35.19/5.04    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 35.19/5.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.19/5.04  
% 35.19/5.04  fof(f13,plain,(
% 35.19/5.04    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 35.19/5.04    inference(ennf_transformation,[],[f1])).
% 35.19/5.04  
% 35.19/5.04  fof(f29,plain,(
% 35.19/5.04    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 35.19/5.04    inference(cnf_transformation,[],[f13])).
% 35.19/5.04  
% 35.19/5.04  fof(f7,axiom,(
% 35.19/5.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 35.19/5.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.19/5.04  
% 35.19/5.04  fof(f18,plain,(
% 35.19/5.04    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 35.19/5.04    inference(ennf_transformation,[],[f7])).
% 35.19/5.04  
% 35.19/5.04  fof(f19,plain,(
% 35.19/5.04    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.19/5.04    inference(flattening,[],[f18])).
% 35.19/5.04  
% 35.19/5.04  fof(f35,plain,(
% 35.19/5.04    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.19/5.04    inference(cnf_transformation,[],[f19])).
% 35.19/5.04  
% 35.19/5.04  fof(f43,plain,(
% 35.19/5.04    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 35.19/5.04    inference(cnf_transformation,[],[f28])).
% 35.19/5.04  
% 35.19/5.04  cnf(c_371,plain,
% 35.19/5.04      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.19/5.04      theory(equality) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_125024,plain,
% 35.19/5.04      ( ~ r1_tarski(X0,X1)
% 35.19/5.04      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.19/5.04      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 35.19/5.04      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_371]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_125057,plain,
% 35.19/5.04      ( ~ r1_tarski(X0,k1_tops_1(X1,X2))
% 35.19/5.04      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.19/5.04      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 35.19/5.04      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,X2) ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_125024]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_125143,plain,
% 35.19/5.04      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.19/5.04      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1))
% 35.19/5.04      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 35.19/5.04      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,X1) ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_125057]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_133555,plain,
% 35.19/5.04      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 35.19/5.04      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 35.19/5.04      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 35.19/5.04      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_125143]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_12,negated_conjecture,
% 35.19/5.04      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.19/5.04      inference(cnf_transformation,[],[f42]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_697,plain,
% 35.19/5.04      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_8,plain,
% 35.19/5.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 35.19/5.04      inference(cnf_transformation,[],[f36]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_699,plain,
% 35.19/5.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.19/5.04      | r1_tarski(X0,X1) = iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1318,plain,
% 35.19/5.04      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_697,c_699]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_13,negated_conjecture,
% 35.19/5.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.19/5.04      inference(cnf_transformation,[],[f41]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_696,plain,
% 35.19/5.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1319,plain,
% 35.19/5.04      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_696,c_699]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_5,plain,
% 35.19/5.04      ( ~ r1_tarski(X0,X1)
% 35.19/5.04      | ~ r1_tarski(X2,X1)
% 35.19/5.04      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 35.19/5.04      inference(cnf_transformation,[],[f34]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_701,plain,
% 35.19/5.04      ( r1_tarski(X0,X1) != iProver_top
% 35.19/5.04      | r1_tarski(X2,X1) != iProver_top
% 35.19/5.04      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1,plain,
% 35.19/5.04      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 35.19/5.04      inference(cnf_transformation,[],[f30]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_705,plain,
% 35.19/5.04      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1716,plain,
% 35.19/5.04      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = X2
% 35.19/5.04      | r1_tarski(X0,X2) != iProver_top
% 35.19/5.04      | r1_tarski(X1,X2) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_701,c_705]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_12923,plain,
% 35.19/5.04      ( k2_xboole_0(k2_xboole_0(sK1,X0),u1_struct_0(sK0)) = u1_struct_0(sK0)
% 35.19/5.04      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_1319,c_1716]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_15538,plain,
% 35.19/5.04      ( k2_xboole_0(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_1318,c_12923]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_4,plain,
% 35.19/5.04      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 35.19/5.04      inference(cnf_transformation,[],[f33]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_702,plain,
% 35.19/5.04      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_15573,plain,
% 35.19/5.04      ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) = iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_15538,c_702]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_10,plain,
% 35.19/5.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.19/5.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 35.19/5.04      | ~ r1_tarski(X0,X2)
% 35.19/5.04      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 35.19/5.04      | ~ l1_pre_topc(X1) ),
% 35.19/5.04      inference(cnf_transformation,[],[f39]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_14,negated_conjecture,
% 35.19/5.04      ( l1_pre_topc(sK0) ),
% 35.19/5.04      inference(cnf_transformation,[],[f40]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_201,plain,
% 35.19/5.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.19/5.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 35.19/5.04      | ~ r1_tarski(X0,X2)
% 35.19/5.04      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 35.19/5.04      | sK0 != X1 ),
% 35.19/5.04      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_202,plain,
% 35.19/5.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.19/5.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.19/5.04      | ~ r1_tarski(X1,X0)
% 35.19/5.04      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 35.19/5.04      inference(unflattening,[status(thm)],[c_201]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_695,plain,
% 35.19/5.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.19/5.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.19/5.04      | r1_tarski(X1,X0) != iProver_top
% 35.19/5.04      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_202]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_7,plain,
% 35.19/5.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.19/5.04      inference(cnf_transformation,[],[f37]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_700,plain,
% 35.19/5.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 35.19/5.04      | r1_tarski(X0,X1) != iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_12924,plain,
% 35.19/5.04      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,X0),X1),k1_tops_1(sK0,X2)) = k1_tops_1(sK0,X2)
% 35.19/5.04      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.19/5.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.19/5.04      | r1_tarski(X0,X2) != iProver_top
% 35.19/5.04      | r1_tarski(X1,k1_tops_1(sK0,X2)) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_695,c_1716]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_18077,plain,
% 35.19/5.04      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
% 35.19/5.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.19/5.04      | r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
% 35.19/5.04      | r1_tarski(sK1,X1) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_696,c_12924]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_18539,plain,
% 35.19/5.04      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
% 35.19/5.04      | r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
% 35.19/5.04      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
% 35.19/5.04      | r1_tarski(sK1,X1) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_700,c_18077]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_23889,plain,
% 35.19/5.04      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
% 35.19/5.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.19/5.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.19/5.04      | r1_tarski(X0,X1) != iProver_top
% 35.19/5.04      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
% 35.19/5.04      | r1_tarski(sK1,X1) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_695,c_18539]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_53034,plain,
% 35.19/5.04      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 35.19/5.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.19/5.04      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 35.19/5.04      | r1_tarski(sK2,X0) != iProver_top
% 35.19/5.04      | r1_tarski(sK1,X0) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_697,c_23889]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_745,plain,
% 35.19/5.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.19/5.04      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_7]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_746,plain,
% 35.19/5.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 35.19/5.04      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_55170,plain,
% 35.19/5.04      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 35.19/5.04      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 35.19/5.04      | r1_tarski(sK2,X0) != iProver_top
% 35.19/5.04      | r1_tarski(sK1,X0) != iProver_top ),
% 35.19/5.04      inference(global_propositional_subsumption,
% 35.19/5.04                [status(thm)],
% 35.19/5.04                [c_53034,c_746]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_55192,plain,
% 35.19/5.04      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 35.19/5.04      | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) != iProver_top
% 35.19/5.04      | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_15573,c_55170]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_14840,plain,
% 35.19/5.04      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_4]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_14841,plain,
% 35.19/5.04      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_14840]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_3,plain,
% 35.19/5.04      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 35.19/5.04      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 35.19/5.04      inference(cnf_transformation,[],[f32]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_9206,plain,
% 35.19/5.04      ( r1_tarski(X0,k2_xboole_0(sK1,sK2))
% 35.19/5.04      | ~ r1_tarski(k4_xboole_0(X0,sK1),sK2) ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_3]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_19633,plain,
% 35.19/5.04      ( ~ r1_tarski(k4_xboole_0(sK2,sK1),sK2)
% 35.19/5.04      | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_9206]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_19635,plain,
% 35.19/5.04      ( r1_tarski(k4_xboole_0(sK2,sK1),sK2) != iProver_top
% 35.19/5.04      | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_19633]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_2,plain,
% 35.19/5.04      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 35.19/5.04      inference(cnf_transformation,[],[f31]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1052,plain,
% 35.19/5.04      ( r1_tarski(k4_xboole_0(sK2,X0),sK2) ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_2]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_19634,plain,
% 35.19/5.04      ( r1_tarski(k4_xboole_0(sK2,sK1),sK2) ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_1052]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_19637,plain,
% 35.19/5.04      ( r1_tarski(k4_xboole_0(sK2,sK1),sK2) = iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_19634]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_56121,plain,
% 35.19/5.04      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 35.19/5.04      inference(global_propositional_subsumption,
% 35.19/5.04                [status(thm)],
% 35.19/5.04                [c_55192,c_14841,c_19635,c_19637]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_56160,plain,
% 35.19/5.04      ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_56121,c_702]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_56249,plain,
% 35.19/5.04      ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
% 35.19/5.04      inference(predicate_to_equality_rev,[status(thm)],[c_56160]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_9,plain,
% 35.19/5.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.19/5.04      | r1_tarski(k1_tops_1(X1,X0),X0)
% 35.19/5.04      | ~ l1_pre_topc(X1) ),
% 35.19/5.04      inference(cnf_transformation,[],[f38]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_219,plain,
% 35.19/5.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.19/5.04      | r1_tarski(k1_tops_1(X1,X0),X0)
% 35.19/5.04      | sK0 != X1 ),
% 35.19/5.04      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_220,plain,
% 35.19/5.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.19/5.04      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 35.19/5.04      inference(unflattening,[status(thm)],[c_219]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_694,plain,
% 35.19/5.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.19/5.04      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_975,plain,
% 35.19/5.04      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_696,c_694]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1311,plain,
% 35.19/5.04      ( k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = sK1 ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_975,c_705]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_0,plain,
% 35.19/5.04      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 35.19/5.04      inference(cnf_transformation,[],[f29]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_706,plain,
% 35.19/5.04      ( r1_tarski(X0,X1) = iProver_top
% 35.19/5.04      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1802,plain,
% 35.19/5.04      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 35.19/5.04      | r1_tarski(sK1,X0) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_1311,c_706]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_10632,plain,
% 35.19/5.04      ( k2_xboole_0(k1_tops_1(sK0,sK1),X0) = X0
% 35.19/5.04      | r1_tarski(sK1,X0) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_1802,c_705]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_12081,plain,
% 35.19/5.04      ( k2_xboole_0(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_1319,c_10632]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_12251,plain,
% 35.19/5.04      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_12081,c_702]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_974,plain,
% 35.19/5.04      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_697,c_694]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1310,plain,
% 35.19/5.04      ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = sK2 ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_974,c_705]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1801,plain,
% 35.19/5.04      ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
% 35.19/5.04      | r1_tarski(sK2,X0) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_1310,c_706]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_9932,plain,
% 35.19/5.04      ( k2_xboole_0(k1_tops_1(sK0,sK2),X0) = X0
% 35.19/5.04      | r1_tarski(sK2,X0) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_1801,c_705]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_11099,plain,
% 35.19/5.04      ( k2_xboole_0(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_1318,c_9932]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_11205,plain,
% 35.19/5.04      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_11099,c_702]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_375,plain,
% 35.19/5.04      ( X0 != X1 | X2 != X3 | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
% 35.19/5.04      theory(equality) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1285,plain,
% 35.19/5.04      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 35.19/5.04      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
% 35.19/5.04      | sK0 != X1 ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_375]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1734,plain,
% 35.19/5.04      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 35.19/5.04      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,sK2))
% 35.19/5.04      | sK0 != X0 ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_1285]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1735,plain,
% 35.19/5.04      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 35.19/5.04      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 35.19/5.04      | sK0 != sK0 ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_1734]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_6,plain,
% 35.19/5.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.19/5.04      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.19/5.04      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 35.19/5.04      inference(cnf_transformation,[],[f35]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_117,plain,
% 35.19/5.04      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 35.19/5.04      inference(prop_impl,[status(thm)],[c_7]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_118,plain,
% 35.19/5.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.19/5.04      inference(renaming,[status(thm)],[c_117]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_143,plain,
% 35.19/5.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.19/5.04      | ~ r1_tarski(X2,X1)
% 35.19/5.04      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 35.19/5.04      inference(bin_hyper_res,[status(thm)],[c_6,c_118]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_289,plain,
% 35.19/5.04      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 35.19/5.04      inference(prop_impl,[status(thm)],[c_7]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_290,plain,
% 35.19/5.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.19/5.04      inference(renaming,[status(thm)],[c_289]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_314,plain,
% 35.19/5.04      ( ~ r1_tarski(X0,X1)
% 35.19/5.04      | ~ r1_tarski(X2,X1)
% 35.19/5.04      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 35.19/5.04      inference(bin_hyper_res,[status(thm)],[c_143,c_290]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_693,plain,
% 35.19/5.04      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 35.19/5.04      | r1_tarski(X1,X0) != iProver_top
% 35.19/5.04      | r1_tarski(X2,X0) != iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1407,plain,
% 35.19/5.04      ( k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)
% 35.19/5.04      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_1318,c_693]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1707,plain,
% 35.19/5.04      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 35.19/5.04      inference(superposition,[status(thm)],[c_1319,c_1407]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1449,plain,
% 35.19/5.04      ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 35.19/5.04      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 35.19/5.04      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_314]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_1450,plain,
% 35.19/5.04      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 35.19/5.04      | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top
% 35.19/5.04      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top ),
% 35.19/5.04      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_369,plain,( X0 = X0 ),theory(equality) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_384,plain,
% 35.19/5.04      ( sK0 = sK0 ),
% 35.19/5.04      inference(instantiation,[status(thm)],[c_369]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(c_11,negated_conjecture,
% 35.19/5.04      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 35.19/5.04      inference(cnf_transformation,[],[f43]) ).
% 35.19/5.04  
% 35.19/5.04  cnf(contradiction,plain,
% 35.19/5.04      ( $false ),
% 35.19/5.04      inference(minisat,
% 35.19/5.04                [status(thm)],
% 35.19/5.04                [c_133555,c_56249,c_12251,c_11205,c_1735,c_1707,c_1450,
% 35.19/5.04                 c_384,c_11]) ).
% 35.19/5.04  
% 35.19/5.04  
% 35.19/5.04  % SZS output end CNFRefutation for theBenchmark.p
% 35.19/5.04  
% 35.19/5.04  ------                               Statistics
% 35.19/5.04  
% 35.19/5.04  ------ General
% 35.19/5.04  
% 35.19/5.04  abstr_ref_over_cycles:                  0
% 35.19/5.04  abstr_ref_under_cycles:                 0
% 35.19/5.04  gc_basic_clause_elim:                   0
% 35.19/5.04  forced_gc_time:                         0
% 35.19/5.04  parsing_time:                           0.01
% 35.19/5.04  unif_index_cands_time:                  0.
% 35.19/5.04  unif_index_add_time:                    0.
% 35.19/5.04  orderings_time:                         0.
% 35.19/5.04  out_proof_time:                         0.027
% 35.19/5.04  total_time:                             4.103
% 35.19/5.04  num_of_symbols:                         43
% 35.19/5.04  num_of_terms:                           170273
% 35.19/5.04  
% 35.19/5.04  ------ Preprocessing
% 35.19/5.04  
% 35.19/5.04  num_of_splits:                          0
% 35.19/5.04  num_of_split_atoms:                     0
% 35.19/5.04  num_of_reused_defs:                     0
% 35.19/5.04  num_eq_ax_congr_red:                    12
% 35.19/5.04  num_of_sem_filtered_clauses:            1
% 35.19/5.04  num_of_subtypes:                        0
% 35.19/5.04  monotx_restored_types:                  0
% 35.19/5.04  sat_num_of_epr_types:                   0
% 35.19/5.04  sat_num_of_non_cyclic_types:            0
% 35.19/5.04  sat_guarded_non_collapsed_types:        0
% 35.19/5.04  num_pure_diseq_elim:                    0
% 35.19/5.04  simp_replaced_by:                       0
% 35.19/5.04  res_preprocessed:                       74
% 35.19/5.04  prep_upred:                             0
% 35.19/5.04  prep_unflattend:                        2
% 35.19/5.04  smt_new_axioms:                         0
% 35.19/5.04  pred_elim_cands:                        2
% 35.19/5.04  pred_elim:                              1
% 35.19/5.04  pred_elim_cl:                           1
% 35.19/5.04  pred_elim_cycles:                       3
% 35.19/5.04  merged_defs:                            8
% 35.19/5.04  merged_defs_ncl:                        0
% 35.19/5.04  bin_hyper_res:                          10
% 35.19/5.04  prep_cycles:                            4
% 35.19/5.04  pred_elim_time:                         0.001
% 35.19/5.04  splitting_time:                         0.
% 35.19/5.04  sem_filter_time:                        0.
% 35.19/5.04  monotx_time:                            0.
% 35.19/5.04  subtype_inf_time:                       0.
% 35.19/5.04  
% 35.19/5.04  ------ Problem properties
% 35.19/5.04  
% 35.19/5.04  clauses:                                14
% 35.19/5.04  conjectures:                            3
% 35.19/5.04  epr:                                    0
% 35.19/5.04  horn:                                   14
% 35.19/5.04  ground:                                 3
% 35.19/5.04  unary:                                  5
% 35.19/5.04  binary:                                 6
% 35.19/5.04  lits:                                   27
% 35.19/5.04  lits_eq:                                2
% 35.19/5.04  fd_pure:                                0
% 35.19/5.04  fd_pseudo:                              0
% 35.19/5.04  fd_cond:                                0
% 35.19/5.04  fd_pseudo_cond:                         0
% 35.19/5.04  ac_symbols:                             0
% 35.19/5.04  
% 35.19/5.04  ------ Propositional Solver
% 35.19/5.04  
% 35.19/5.04  prop_solver_calls:                      67
% 35.19/5.04  prop_fast_solver_calls:                 1921
% 35.19/5.04  smt_solver_calls:                       0
% 35.19/5.04  smt_fast_solver_calls:                  0
% 35.19/5.04  prop_num_of_clauses:                    63003
% 35.19/5.04  prop_preprocess_simplified:             57459
% 35.19/5.04  prop_fo_subsumed:                       79
% 35.19/5.04  prop_solver_time:                       0.
% 35.19/5.04  smt_solver_time:                        0.
% 35.19/5.04  smt_fast_solver_time:                   0.
% 35.19/5.04  prop_fast_solver_time:                  0.
% 35.19/5.04  prop_unsat_core_time:                   0.008
% 35.19/5.04  
% 35.19/5.04  ------ QBF
% 35.19/5.04  
% 35.19/5.04  qbf_q_res:                              0
% 35.19/5.04  qbf_num_tautologies:                    0
% 35.19/5.04  qbf_prep_cycles:                        0
% 35.19/5.04  
% 35.19/5.04  ------ BMC1
% 35.19/5.04  
% 35.19/5.04  bmc1_current_bound:                     -1
% 35.19/5.04  bmc1_last_solved_bound:                 -1
% 35.19/5.04  bmc1_unsat_core_size:                   -1
% 35.19/5.04  bmc1_unsat_core_parents_size:           -1
% 35.19/5.04  bmc1_merge_next_fun:                    0
% 35.19/5.04  bmc1_unsat_core_clauses_time:           0.
% 35.19/5.04  
% 35.19/5.04  ------ Instantiation
% 35.19/5.04  
% 35.19/5.04  inst_num_of_clauses:                    480
% 35.19/5.04  inst_num_in_passive:                    215
% 35.19/5.04  inst_num_in_active:                     2958
% 35.19/5.04  inst_num_in_unprocessed:                1
% 35.19/5.04  inst_num_of_loops:                      3268
% 35.19/5.04  inst_num_of_learning_restarts:          1
% 35.19/5.04  inst_num_moves_active_passive:          300
% 35.19/5.04  inst_lit_activity:                      0
% 35.19/5.04  inst_lit_activity_moves:                5
% 35.19/5.04  inst_num_tautologies:                   0
% 35.19/5.04  inst_num_prop_implied:                  0
% 35.19/5.04  inst_num_existing_simplified:           0
% 35.19/5.04  inst_num_eq_res_simplified:             0
% 35.19/5.04  inst_num_child_elim:                    0
% 35.19/5.04  inst_num_of_dismatching_blockings:      30605
% 35.19/5.04  inst_num_of_non_proper_insts:           13252
% 35.19/5.04  inst_num_of_duplicates:                 0
% 35.19/5.04  inst_inst_num_from_inst_to_res:         0
% 35.19/5.04  inst_dismatching_checking_time:         0.
% 35.19/5.04  
% 35.19/5.04  ------ Resolution
% 35.19/5.04  
% 35.19/5.04  res_num_of_clauses:                     22
% 35.19/5.04  res_num_in_passive:                     22
% 35.19/5.04  res_num_in_active:                      0
% 35.19/5.04  res_num_of_loops:                       78
% 35.19/5.04  res_forward_subset_subsumed:            254
% 35.19/5.04  res_backward_subset_subsumed:           18
% 35.19/5.04  res_forward_subsumed:                   0
% 35.19/5.04  res_backward_subsumed:                  0
% 35.19/5.04  res_forward_subsumption_resolution:     0
% 35.19/5.04  res_backward_subsumption_resolution:    0
% 35.19/5.04  res_clause_to_clause_subsumption:       109574
% 35.19/5.04  res_orphan_elimination:                 0
% 35.19/5.04  res_tautology_del:                      127
% 35.19/5.04  res_num_eq_res_simplified:              0
% 35.19/5.04  res_num_sel_changes:                    0
% 35.19/5.04  res_moves_from_active_to_pass:          0
% 35.19/5.04  
% 35.19/5.04  ------ Superposition
% 35.19/5.04  
% 35.19/5.04  sup_time_total:                         0.
% 35.19/5.04  sup_time_generating:                    0.
% 35.19/5.04  sup_time_sim_full:                      0.
% 35.19/5.04  sup_time_sim_immed:                     0.
% 35.19/5.04  
% 35.19/5.04  sup_num_of_clauses:                     10767
% 35.19/5.04  sup_num_in_active:                      632
% 35.19/5.04  sup_num_in_passive:                     10135
% 35.19/5.04  sup_num_of_loops:                       652
% 35.19/5.04  sup_fw_superposition:                   7470
% 35.19/5.04  sup_bw_superposition:                   9255
% 35.19/5.04  sup_immediate_simplified:               3586
% 35.19/5.04  sup_given_eliminated:                   0
% 35.19/5.04  comparisons_done:                       0
% 35.19/5.04  comparisons_avoided:                    0
% 35.19/5.04  
% 35.19/5.04  ------ Simplifications
% 35.19/5.04  
% 35.19/5.04  
% 35.19/5.04  sim_fw_subset_subsumed:                 441
% 35.19/5.04  sim_bw_subset_subsumed:                 345
% 35.19/5.04  sim_fw_subsumed:                        653
% 35.19/5.04  sim_bw_subsumed:                        153
% 35.19/5.04  sim_fw_subsumption_res:                 0
% 35.19/5.04  sim_bw_subsumption_res:                 0
% 35.19/5.04  sim_tautology_del:                      205
% 35.19/5.04  sim_eq_tautology_del:                   489
% 35.19/5.04  sim_eq_res_simp:                        0
% 35.19/5.04  sim_fw_demodulated:                     1646
% 35.19/5.04  sim_bw_demodulated:                     12
% 35.19/5.04  sim_light_normalised:                   782
% 35.19/5.04  sim_joinable_taut:                      0
% 35.19/5.04  sim_joinable_simp:                      0
% 35.19/5.04  sim_ac_normalised:                      0
% 35.19/5.04  sim_smt_subsumption:                    0
% 35.19/5.04  
%------------------------------------------------------------------------------
