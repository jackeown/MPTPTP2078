%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:27 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 214 expanded)
%              Number of clauses        :   60 (  81 expanded)
%              Number of leaves         :   10 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  257 ( 784 expanded)
%              Number of equality atoms :   72 (  79 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0)
        & v1_tops_2(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0)
            & v1_tops_2(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f22,f21,f20])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_649,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_653,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1084,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_649,c_653])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_656,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_655,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2008,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_656,c_655])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_654,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_186,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_187,plain,
    ( ~ v1_tops_2(X0,sK0)
    | v1_tops_2(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_186])).

cnf(c_647,plain,
    ( v1_tops_2(X0,sK0) != iProver_top
    | v1_tops_2(X1,sK0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_1166,plain,
    ( v1_tops_2(X0,sK0) != iProver_top
    | v1_tops_2(X1,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_647])).

cnf(c_1568,plain,
    ( v1_tops_2(X0,sK0) = iProver_top
    | v1_tops_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_649,c_1166])).

cnf(c_11,negated_conjecture,
    ( v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,plain,
    ( v1_tops_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1736,plain,
    ( v1_tops_2(X0,sK0) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1568,c_18])).

cnf(c_8065,plain,
    ( v1_tops_2(k4_xboole_0(X0,X1),sK0) = iProver_top
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2008,c_1736])).

cnf(c_8989,plain,
    ( v1_tops_2(k4_xboole_0(sK1,X0),sK0) = iProver_top
    | r1_tarski(k4_xboole_0(sK1,X0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1084,c_8065])).

cnf(c_16,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_851,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_965,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_966,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_965])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1427,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1430,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1427])).

cnf(c_987,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1493,plain,
    ( r1_tarski(sK1,k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_987])).

cnf(c_1494,plain,
    ( r1_tarski(sK1,k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1493])).

cnf(c_863,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(k4_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1942,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_1943,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK1,k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1942])).

cnf(c_1308,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,sK1))
    | ~ r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2603,plain,
    ( r1_tarski(sK1,k2_xboole_0(X0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_2607,plain,
    ( r1_tarski(sK1,k2_xboole_0(X0,sK1)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2603])).

cnf(c_1125,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X0,k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3826,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1125])).

cnf(c_3829,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | r1_tarski(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3826])).

cnf(c_900,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,sK1))
    | r1_tarski(k4_xboole_0(X0,X1),sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4423,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),sK1)
    | ~ r1_tarski(sK1,k2_xboole_0(X0,sK1)) ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_4424,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),sK1) = iProver_top
    | r1_tarski(sK1,k2_xboole_0(X0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4423])).

cnf(c_734,plain,
    ( v1_tops_2(X0,sK0)
    | ~ v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_7880,plain,
    ( v1_tops_2(k4_xboole_0(sK1,X0),sK0)
    | ~ v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_7881,plain,
    ( v1_tops_2(k4_xboole_0(sK1,X0),sK0) = iProver_top
    | v1_tops_2(sK1,sK0) != iProver_top
    | m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(k4_xboole_0(sK1,X0),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7880])).

cnf(c_9214,plain,
    ( v1_tops_2(k4_xboole_0(sK1,X0),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8989,c_16,c_18,c_966,c_1430,c_1494,c_1943,c_2607,c_3829,c_4424,c_7881])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_106,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_107,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_106])).

cnf(c_131,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_107])).

cnf(c_648,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_131])).

cnf(c_8497,plain,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1084,c_648])).

cnf(c_10,negated_conjecture,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_652,plain,
    ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8870,plain,
    ( v1_tops_2(k4_xboole_0(sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8497,c_652])).

cnf(c_9221,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_9214,c_8870])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.36/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/0.98  
% 3.36/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/0.98  
% 3.36/0.98  ------  iProver source info
% 3.36/0.98  
% 3.36/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.36/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/0.98  git: non_committed_changes: false
% 3.36/0.98  git: last_make_outside_of_git: false
% 3.36/0.98  
% 3.36/0.98  ------ 
% 3.36/0.98  
% 3.36/0.98  ------ Input Options
% 3.36/0.98  
% 3.36/0.98  --out_options                           all
% 3.36/0.98  --tptp_safe_out                         true
% 3.36/0.98  --problem_path                          ""
% 3.36/0.98  --include_path                          ""
% 3.36/0.98  --clausifier                            res/vclausify_rel
% 3.36/0.98  --clausifier_options                    --mode clausify
% 3.36/0.98  --stdin                                 false
% 3.36/0.98  --stats_out                             all
% 3.36/0.98  
% 3.36/0.98  ------ General Options
% 3.36/0.98  
% 3.36/0.98  --fof                                   false
% 3.36/0.98  --time_out_real                         305.
% 3.36/0.98  --time_out_virtual                      -1.
% 3.36/0.98  --symbol_type_check                     false
% 3.36/0.98  --clausify_out                          false
% 3.36/0.98  --sig_cnt_out                           false
% 3.36/0.98  --trig_cnt_out                          false
% 3.36/0.98  --trig_cnt_out_tolerance                1.
% 3.36/0.98  --trig_cnt_out_sk_spl                   false
% 3.36/0.98  --abstr_cl_out                          false
% 3.36/0.98  
% 3.36/0.98  ------ Global Options
% 3.36/0.98  
% 3.36/0.98  --schedule                              default
% 3.36/0.98  --add_important_lit                     false
% 3.36/0.98  --prop_solver_per_cl                    1000
% 3.36/0.98  --min_unsat_core                        false
% 3.36/0.98  --soft_assumptions                      false
% 3.36/0.98  --soft_lemma_size                       3
% 3.36/0.98  --prop_impl_unit_size                   0
% 3.36/0.98  --prop_impl_unit                        []
% 3.36/0.98  --share_sel_clauses                     true
% 3.36/0.98  --reset_solvers                         false
% 3.36/0.98  --bc_imp_inh                            [conj_cone]
% 3.36/0.98  --conj_cone_tolerance                   3.
% 3.36/0.98  --extra_neg_conj                        none
% 3.36/0.98  --large_theory_mode                     true
% 3.36/0.98  --prolific_symb_bound                   200
% 3.36/0.98  --lt_threshold                          2000
% 3.36/0.98  --clause_weak_htbl                      true
% 3.36/0.98  --gc_record_bc_elim                     false
% 3.36/0.98  
% 3.36/0.98  ------ Preprocessing Options
% 3.36/0.98  
% 3.36/0.98  --preprocessing_flag                    true
% 3.36/0.98  --time_out_prep_mult                    0.1
% 3.36/0.98  --splitting_mode                        input
% 3.36/0.98  --splitting_grd                         true
% 3.36/0.98  --splitting_cvd                         false
% 3.36/0.98  --splitting_cvd_svl                     false
% 3.36/0.98  --splitting_nvd                         32
% 3.36/0.98  --sub_typing                            true
% 3.36/0.98  --prep_gs_sim                           true
% 3.36/0.98  --prep_unflatten                        true
% 3.36/0.98  --prep_res_sim                          true
% 3.36/0.98  --prep_upred                            true
% 3.36/0.98  --prep_sem_filter                       exhaustive
% 3.36/0.98  --prep_sem_filter_out                   false
% 3.36/0.98  --pred_elim                             true
% 3.36/0.98  --res_sim_input                         true
% 3.36/0.98  --eq_ax_congr_red                       true
% 3.36/0.98  --pure_diseq_elim                       true
% 3.36/0.98  --brand_transform                       false
% 3.36/0.98  --non_eq_to_eq                          false
% 3.36/0.98  --prep_def_merge                        true
% 3.36/0.98  --prep_def_merge_prop_impl              false
% 3.36/0.98  --prep_def_merge_mbd                    true
% 3.36/0.98  --prep_def_merge_tr_red                 false
% 3.36/0.98  --prep_def_merge_tr_cl                  false
% 3.36/0.98  --smt_preprocessing                     true
% 3.36/0.98  --smt_ac_axioms                         fast
% 3.36/0.98  --preprocessed_out                      false
% 3.36/0.98  --preprocessed_stats                    false
% 3.36/0.98  
% 3.36/0.98  ------ Abstraction refinement Options
% 3.36/0.98  
% 3.36/0.98  --abstr_ref                             []
% 3.36/0.98  --abstr_ref_prep                        false
% 3.36/0.98  --abstr_ref_until_sat                   false
% 3.36/0.98  --abstr_ref_sig_restrict                funpre
% 3.36/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/0.98  --abstr_ref_under                       []
% 3.36/0.98  
% 3.36/0.98  ------ SAT Options
% 3.36/0.98  
% 3.36/0.98  --sat_mode                              false
% 3.36/0.98  --sat_fm_restart_options                ""
% 3.36/0.98  --sat_gr_def                            false
% 3.36/0.98  --sat_epr_types                         true
% 3.36/0.98  --sat_non_cyclic_types                  false
% 3.36/0.98  --sat_finite_models                     false
% 3.36/0.98  --sat_fm_lemmas                         false
% 3.36/0.98  --sat_fm_prep                           false
% 3.36/0.98  --sat_fm_uc_incr                        true
% 3.36/0.98  --sat_out_model                         small
% 3.36/0.98  --sat_out_clauses                       false
% 3.36/0.98  
% 3.36/0.98  ------ QBF Options
% 3.36/0.98  
% 3.36/0.98  --qbf_mode                              false
% 3.36/0.98  --qbf_elim_univ                         false
% 3.36/0.98  --qbf_dom_inst                          none
% 3.36/0.98  --qbf_dom_pre_inst                      false
% 3.36/0.98  --qbf_sk_in                             false
% 3.36/0.98  --qbf_pred_elim                         true
% 3.36/0.98  --qbf_split                             512
% 3.36/0.98  
% 3.36/0.98  ------ BMC1 Options
% 3.36/0.98  
% 3.36/0.98  --bmc1_incremental                      false
% 3.36/0.98  --bmc1_axioms                           reachable_all
% 3.36/0.98  --bmc1_min_bound                        0
% 3.36/0.98  --bmc1_max_bound                        -1
% 3.36/0.98  --bmc1_max_bound_default                -1
% 3.36/0.98  --bmc1_symbol_reachability              true
% 3.36/0.98  --bmc1_property_lemmas                  false
% 3.36/0.98  --bmc1_k_induction                      false
% 3.36/0.98  --bmc1_non_equiv_states                 false
% 3.36/0.98  --bmc1_deadlock                         false
% 3.36/0.98  --bmc1_ucm                              false
% 3.36/0.98  --bmc1_add_unsat_core                   none
% 3.36/0.98  --bmc1_unsat_core_children              false
% 3.36/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/0.98  --bmc1_out_stat                         full
% 3.36/0.98  --bmc1_ground_init                      false
% 3.36/0.98  --bmc1_pre_inst_next_state              false
% 3.36/0.98  --bmc1_pre_inst_state                   false
% 3.36/0.98  --bmc1_pre_inst_reach_state             false
% 3.36/0.98  --bmc1_out_unsat_core                   false
% 3.36/0.98  --bmc1_aig_witness_out                  false
% 3.36/0.98  --bmc1_verbose                          false
% 3.36/0.98  --bmc1_dump_clauses_tptp                false
% 3.36/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.36/0.98  --bmc1_dump_file                        -
% 3.36/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.36/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.36/0.98  --bmc1_ucm_extend_mode                  1
% 3.36/0.98  --bmc1_ucm_init_mode                    2
% 3.36/0.98  --bmc1_ucm_cone_mode                    none
% 3.36/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.36/0.98  --bmc1_ucm_relax_model                  4
% 3.36/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.36/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/0.98  --bmc1_ucm_layered_model                none
% 3.36/0.98  --bmc1_ucm_max_lemma_size               10
% 3.36/0.98  
% 3.36/0.98  ------ AIG Options
% 3.36/0.98  
% 3.36/0.98  --aig_mode                              false
% 3.36/0.98  
% 3.36/0.98  ------ Instantiation Options
% 3.36/0.98  
% 3.36/0.98  --instantiation_flag                    true
% 3.36/0.98  --inst_sos_flag                         false
% 3.36/0.98  --inst_sos_phase                        true
% 3.36/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/0.98  --inst_lit_sel_side                     num_symb
% 3.36/0.98  --inst_solver_per_active                1400
% 3.36/0.98  --inst_solver_calls_frac                1.
% 3.36/0.98  --inst_passive_queue_type               priority_queues
% 3.36/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/0.98  --inst_passive_queues_freq              [25;2]
% 3.36/0.98  --inst_dismatching                      true
% 3.36/0.98  --inst_eager_unprocessed_to_passive     true
% 3.36/0.98  --inst_prop_sim_given                   true
% 3.36/0.98  --inst_prop_sim_new                     false
% 3.36/0.98  --inst_subs_new                         false
% 3.36/0.98  --inst_eq_res_simp                      false
% 3.36/0.98  --inst_subs_given                       false
% 3.36/0.98  --inst_orphan_elimination               true
% 3.36/0.98  --inst_learning_loop_flag               true
% 3.36/0.98  --inst_learning_start                   3000
% 3.36/0.98  --inst_learning_factor                  2
% 3.36/0.98  --inst_start_prop_sim_after_learn       3
% 3.36/0.98  --inst_sel_renew                        solver
% 3.36/0.98  --inst_lit_activity_flag                true
% 3.36/0.98  --inst_restr_to_given                   false
% 3.36/0.98  --inst_activity_threshold               500
% 3.36/0.98  --inst_out_proof                        true
% 3.36/0.98  
% 3.36/0.98  ------ Resolution Options
% 3.36/0.98  
% 3.36/0.98  --resolution_flag                       true
% 3.36/0.98  --res_lit_sel                           adaptive
% 3.36/0.98  --res_lit_sel_side                      none
% 3.36/0.98  --res_ordering                          kbo
% 3.36/0.98  --res_to_prop_solver                    active
% 3.36/0.98  --res_prop_simpl_new                    false
% 3.36/0.98  --res_prop_simpl_given                  true
% 3.36/0.98  --res_passive_queue_type                priority_queues
% 3.36/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/0.98  --res_passive_queues_freq               [15;5]
% 3.36/0.98  --res_forward_subs                      full
% 3.36/0.98  --res_backward_subs                     full
% 3.36/0.98  --res_forward_subs_resolution           true
% 3.36/0.98  --res_backward_subs_resolution          true
% 3.36/0.98  --res_orphan_elimination                true
% 3.36/0.98  --res_time_limit                        2.
% 3.36/0.98  --res_out_proof                         true
% 3.36/0.98  
% 3.36/0.98  ------ Superposition Options
% 3.36/0.98  
% 3.36/0.98  --superposition_flag                    true
% 3.36/0.98  --sup_passive_queue_type                priority_queues
% 3.36/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.36/0.98  --demod_completeness_check              fast
% 3.36/0.98  --demod_use_ground                      true
% 3.36/0.98  --sup_to_prop_solver                    passive
% 3.36/0.98  --sup_prop_simpl_new                    true
% 3.36/0.98  --sup_prop_simpl_given                  true
% 3.36/0.98  --sup_fun_splitting                     false
% 3.36/0.98  --sup_smt_interval                      50000
% 3.36/0.98  
% 3.36/0.98  ------ Superposition Simplification Setup
% 3.36/0.98  
% 3.36/0.98  --sup_indices_passive                   []
% 3.36/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.98  --sup_full_bw                           [BwDemod]
% 3.36/0.98  --sup_immed_triv                        [TrivRules]
% 3.36/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.98  --sup_immed_bw_main                     []
% 3.36/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.98  
% 3.36/0.98  ------ Combination Options
% 3.36/0.98  
% 3.36/0.98  --comb_res_mult                         3
% 3.36/0.98  --comb_sup_mult                         2
% 3.36/0.98  --comb_inst_mult                        10
% 3.36/0.98  
% 3.36/0.98  ------ Debug Options
% 3.36/0.98  
% 3.36/0.98  --dbg_backtrace                         false
% 3.36/0.98  --dbg_dump_prop_clauses                 false
% 3.36/0.98  --dbg_dump_prop_clauses_file            -
% 3.36/0.98  --dbg_out_stat                          false
% 3.36/0.98  ------ Parsing...
% 3.36/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/0.98  
% 3.36/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.36/0.98  
% 3.36/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/0.98  
% 3.36/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/0.98  ------ Proving...
% 3.36/0.98  ------ Problem Properties 
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  clauses                                 13
% 3.36/0.98  conjectures                             4
% 3.36/0.98  EPR                                     3
% 3.36/0.98  Horn                                    13
% 3.36/0.98  unary                                   6
% 3.36/0.98  binary                                  5
% 3.36/0.98  lits                                    24
% 3.36/0.98  lits eq                                 3
% 3.36/0.98  fd_pure                                 0
% 3.36/0.98  fd_pseudo                               0
% 3.36/0.98  fd_cond                                 0
% 3.36/0.98  fd_pseudo_cond                          1
% 3.36/0.98  AC symbols                              0
% 3.36/0.98  
% 3.36/0.98  ------ Schedule dynamic 5 is on 
% 3.36/0.98  
% 3.36/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  ------ 
% 3.36/0.98  Current options:
% 3.36/0.98  ------ 
% 3.36/0.98  
% 3.36/0.98  ------ Input Options
% 3.36/0.98  
% 3.36/0.98  --out_options                           all
% 3.36/0.98  --tptp_safe_out                         true
% 3.36/0.98  --problem_path                          ""
% 3.36/0.98  --include_path                          ""
% 3.36/0.98  --clausifier                            res/vclausify_rel
% 3.36/0.98  --clausifier_options                    --mode clausify
% 3.36/0.98  --stdin                                 false
% 3.36/0.98  --stats_out                             all
% 3.36/0.98  
% 3.36/0.98  ------ General Options
% 3.36/0.98  
% 3.36/0.98  --fof                                   false
% 3.36/0.98  --time_out_real                         305.
% 3.36/0.98  --time_out_virtual                      -1.
% 3.36/0.98  --symbol_type_check                     false
% 3.36/0.98  --clausify_out                          false
% 3.36/0.98  --sig_cnt_out                           false
% 3.36/0.98  --trig_cnt_out                          false
% 3.36/0.98  --trig_cnt_out_tolerance                1.
% 3.36/0.98  --trig_cnt_out_sk_spl                   false
% 3.36/0.98  --abstr_cl_out                          false
% 3.36/0.98  
% 3.36/0.98  ------ Global Options
% 3.36/0.98  
% 3.36/0.98  --schedule                              default
% 3.36/0.98  --add_important_lit                     false
% 3.36/0.98  --prop_solver_per_cl                    1000
% 3.36/0.98  --min_unsat_core                        false
% 3.36/0.98  --soft_assumptions                      false
% 3.36/0.98  --soft_lemma_size                       3
% 3.36/0.98  --prop_impl_unit_size                   0
% 3.36/0.98  --prop_impl_unit                        []
% 3.36/0.98  --share_sel_clauses                     true
% 3.36/0.98  --reset_solvers                         false
% 3.36/0.98  --bc_imp_inh                            [conj_cone]
% 3.36/0.98  --conj_cone_tolerance                   3.
% 3.36/0.98  --extra_neg_conj                        none
% 3.36/0.98  --large_theory_mode                     true
% 3.36/0.98  --prolific_symb_bound                   200
% 3.36/0.98  --lt_threshold                          2000
% 3.36/0.98  --clause_weak_htbl                      true
% 3.36/0.98  --gc_record_bc_elim                     false
% 3.36/0.98  
% 3.36/0.98  ------ Preprocessing Options
% 3.36/0.98  
% 3.36/0.98  --preprocessing_flag                    true
% 3.36/0.98  --time_out_prep_mult                    0.1
% 3.36/0.98  --splitting_mode                        input
% 3.36/0.98  --splitting_grd                         true
% 3.36/0.98  --splitting_cvd                         false
% 3.36/0.98  --splitting_cvd_svl                     false
% 3.36/0.98  --splitting_nvd                         32
% 3.36/0.98  --sub_typing                            true
% 3.36/0.98  --prep_gs_sim                           true
% 3.36/0.98  --prep_unflatten                        true
% 3.36/0.98  --prep_res_sim                          true
% 3.36/0.98  --prep_upred                            true
% 3.36/0.98  --prep_sem_filter                       exhaustive
% 3.36/0.98  --prep_sem_filter_out                   false
% 3.36/0.98  --pred_elim                             true
% 3.36/0.98  --res_sim_input                         true
% 3.36/0.98  --eq_ax_congr_red                       true
% 3.36/0.98  --pure_diseq_elim                       true
% 3.36/0.98  --brand_transform                       false
% 3.36/0.98  --non_eq_to_eq                          false
% 3.36/0.98  --prep_def_merge                        true
% 3.36/0.98  --prep_def_merge_prop_impl              false
% 3.36/0.98  --prep_def_merge_mbd                    true
% 3.36/0.98  --prep_def_merge_tr_red                 false
% 3.36/0.98  --prep_def_merge_tr_cl                  false
% 3.36/0.98  --smt_preprocessing                     true
% 3.36/0.98  --smt_ac_axioms                         fast
% 3.36/0.98  --preprocessed_out                      false
% 3.36/0.98  --preprocessed_stats                    false
% 3.36/0.98  
% 3.36/0.98  ------ Abstraction refinement Options
% 3.36/0.98  
% 3.36/0.98  --abstr_ref                             []
% 3.36/0.98  --abstr_ref_prep                        false
% 3.36/0.98  --abstr_ref_until_sat                   false
% 3.36/0.98  --abstr_ref_sig_restrict                funpre
% 3.36/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/0.98  --abstr_ref_under                       []
% 3.36/0.98  
% 3.36/0.98  ------ SAT Options
% 3.36/0.98  
% 3.36/0.98  --sat_mode                              false
% 3.36/0.98  --sat_fm_restart_options                ""
% 3.36/0.98  --sat_gr_def                            false
% 3.36/0.98  --sat_epr_types                         true
% 3.36/0.98  --sat_non_cyclic_types                  false
% 3.36/0.98  --sat_finite_models                     false
% 3.36/0.98  --sat_fm_lemmas                         false
% 3.36/0.98  --sat_fm_prep                           false
% 3.36/0.98  --sat_fm_uc_incr                        true
% 3.36/0.98  --sat_out_model                         small
% 3.36/0.98  --sat_out_clauses                       false
% 3.36/0.98  
% 3.36/0.98  ------ QBF Options
% 3.36/0.98  
% 3.36/0.98  --qbf_mode                              false
% 3.36/0.98  --qbf_elim_univ                         false
% 3.36/0.98  --qbf_dom_inst                          none
% 3.36/0.98  --qbf_dom_pre_inst                      false
% 3.36/0.98  --qbf_sk_in                             false
% 3.36/0.98  --qbf_pred_elim                         true
% 3.36/0.98  --qbf_split                             512
% 3.36/0.98  
% 3.36/0.98  ------ BMC1 Options
% 3.36/0.98  
% 3.36/0.98  --bmc1_incremental                      false
% 3.36/0.98  --bmc1_axioms                           reachable_all
% 3.36/0.98  --bmc1_min_bound                        0
% 3.36/0.98  --bmc1_max_bound                        -1
% 3.36/0.98  --bmc1_max_bound_default                -1
% 3.36/0.98  --bmc1_symbol_reachability              true
% 3.36/0.98  --bmc1_property_lemmas                  false
% 3.36/0.98  --bmc1_k_induction                      false
% 3.36/0.98  --bmc1_non_equiv_states                 false
% 3.36/0.98  --bmc1_deadlock                         false
% 3.36/0.98  --bmc1_ucm                              false
% 3.36/0.98  --bmc1_add_unsat_core                   none
% 3.36/0.98  --bmc1_unsat_core_children              false
% 3.36/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/0.98  --bmc1_out_stat                         full
% 3.36/0.98  --bmc1_ground_init                      false
% 3.36/0.98  --bmc1_pre_inst_next_state              false
% 3.36/0.98  --bmc1_pre_inst_state                   false
% 3.36/0.98  --bmc1_pre_inst_reach_state             false
% 3.36/0.98  --bmc1_out_unsat_core                   false
% 3.36/0.98  --bmc1_aig_witness_out                  false
% 3.36/0.98  --bmc1_verbose                          false
% 3.36/0.98  --bmc1_dump_clauses_tptp                false
% 3.36/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.36/0.98  --bmc1_dump_file                        -
% 3.36/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.36/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.36/0.98  --bmc1_ucm_extend_mode                  1
% 3.36/0.98  --bmc1_ucm_init_mode                    2
% 3.36/0.98  --bmc1_ucm_cone_mode                    none
% 3.36/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.36/0.98  --bmc1_ucm_relax_model                  4
% 3.36/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.36/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/0.98  --bmc1_ucm_layered_model                none
% 3.36/0.98  --bmc1_ucm_max_lemma_size               10
% 3.36/0.98  
% 3.36/0.98  ------ AIG Options
% 3.36/0.98  
% 3.36/0.98  --aig_mode                              false
% 3.36/0.98  
% 3.36/0.98  ------ Instantiation Options
% 3.36/0.98  
% 3.36/0.98  --instantiation_flag                    true
% 3.36/0.98  --inst_sos_flag                         false
% 3.36/0.98  --inst_sos_phase                        true
% 3.36/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/0.98  --inst_lit_sel_side                     none
% 3.36/0.98  --inst_solver_per_active                1400
% 3.36/0.98  --inst_solver_calls_frac                1.
% 3.36/0.98  --inst_passive_queue_type               priority_queues
% 3.36/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/0.98  --inst_passive_queues_freq              [25;2]
% 3.36/0.98  --inst_dismatching                      true
% 3.36/0.98  --inst_eager_unprocessed_to_passive     true
% 3.36/0.98  --inst_prop_sim_given                   true
% 3.36/0.98  --inst_prop_sim_new                     false
% 3.36/0.98  --inst_subs_new                         false
% 3.36/0.98  --inst_eq_res_simp                      false
% 3.36/0.98  --inst_subs_given                       false
% 3.36/0.98  --inst_orphan_elimination               true
% 3.36/0.98  --inst_learning_loop_flag               true
% 3.36/0.98  --inst_learning_start                   3000
% 3.36/0.98  --inst_learning_factor                  2
% 3.36/0.98  --inst_start_prop_sim_after_learn       3
% 3.36/0.98  --inst_sel_renew                        solver
% 3.36/0.98  --inst_lit_activity_flag                true
% 3.36/0.98  --inst_restr_to_given                   false
% 3.36/0.98  --inst_activity_threshold               500
% 3.36/0.98  --inst_out_proof                        true
% 3.36/0.98  
% 3.36/0.98  ------ Resolution Options
% 3.36/0.98  
% 3.36/0.98  --resolution_flag                       false
% 3.36/0.98  --res_lit_sel                           adaptive
% 3.36/0.98  --res_lit_sel_side                      none
% 3.36/0.98  --res_ordering                          kbo
% 3.36/0.98  --res_to_prop_solver                    active
% 3.36/0.98  --res_prop_simpl_new                    false
% 3.36/0.98  --res_prop_simpl_given                  true
% 3.36/0.98  --res_passive_queue_type                priority_queues
% 3.36/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/0.98  --res_passive_queues_freq               [15;5]
% 3.36/0.98  --res_forward_subs                      full
% 3.36/0.98  --res_backward_subs                     full
% 3.36/0.98  --res_forward_subs_resolution           true
% 3.36/0.98  --res_backward_subs_resolution          true
% 3.36/0.98  --res_orphan_elimination                true
% 3.36/0.98  --res_time_limit                        2.
% 3.36/0.98  --res_out_proof                         true
% 3.36/0.98  
% 3.36/0.98  ------ Superposition Options
% 3.36/0.98  
% 3.36/0.98  --superposition_flag                    true
% 3.36/0.98  --sup_passive_queue_type                priority_queues
% 3.36/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.36/0.98  --demod_completeness_check              fast
% 3.36/0.98  --demod_use_ground                      true
% 3.36/0.98  --sup_to_prop_solver                    passive
% 3.36/0.98  --sup_prop_simpl_new                    true
% 3.36/0.98  --sup_prop_simpl_given                  true
% 3.36/0.98  --sup_fun_splitting                     false
% 3.36/0.98  --sup_smt_interval                      50000
% 3.36/0.98  
% 3.36/0.98  ------ Superposition Simplification Setup
% 3.36/0.98  
% 3.36/0.98  --sup_indices_passive                   []
% 3.36/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.98  --sup_full_bw                           [BwDemod]
% 3.36/0.98  --sup_immed_triv                        [TrivRules]
% 3.36/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.98  --sup_immed_bw_main                     []
% 3.36/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/0.98  
% 3.36/0.98  ------ Combination Options
% 3.36/0.98  
% 3.36/0.98  --comb_res_mult                         3
% 3.36/0.98  --comb_sup_mult                         2
% 3.36/0.98  --comb_inst_mult                        10
% 3.36/0.98  
% 3.36/0.98  ------ Debug Options
% 3.36/0.98  
% 3.36/0.98  --dbg_backtrace                         false
% 3.36/0.98  --dbg_dump_prop_clauses                 false
% 3.36/0.98  --dbg_dump_prop_clauses_file            -
% 3.36/0.98  --dbg_out_stat                          false
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  ------ Proving...
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  % SZS status Theorem for theBenchmark.p
% 3.36/0.98  
% 3.36/0.98   Resolution empty clause
% 3.36/0.98  
% 3.36/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/0.98  
% 3.36/0.98  fof(f8,conjecture,(
% 3.36/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 3.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f9,negated_conjecture,(
% 3.36/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 3.36/0.98    inference(negated_conjecture,[],[f8])).
% 3.36/0.98  
% 3.36/0.98  fof(f15,plain,(
% 3.36/0.98    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 3.36/0.98    inference(ennf_transformation,[],[f9])).
% 3.36/0.98  
% 3.36/0.98  fof(f16,plain,(
% 3.36/0.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 3.36/0.98    inference(flattening,[],[f15])).
% 3.36/0.98  
% 3.36/0.98  fof(f22,plain,(
% 3.36/0.98    ( ! [X0,X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0) & v1_tops_2(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.36/0.98    introduced(choice_axiom,[])).
% 3.36/0.98  
% 3.36/0.98  fof(f21,plain,(
% 3.36/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0) & v1_tops_2(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 3.36/0.98    introduced(choice_axiom,[])).
% 3.36/0.98  
% 3.36/0.98  fof(f20,plain,(
% 3.36/0.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 3.36/0.98    introduced(choice_axiom,[])).
% 3.36/0.98  
% 3.36/0.98  fof(f23,plain,(
% 3.36/0.98    ((~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 3.36/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f22,f21,f20])).
% 3.36/0.98  
% 3.36/0.98  fof(f35,plain,(
% 3.36/0.98    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.36/0.98    inference(cnf_transformation,[],[f23])).
% 3.36/0.98  
% 3.36/0.98  fof(f6,axiom,(
% 3.36/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f19,plain,(
% 3.36/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.36/0.98    inference(nnf_transformation,[],[f6])).
% 3.36/0.98  
% 3.36/0.98  fof(f31,plain,(
% 3.36/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.36/0.98    inference(cnf_transformation,[],[f19])).
% 3.36/0.98  
% 3.36/0.98  fof(f2,axiom,(
% 3.36/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f10,plain,(
% 3.36/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.36/0.98    inference(ennf_transformation,[],[f2])).
% 3.36/0.98  
% 3.36/0.98  fof(f27,plain,(
% 3.36/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f10])).
% 3.36/0.98  
% 3.36/0.98  fof(f3,axiom,(
% 3.36/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f11,plain,(
% 3.36/0.98    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.36/0.98    inference(ennf_transformation,[],[f3])).
% 3.36/0.98  
% 3.36/0.98  fof(f28,plain,(
% 3.36/0.98    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.36/0.98    inference(cnf_transformation,[],[f11])).
% 3.36/0.98  
% 3.36/0.98  fof(f32,plain,(
% 3.36/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f19])).
% 3.36/0.98  
% 3.36/0.98  fof(f7,axiom,(
% 3.36/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 3.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f13,plain,(
% 3.36/0.98    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.36/0.98    inference(ennf_transformation,[],[f7])).
% 3.36/0.98  
% 3.36/0.98  fof(f14,plain,(
% 3.36/0.98    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 3.36/0.98    inference(flattening,[],[f13])).
% 3.36/0.98  
% 3.36/0.98  fof(f33,plain,(
% 3.36/0.98    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.36/0.98    inference(cnf_transformation,[],[f14])).
% 3.36/0.98  
% 3.36/0.98  fof(f34,plain,(
% 3.36/0.98    l1_pre_topc(sK0)),
% 3.36/0.98    inference(cnf_transformation,[],[f23])).
% 3.36/0.98  
% 3.36/0.98  fof(f37,plain,(
% 3.36/0.98    v1_tops_2(sK1,sK0)),
% 3.36/0.98    inference(cnf_transformation,[],[f23])).
% 3.36/0.98  
% 3.36/0.98  fof(f1,axiom,(
% 3.36/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f17,plain,(
% 3.36/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.36/0.98    inference(nnf_transformation,[],[f1])).
% 3.36/0.98  
% 3.36/0.98  fof(f18,plain,(
% 3.36/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.36/0.98    inference(flattening,[],[f17])).
% 3.36/0.98  
% 3.36/0.98  fof(f24,plain,(
% 3.36/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.36/0.98    inference(cnf_transformation,[],[f18])).
% 3.36/0.98  
% 3.36/0.98  fof(f40,plain,(
% 3.36/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.36/0.98    inference(equality_resolution,[],[f24])).
% 3.36/0.98  
% 3.36/0.98  fof(f5,axiom,(
% 3.36/0.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.36/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/0.98  
% 3.36/0.98  fof(f12,plain,(
% 3.36/0.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.36/0.98    inference(ennf_transformation,[],[f5])).
% 3.36/0.98  
% 3.36/0.98  fof(f30,plain,(
% 3.36/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.36/0.98    inference(cnf_transformation,[],[f12])).
% 3.36/0.98  
% 3.36/0.98  fof(f38,plain,(
% 3.36/0.98    ~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 3.36/0.98    inference(cnf_transformation,[],[f23])).
% 3.36/0.98  
% 3.36/0.98  cnf(c_13,negated_conjecture,
% 3.36/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 3.36/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_649,plain,
% 3.36/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_8,plain,
% 3.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.36/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_653,plain,
% 3.36/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.36/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1084,plain,
% 3.36/0.98      ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_649,c_653]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3,plain,
% 3.36/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 3.36/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_656,plain,
% 3.36/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.36/0.98      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_4,plain,
% 3.36/0.98      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 3.36/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_655,plain,
% 3.36/0.98      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 3.36/0.98      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2008,plain,
% 3.36/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.36/0.98      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_656,c_655]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_7,plain,
% 3.36/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.36/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_654,plain,
% 3.36/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.36/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_9,plain,
% 3.36/0.98      ( ~ v1_tops_2(X0,X1)
% 3.36/0.98      | v1_tops_2(X2,X1)
% 3.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.36/0.98      | ~ r1_tarski(X2,X0)
% 3.36/0.98      | ~ l1_pre_topc(X1) ),
% 3.36/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_14,negated_conjecture,
% 3.36/0.98      ( l1_pre_topc(sK0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_186,plain,
% 3.36/0.98      ( ~ v1_tops_2(X0,X1)
% 3.36/0.98      | v1_tops_2(X2,X1)
% 3.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.36/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.36/0.98      | ~ r1_tarski(X2,X0)
% 3.36/0.98      | sK0 != X1 ),
% 3.36/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_187,plain,
% 3.36/0.98      ( ~ v1_tops_2(X0,sK0)
% 3.36/0.98      | v1_tops_2(X1,sK0)
% 3.36/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.36/0.98      | ~ r1_tarski(X1,X0) ),
% 3.36/0.98      inference(unflattening,[status(thm)],[c_186]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_647,plain,
% 3.36/0.98      ( v1_tops_2(X0,sK0) != iProver_top
% 3.36/0.98      | v1_tops_2(X1,sK0) = iProver_top
% 3.36/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.36/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.36/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1166,plain,
% 3.36/0.98      ( v1_tops_2(X0,sK0) != iProver_top
% 3.36/0.98      | v1_tops_2(X1,sK0) = iProver_top
% 3.36/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.36/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.36/0.98      | r1_tarski(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_654,c_647]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1568,plain,
% 3.36/0.98      ( v1_tops_2(X0,sK0) = iProver_top
% 3.36/0.98      | v1_tops_2(sK1,sK0) != iProver_top
% 3.36/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.36/0.98      | r1_tarski(X0,sK1) != iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_649,c_1166]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_11,negated_conjecture,
% 3.36/0.98      ( v1_tops_2(sK1,sK0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_18,plain,
% 3.36/0.98      ( v1_tops_2(sK1,sK0) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1736,plain,
% 3.36/0.98      ( v1_tops_2(X0,sK0) = iProver_top
% 3.36/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.36/0.98      | r1_tarski(X0,sK1) != iProver_top ),
% 3.36/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1568,c_18]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_8065,plain,
% 3.36/0.98      ( v1_tops_2(k4_xboole_0(X0,X1),sK0) = iProver_top
% 3.36/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.36/0.98      | r1_tarski(k4_xboole_0(X0,X1),sK1) != iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_2008,c_1736]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_8989,plain,
% 3.36/0.98      ( v1_tops_2(k4_xboole_0(sK1,X0),sK0) = iProver_top
% 3.36/0.98      | r1_tarski(k4_xboole_0(sK1,X0),sK1) != iProver_top ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_1084,c_8065]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_16,plain,
% 3.36/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_851,plain,
% 3.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.36/0.98      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_965,plain,
% 3.36/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.36/0.98      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_851]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_966,plain,
% 3.36/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.36/0.98      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_965]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f40]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1427,plain,
% 3.36/0.98      ( r1_tarski(sK1,sK1) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1430,plain,
% 3.36/0.98      ( r1_tarski(sK1,sK1) = iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_1427]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_987,plain,
% 3.36/0.98      ( r1_tarski(X0,k2_xboole_0(X1,k1_zfmisc_1(u1_struct_0(sK0))))
% 3.36/0.98      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1493,plain,
% 3.36/0.98      ( r1_tarski(sK1,k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK0))))
% 3.36/0.98      | ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_987]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1494,plain,
% 3.36/0.98      ( r1_tarski(sK1,k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.36/0.98      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_1493]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_863,plain,
% 3.36/0.98      ( ~ r1_tarski(X0,k2_xboole_0(X1,k1_zfmisc_1(u1_struct_0(sK0))))
% 3.36/0.98      | r1_tarski(k4_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1942,plain,
% 3.36/0.98      ( r1_tarski(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.36/0.98      | ~ r1_tarski(sK1,k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_863]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1943,plain,
% 3.36/0.98      ( r1_tarski(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.36/0.98      | r1_tarski(sK1,k2_xboole_0(X0,k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_1942]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1308,plain,
% 3.36/0.98      ( r1_tarski(X0,k2_xboole_0(X1,sK1)) | ~ r1_tarski(X0,sK1) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2603,plain,
% 3.36/0.98      ( r1_tarski(sK1,k2_xboole_0(X0,sK1)) | ~ r1_tarski(sK1,sK1) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_1308]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_2607,plain,
% 3.36/0.98      ( r1_tarski(sK1,k2_xboole_0(X0,sK1)) = iProver_top
% 3.36/0.98      | r1_tarski(sK1,sK1) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_2603]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_1125,plain,
% 3.36/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.36/0.98      | ~ r1_tarski(X0,k1_zfmisc_1(X1)) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3826,plain,
% 3.36/0.98      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.36/0.98      | ~ r1_tarski(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_1125]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_3829,plain,
% 3.36/0.98      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 3.36/0.98      | r1_tarski(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_3826]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_900,plain,
% 3.36/0.98      ( ~ r1_tarski(X0,k2_xboole_0(X1,sK1))
% 3.36/0.98      | r1_tarski(k4_xboole_0(X0,X1),sK1) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_4423,plain,
% 3.36/0.98      ( r1_tarski(k4_xboole_0(sK1,X0),sK1)
% 3.36/0.98      | ~ r1_tarski(sK1,k2_xboole_0(X0,sK1)) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_900]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_4424,plain,
% 3.36/0.98      ( r1_tarski(k4_xboole_0(sK1,X0),sK1) = iProver_top
% 3.36/0.98      | r1_tarski(sK1,k2_xboole_0(X0,sK1)) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_4423]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_734,plain,
% 3.36/0.98      ( v1_tops_2(X0,sK0)
% 3.36/0.98      | ~ v1_tops_2(sK1,sK0)
% 3.36/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.36/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.36/0.98      | ~ r1_tarski(X0,sK1) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_187]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_7880,plain,
% 3.36/0.98      ( v1_tops_2(k4_xboole_0(sK1,X0),sK0)
% 3.36/0.98      | ~ v1_tops_2(sK1,sK0)
% 3.36/0.98      | ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.36/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 3.36/0.98      | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
% 3.36/0.98      inference(instantiation,[status(thm)],[c_734]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_7881,plain,
% 3.36/0.98      ( v1_tops_2(k4_xboole_0(sK1,X0),sK0) = iProver_top
% 3.36/0.98      | v1_tops_2(sK1,sK0) != iProver_top
% 3.36/0.98      | m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.36/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 3.36/0.98      | r1_tarski(k4_xboole_0(sK1,X0),sK1) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_7880]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_9214,plain,
% 3.36/0.98      ( v1_tops_2(k4_xboole_0(sK1,X0),sK0) = iProver_top ),
% 3.36/0.98      inference(global_propositional_subsumption,
% 3.36/0.98                [status(thm)],
% 3.36/0.98                [c_8989,c_16,c_18,c_966,c_1430,c_1494,c_1943,c_2607,c_3829,
% 3.36/0.98                 c_4424,c_7881]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_6,plain,
% 3.36/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.36/0.98      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.36/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_106,plain,
% 3.36/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.36/0.98      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_107,plain,
% 3.36/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.36/0.98      inference(renaming,[status(thm)],[c_106]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_131,plain,
% 3.36/0.98      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.36/0.98      inference(bin_hyper_res,[status(thm)],[c_6,c_107]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_648,plain,
% 3.36/0.98      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.36/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_131]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_8497,plain,
% 3.36/0.98      ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_1084,c_648]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_10,negated_conjecture,
% 3.36/0.98      ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
% 3.36/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_652,plain,
% 3.36/0.98      ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
% 3.36/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_8870,plain,
% 3.36/0.98      ( v1_tops_2(k4_xboole_0(sK1,sK2),sK0) != iProver_top ),
% 3.36/0.98      inference(demodulation,[status(thm)],[c_8497,c_652]) ).
% 3.36/0.98  
% 3.36/0.98  cnf(c_9221,plain,
% 3.36/0.98      ( $false ),
% 3.36/0.98      inference(superposition,[status(thm)],[c_9214,c_8870]) ).
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/0.98  
% 3.36/0.98  ------                               Statistics
% 3.36/0.98  
% 3.36/0.98  ------ General
% 3.36/0.98  
% 3.36/0.98  abstr_ref_over_cycles:                  0
% 3.36/0.98  abstr_ref_under_cycles:                 0
% 3.36/0.98  gc_basic_clause_elim:                   0
% 3.36/0.98  forced_gc_time:                         0
% 3.36/0.98  parsing_time:                           0.01
% 3.36/0.98  unif_index_cands_time:                  0.
% 3.36/0.98  unif_index_add_time:                    0.
% 3.36/0.98  orderings_time:                         0.
% 3.36/0.98  out_proof_time:                         0.01
% 3.36/0.98  total_time:                             0.278
% 3.36/0.98  num_of_symbols:                         44
% 3.36/0.98  num_of_terms:                           10260
% 3.36/0.98  
% 3.36/0.98  ------ Preprocessing
% 3.36/0.98  
% 3.36/0.98  num_of_splits:                          0
% 3.36/0.98  num_of_split_atoms:                     0
% 3.36/0.98  num_of_reused_defs:                     0
% 3.36/0.98  num_eq_ax_congr_red:                    12
% 3.36/0.98  num_of_sem_filtered_clauses:            1
% 3.36/0.98  num_of_subtypes:                        0
% 3.36/0.98  monotx_restored_types:                  0
% 3.36/0.98  sat_num_of_epr_types:                   0
% 3.36/0.98  sat_num_of_non_cyclic_types:            0
% 3.36/0.98  sat_guarded_non_collapsed_types:        0
% 3.36/0.98  num_pure_diseq_elim:                    0
% 3.36/0.98  simp_replaced_by:                       0
% 3.36/0.98  res_preprocessed:                       72
% 3.36/0.98  prep_upred:                             0
% 3.36/0.98  prep_unflattend:                        1
% 3.36/0.98  smt_new_axioms:                         0
% 3.36/0.98  pred_elim_cands:                        3
% 3.36/0.98  pred_elim:                              1
% 3.36/0.98  pred_elim_cl:                           1
% 3.36/0.98  pred_elim_cycles:                       3
% 3.36/0.98  merged_defs:                            8
% 3.36/0.98  merged_defs_ncl:                        0
% 3.36/0.98  bin_hyper_res:                          9
% 3.36/0.98  prep_cycles:                            4
% 3.36/0.98  pred_elim_time:                         0.001
% 3.36/0.98  splitting_time:                         0.
% 3.36/0.98  sem_filter_time:                        0.
% 3.36/0.98  monotx_time:                            0.001
% 3.36/0.98  subtype_inf_time:                       0.
% 3.36/0.98  
% 3.36/0.98  ------ Problem properties
% 3.36/0.98  
% 3.36/0.98  clauses:                                13
% 3.36/0.98  conjectures:                            4
% 3.36/0.98  epr:                                    3
% 3.36/0.98  horn:                                   13
% 3.36/0.98  ground:                                 4
% 3.36/0.98  unary:                                  6
% 3.36/0.98  binary:                                 5
% 3.36/0.98  lits:                                   24
% 3.36/0.98  lits_eq:                                3
% 3.36/0.98  fd_pure:                                0
% 3.36/0.98  fd_pseudo:                              0
% 3.36/0.98  fd_cond:                                0
% 3.36/0.98  fd_pseudo_cond:                         1
% 3.36/0.98  ac_symbols:                             0
% 3.36/0.98  
% 3.36/0.98  ------ Propositional Solver
% 3.36/0.98  
% 3.36/0.98  prop_solver_calls:                      29
% 3.36/0.98  prop_fast_solver_calls:                 540
% 3.36/0.98  smt_solver_calls:                       0
% 3.36/0.98  smt_fast_solver_calls:                  0
% 3.36/0.98  prop_num_of_clauses:                    4060
% 3.36/0.98  prop_preprocess_simplified:             8261
% 3.36/0.98  prop_fo_subsumed:                       4
% 3.36/0.98  prop_solver_time:                       0.
% 3.36/0.98  smt_solver_time:                        0.
% 3.36/0.98  smt_fast_solver_time:                   0.
% 3.36/0.98  prop_fast_solver_time:                  0.
% 3.36/0.98  prop_unsat_core_time:                   0.
% 3.36/0.98  
% 3.36/0.98  ------ QBF
% 3.36/0.98  
% 3.36/0.98  qbf_q_res:                              0
% 3.36/0.98  qbf_num_tautologies:                    0
% 3.36/0.98  qbf_prep_cycles:                        0
% 3.36/0.98  
% 3.36/0.98  ------ BMC1
% 3.36/0.98  
% 3.36/0.98  bmc1_current_bound:                     -1
% 3.36/0.98  bmc1_last_solved_bound:                 -1
% 3.36/0.98  bmc1_unsat_core_size:                   -1
% 3.36/0.98  bmc1_unsat_core_parents_size:           -1
% 3.36/0.98  bmc1_merge_next_fun:                    0
% 3.36/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.36/0.98  
% 3.36/0.98  ------ Instantiation
% 3.36/0.98  
% 3.36/0.98  inst_num_of_clauses:                    1003
% 3.36/0.98  inst_num_in_passive:                    332
% 3.36/0.98  inst_num_in_active:                     481
% 3.36/0.98  inst_num_in_unprocessed:                190
% 3.36/0.98  inst_num_of_loops:                      490
% 3.36/0.98  inst_num_of_learning_restarts:          0
% 3.36/0.98  inst_num_moves_active_passive:          6
% 3.36/0.98  inst_lit_activity:                      0
% 3.36/0.98  inst_lit_activity_moves:                0
% 3.36/0.98  inst_num_tautologies:                   0
% 3.36/0.98  inst_num_prop_implied:                  0
% 3.36/0.98  inst_num_existing_simplified:           0
% 3.36/0.98  inst_num_eq_res_simplified:             0
% 3.36/0.98  inst_num_child_elim:                    0
% 3.36/0.98  inst_num_of_dismatching_blockings:      409
% 3.36/0.98  inst_num_of_non_proper_insts:           1481
% 3.36/0.98  inst_num_of_duplicates:                 0
% 3.36/0.98  inst_inst_num_from_inst_to_res:         0
% 3.36/0.98  inst_dismatching_checking_time:         0.
% 3.36/0.98  
% 3.36/0.98  ------ Resolution
% 3.36/0.98  
% 3.36/0.98  res_num_of_clauses:                     0
% 3.36/0.98  res_num_in_passive:                     0
% 3.36/0.98  res_num_in_active:                      0
% 3.36/0.98  res_num_of_loops:                       76
% 3.36/0.98  res_forward_subset_subsumed:            114
% 3.36/0.98  res_backward_subset_subsumed:           4
% 3.36/0.98  res_forward_subsumed:                   0
% 3.36/0.98  res_backward_subsumed:                  0
% 3.36/0.98  res_forward_subsumption_resolution:     0
% 3.36/0.98  res_backward_subsumption_resolution:    0
% 3.36/0.98  res_clause_to_clause_subsumption:       959
% 3.36/0.98  res_orphan_elimination:                 0
% 3.36/0.98  res_tautology_del:                      121
% 3.36/0.98  res_num_eq_res_simplified:              0
% 3.36/0.98  res_num_sel_changes:                    0
% 3.36/0.98  res_moves_from_active_to_pass:          0
% 3.36/0.98  
% 3.36/0.98  ------ Superposition
% 3.36/0.98  
% 3.36/0.98  sup_time_total:                         0.
% 3.36/0.98  sup_time_generating:                    0.
% 3.36/0.98  sup_time_sim_full:                      0.
% 3.36/0.98  sup_time_sim_immed:                     0.
% 3.36/0.98  
% 3.36/0.98  sup_num_of_clauses:                     224
% 3.36/0.98  sup_num_in_active:                      96
% 3.36/0.98  sup_num_in_passive:                     128
% 3.36/0.98  sup_num_of_loops:                       96
% 3.36/0.98  sup_fw_superposition:                   100
% 3.36/0.98  sup_bw_superposition:                   160
% 3.36/0.98  sup_immediate_simplified:               23
% 3.36/0.98  sup_given_eliminated:                   0
% 3.36/0.98  comparisons_done:                       0
% 3.36/0.98  comparisons_avoided:                    0
% 3.36/0.98  
% 3.36/0.98  ------ Simplifications
% 3.36/0.98  
% 3.36/0.98  
% 3.36/0.98  sim_fw_subset_subsumed:                 8
% 3.36/0.99  sim_bw_subset_subsumed:                 0
% 3.36/0.99  sim_fw_subsumed:                        15
% 3.36/0.99  sim_bw_subsumed:                        0
% 3.36/0.99  sim_fw_subsumption_res:                 1
% 3.36/0.99  sim_bw_subsumption_res:                 0
% 3.36/0.99  sim_tautology_del:                      5
% 3.36/0.99  sim_eq_tautology_del:                   1
% 3.36/0.99  sim_eq_res_simp:                        0
% 3.36/0.99  sim_fw_demodulated:                     7
% 3.36/0.99  sim_bw_demodulated:                     1
% 3.36/0.99  sim_light_normalised:                   0
% 3.36/0.99  sim_joinable_taut:                      0
% 3.36/0.99  sim_joinable_simp:                      0
% 3.36/0.99  sim_ac_normalised:                      0
% 3.36/0.99  sim_smt_subsumption:                    0
% 3.36/0.99  
%------------------------------------------------------------------------------
