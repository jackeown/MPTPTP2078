%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:44 EST 2020

% Result     : Theorem 8.13s
% Output     : CNFRefutation 8.13s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 360 expanded)
%              Number of clauses        :   71 ( 117 expanded)
%              Number of leaves         :   14 (  84 expanded)
%              Depth                    :   18
%              Number of atoms          :  296 (1175 expanded)
%              Number of equality atoms :  115 ( 174 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1)))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f35,f34])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_790,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_800,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1112,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_800])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_802,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1588,plain,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1112,c_802])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_795,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2333,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_795])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_981,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_982,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_981])).

cnf(c_2776,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2333,c_20,c_21,c_982])).

cnf(c_2783,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2776,c_802])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_805,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_803,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1432,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_803])).

cnf(c_3740,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1432,c_803])).

cnf(c_4723,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2783,c_3740])).

cnf(c_5194,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1588,c_4723])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_801,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_799,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2546,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_799])).

cnf(c_34709,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5194,c_2546])).

cnf(c_11,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_797,plain,
    ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
    | v5_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3517,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
    | v5_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_797])).

cnf(c_17,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1033,plain,
    ( ~ v5_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3913,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3517,c_19,c_18,c_17,c_1033])).

cnf(c_34712,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34709,c_3913])).

cnf(c_35691,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_34712,c_20])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_796,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2350,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_796,c_800])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_136,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_137,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_136])).

cnf(c_165,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_137])).

cnf(c_266,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_267,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_266])).

cnf(c_297,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_165,c_267])).

cnf(c_788,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_1586,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1112,c_788])).

cnf(c_28202,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2350,c_1586])).

cnf(c_29555,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28202,c_20])).

cnf(c_29556,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_29555])).

cnf(c_29565,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_790,c_29556])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_794,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2578,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_794])).

cnf(c_1037,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2915,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2578,c_19,c_18,c_1037])).

cnf(c_29567,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_29565,c_2915])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_804,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_29586,plain,
    ( r1_tarski(X0,k2_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_29567,c_804])).

cnf(c_31884,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_29586])).

cnf(c_35705,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_35691,c_31884])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_792,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3916,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3913,c_792])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35705,c_3916])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:59:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.13/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.13/1.50  
% 8.13/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.13/1.50  
% 8.13/1.50  ------  iProver source info
% 8.13/1.50  
% 8.13/1.50  git: date: 2020-06-30 10:37:57 +0100
% 8.13/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.13/1.50  git: non_committed_changes: false
% 8.13/1.50  git: last_make_outside_of_git: false
% 8.13/1.50  
% 8.13/1.50  ------ 
% 8.13/1.50  ------ Parsing...
% 8.13/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.13/1.50  
% 8.13/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 8.13/1.50  
% 8.13/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.13/1.50  
% 8.13/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.13/1.50  ------ Proving...
% 8.13/1.50  ------ Problem Properties 
% 8.13/1.50  
% 8.13/1.50  
% 8.13/1.50  clauses                                 19
% 8.13/1.50  conjectures                             4
% 8.13/1.50  EPR                                     4
% 8.13/1.50  Horn                                    19
% 8.13/1.50  unary                                   5
% 8.13/1.50  binary                                  5
% 8.13/1.50  lits                                    44
% 8.13/1.50  lits eq                                 7
% 8.13/1.50  fd_pure                                 0
% 8.13/1.50  fd_pseudo                               0
% 8.13/1.50  fd_cond                                 0
% 8.13/1.50  fd_pseudo_cond                          1
% 8.13/1.50  AC symbols                              0
% 8.13/1.50  
% 8.13/1.50  ------ Input Options Time Limit: Unbounded
% 8.13/1.50  
% 8.13/1.50  
% 8.13/1.50  ------ 
% 8.13/1.50  Current options:
% 8.13/1.50  ------ 
% 8.13/1.50  
% 8.13/1.50  
% 8.13/1.50  
% 8.13/1.50  
% 8.13/1.50  ------ Proving...
% 8.13/1.50  
% 8.13/1.50  
% 8.13/1.50  % SZS status Theorem for theBenchmark.p
% 8.13/1.50  
% 8.13/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 8.13/1.50  
% 8.13/1.50  fof(f13,conjecture,(
% 8.13/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 8.13/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.13/1.50  
% 8.13/1.50  fof(f14,negated_conjecture,(
% 8.13/1.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 8.13/1.50    inference(negated_conjecture,[],[f13])).
% 8.13/1.50  
% 8.13/1.50  fof(f28,plain,(
% 8.13/1.50    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.13/1.50    inference(ennf_transformation,[],[f14])).
% 8.13/1.50  
% 8.13/1.50  fof(f29,plain,(
% 8.13/1.50    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.13/1.50    inference(flattening,[],[f28])).
% 8.13/1.50  
% 8.13/1.50  fof(f35,plain,(
% 8.13/1.50    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1))) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 8.13/1.50    introduced(choice_axiom,[])).
% 8.13/1.50  
% 8.13/1.50  fof(f34,plain,(
% 8.13/1.50    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 8.13/1.50    introduced(choice_axiom,[])).
% 8.13/1.50  
% 8.13/1.50  fof(f36,plain,(
% 8.13/1.50    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 8.13/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f35,f34])).
% 8.13/1.50  
% 8.13/1.50  fof(f54,plain,(
% 8.13/1.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.13/1.50    inference(cnf_transformation,[],[f36])).
% 8.13/1.50  
% 8.13/1.50  fof(f6,axiom,(
% 8.13/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.13/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.13/1.50  
% 8.13/1.50  fof(f32,plain,(
% 8.13/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.13/1.50    inference(nnf_transformation,[],[f6])).
% 8.13/1.50  
% 8.13/1.50  fof(f44,plain,(
% 8.13/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 8.13/1.50    inference(cnf_transformation,[],[f32])).
% 8.13/1.50  
% 8.13/1.50  fof(f4,axiom,(
% 8.13/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 8.13/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.13/1.50  
% 8.13/1.50  fof(f17,plain,(
% 8.13/1.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 8.13/1.50    inference(ennf_transformation,[],[f4])).
% 8.13/1.50  
% 8.13/1.50  fof(f42,plain,(
% 8.13/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 8.13/1.50    inference(cnf_transformation,[],[f17])).
% 8.13/1.50  
% 8.13/1.50  fof(f10,axiom,(
% 8.13/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 8.13/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.13/1.50  
% 8.13/1.50  fof(f25,plain,(
% 8.13/1.50    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.13/1.50    inference(ennf_transformation,[],[f10])).
% 8.13/1.50  
% 8.13/1.50  fof(f50,plain,(
% 8.13/1.50    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.13/1.50    inference(cnf_transformation,[],[f25])).
% 8.13/1.50  
% 8.13/1.50  fof(f53,plain,(
% 8.13/1.50    l1_pre_topc(sK0)),
% 8.13/1.50    inference(cnf_transformation,[],[f36])).
% 8.13/1.50  
% 8.13/1.50  fof(f1,axiom,(
% 8.13/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.13/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.13/1.50  
% 8.13/1.50  fof(f30,plain,(
% 8.13/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.13/1.50    inference(nnf_transformation,[],[f1])).
% 8.13/1.50  
% 8.13/1.50  fof(f31,plain,(
% 8.13/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.13/1.50    inference(flattening,[],[f30])).
% 8.13/1.50  
% 8.13/1.50  fof(f38,plain,(
% 8.13/1.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 8.13/1.50    inference(cnf_transformation,[],[f31])).
% 8.13/1.50  
% 8.13/1.50  fof(f57,plain,(
% 8.13/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.13/1.50    inference(equality_resolution,[],[f38])).
% 8.13/1.50  
% 8.13/1.50  fof(f3,axiom,(
% 8.13/1.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 8.13/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.13/1.50  
% 8.13/1.50  fof(f16,plain,(
% 8.13/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 8.13/1.50    inference(ennf_transformation,[],[f3])).
% 8.13/1.50  
% 8.13/1.50  fof(f41,plain,(
% 8.13/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 8.13/1.50    inference(cnf_transformation,[],[f16])).
% 8.13/1.50  
% 8.13/1.50  fof(f45,plain,(
% 8.13/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.13/1.50    inference(cnf_transformation,[],[f32])).
% 8.13/1.50  
% 8.13/1.50  fof(f7,axiom,(
% 8.13/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 8.13/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.13/1.50  
% 8.13/1.50  fof(f20,plain,(
% 8.13/1.50    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.13/1.50    inference(ennf_transformation,[],[f7])).
% 8.13/1.50  
% 8.13/1.50  fof(f21,plain,(
% 8.13/1.50    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.13/1.50    inference(flattening,[],[f20])).
% 8.13/1.50  
% 8.13/1.50  fof(f46,plain,(
% 8.13/1.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.13/1.50    inference(cnf_transformation,[],[f21])).
% 8.13/1.50  
% 8.13/1.50  fof(f8,axiom,(
% 8.13/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 8.13/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.13/1.50  
% 8.13/1.50  fof(f22,plain,(
% 8.13/1.50    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.13/1.50    inference(ennf_transformation,[],[f8])).
% 8.13/1.50  
% 8.13/1.50  fof(f33,plain,(
% 8.13/1.50    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.13/1.50    inference(nnf_transformation,[],[f22])).
% 8.13/1.50  
% 8.13/1.50  fof(f47,plain,(
% 8.13/1.50    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.13/1.50    inference(cnf_transformation,[],[f33])).
% 8.13/1.50  
% 8.13/1.50  fof(f55,plain,(
% 8.13/1.50    v5_tops_1(sK1,sK0)),
% 8.13/1.50    inference(cnf_transformation,[],[f36])).
% 8.13/1.50  
% 8.13/1.50  fof(f9,axiom,(
% 8.13/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 8.13/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.13/1.50  
% 8.13/1.50  fof(f23,plain,(
% 8.13/1.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.13/1.50    inference(ennf_transformation,[],[f9])).
% 8.13/1.50  
% 8.13/1.50  fof(f24,plain,(
% 8.13/1.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.13/1.50    inference(flattening,[],[f23])).
% 8.13/1.50  
% 8.13/1.50  fof(f49,plain,(
% 8.13/1.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.13/1.50    inference(cnf_transformation,[],[f24])).
% 8.13/1.50  
% 8.13/1.50  fof(f5,axiom,(
% 8.13/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 8.13/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.13/1.50  
% 8.13/1.50  fof(f18,plain,(
% 8.13/1.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 8.13/1.50    inference(ennf_transformation,[],[f5])).
% 8.13/1.50  
% 8.13/1.50  fof(f19,plain,(
% 8.13/1.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.13/1.50    inference(flattening,[],[f18])).
% 8.13/1.50  
% 8.13/1.50  fof(f43,plain,(
% 8.13/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.13/1.50    inference(cnf_transformation,[],[f19])).
% 8.13/1.50  
% 8.13/1.50  fof(f11,axiom,(
% 8.13/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 8.13/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.13/1.50  
% 8.13/1.50  fof(f26,plain,(
% 8.13/1.50    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.13/1.50    inference(ennf_transformation,[],[f11])).
% 8.13/1.50  
% 8.13/1.50  fof(f51,plain,(
% 8.13/1.50    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.13/1.50    inference(cnf_transformation,[],[f26])).
% 8.13/1.50  
% 8.13/1.50  fof(f2,axiom,(
% 8.13/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 8.13/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.13/1.50  
% 8.13/1.50  fof(f15,plain,(
% 8.13/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 8.13/1.50    inference(ennf_transformation,[],[f2])).
% 8.13/1.50  
% 8.13/1.50  fof(f40,plain,(
% 8.13/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 8.13/1.50    inference(cnf_transformation,[],[f15])).
% 8.13/1.50  
% 8.13/1.50  fof(f56,plain,(
% 8.13/1.50    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 8.13/1.50    inference(cnf_transformation,[],[f36])).
% 8.13/1.50  
% 8.13/1.50  cnf(c_18,negated_conjecture,
% 8.13/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.13/1.50      inference(cnf_transformation,[],[f54]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_790,plain,
% 8.13/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_8,plain,
% 8.13/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 8.13/1.50      inference(cnf_transformation,[],[f44]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_800,plain,
% 8.13/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.13/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_1112,plain,
% 8.13/1.50      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_790,c_800]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_5,plain,
% 8.13/1.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 8.13/1.50      inference(cnf_transformation,[],[f42]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_802,plain,
% 8.13/1.50      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_1588,plain,
% 8.13/1.50      ( k2_xboole_0(sK1,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_1112,c_802]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_13,plain,
% 8.13/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.13/1.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 8.13/1.50      | ~ l1_pre_topc(X1) ),
% 8.13/1.50      inference(cnf_transformation,[],[f50]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_795,plain,
% 8.13/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.13/1.50      | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
% 8.13/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_2333,plain,
% 8.13/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 8.13/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_790,c_795]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_19,negated_conjecture,
% 8.13/1.50      ( l1_pre_topc(sK0) ),
% 8.13/1.50      inference(cnf_transformation,[],[f53]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_20,plain,
% 8.13/1.50      ( l1_pre_topc(sK0) = iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_21,plain,
% 8.13/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_981,plain,
% 8.13/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.13/1.50      | r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 8.13/1.50      | ~ l1_pre_topc(sK0) ),
% 8.13/1.50      inference(instantiation,[status(thm)],[c_13]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_982,plain,
% 8.13/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.13/1.50      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 8.13/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_981]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_2776,plain,
% 8.13/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 8.13/1.50      inference(global_propositional_subsumption,
% 8.13/1.50                [status(thm)],
% 8.13/1.50                [c_2333,c_20,c_21,c_982]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_2783,plain,
% 8.13/1.50      ( k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = sK1 ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_2776,c_802]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_1,plain,
% 8.13/1.50      ( r1_tarski(X0,X0) ),
% 8.13/1.50      inference(cnf_transformation,[],[f57]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_805,plain,
% 8.13/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_4,plain,
% 8.13/1.50      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 8.13/1.50      inference(cnf_transformation,[],[f41]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_803,plain,
% 8.13/1.50      ( r1_tarski(X0,X1) = iProver_top
% 8.13/1.50      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_1432,plain,
% 8.13/1.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_805,c_803]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_3740,plain,
% 8.13/1.50      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_1432,c_803]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_4723,plain,
% 8.13/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,X0)) = iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_2783,c_3740]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_5194,plain,
% 8.13/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_1588,c_4723]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_7,plain,
% 8.13/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.13/1.50      inference(cnf_transformation,[],[f45]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_801,plain,
% 8.13/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 8.13/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_9,plain,
% 8.13/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.13/1.50      | ~ l1_pre_topc(X1)
% 8.13/1.50      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 8.13/1.50      inference(cnf_transformation,[],[f46]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_799,plain,
% 8.13/1.50      ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
% 8.13/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.13/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_2546,plain,
% 8.13/1.50      ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
% 8.13/1.50      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 8.13/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_801,c_799]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_34709,plain,
% 8.13/1.50      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 8.13/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_5194,c_2546]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_11,plain,
% 8.13/1.50      ( ~ v5_tops_1(X0,X1)
% 8.13/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.13/1.50      | ~ l1_pre_topc(X1)
% 8.13/1.50      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 8.13/1.50      inference(cnf_transformation,[],[f47]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_797,plain,
% 8.13/1.50      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
% 8.13/1.50      | v5_tops_1(X1,X0) != iProver_top
% 8.13/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.13/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_3517,plain,
% 8.13/1.50      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
% 8.13/1.50      | v5_tops_1(sK1,sK0) != iProver_top
% 8.13/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_790,c_797]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_17,negated_conjecture,
% 8.13/1.50      ( v5_tops_1(sK1,sK0) ),
% 8.13/1.50      inference(cnf_transformation,[],[f55]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_1033,plain,
% 8.13/1.50      ( ~ v5_tops_1(sK1,sK0)
% 8.13/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.13/1.50      | ~ l1_pre_topc(sK0)
% 8.13/1.50      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 8.13/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_3913,plain,
% 8.13/1.50      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 8.13/1.50      inference(global_propositional_subsumption,
% 8.13/1.50                [status(thm)],
% 8.13/1.50                [c_3517,c_19,c_18,c_17,c_1033]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_34712,plain,
% 8.13/1.50      ( k2_pre_topc(sK0,sK1) = sK1 | l1_pre_topc(sK0) != iProver_top ),
% 8.13/1.50      inference(light_normalisation,[status(thm)],[c_34709,c_3913]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_35691,plain,
% 8.13/1.50      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 8.13/1.50      inference(global_propositional_subsumption,
% 8.13/1.50                [status(thm)],
% 8.13/1.50                [c_34712,c_20]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_12,plain,
% 8.13/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.13/1.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.13/1.50      | ~ l1_pre_topc(X1) ),
% 8.13/1.50      inference(cnf_transformation,[],[f49]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_796,plain,
% 8.13/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.13/1.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.13/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_2350,plain,
% 8.13/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.13/1.50      | r1_tarski(k2_tops_1(X1,X0),u1_struct_0(X1)) = iProver_top
% 8.13/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_796,c_800]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_6,plain,
% 8.13/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.13/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 8.13/1.50      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 8.13/1.50      inference(cnf_transformation,[],[f43]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_136,plain,
% 8.13/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.13/1.50      inference(prop_impl,[status(thm)],[c_7]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_137,plain,
% 8.13/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.13/1.50      inference(renaming,[status(thm)],[c_136]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_165,plain,
% 8.13/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.13/1.50      | ~ r1_tarski(X2,X1)
% 8.13/1.50      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 8.13/1.50      inference(bin_hyper_res,[status(thm)],[c_6,c_137]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_266,plain,
% 8.13/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.13/1.50      inference(prop_impl,[status(thm)],[c_7]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_267,plain,
% 8.13/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.13/1.50      inference(renaming,[status(thm)],[c_266]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_297,plain,
% 8.13/1.50      ( ~ r1_tarski(X0,X1)
% 8.13/1.50      | ~ r1_tarski(X2,X1)
% 8.13/1.50      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 8.13/1.50      inference(bin_hyper_res,[status(thm)],[c_165,c_267]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_788,plain,
% 8.13/1.50      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 8.13/1.50      | r1_tarski(X1,X0) != iProver_top
% 8.13/1.50      | r1_tarski(X2,X0) != iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_1586,plain,
% 8.13/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 8.13/1.50      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_1112,c_788]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_28202,plain,
% 8.13/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 8.13/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.13/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_2350,c_1586]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_29555,plain,
% 8.13/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.13/1.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 8.13/1.50      inference(global_propositional_subsumption,
% 8.13/1.50                [status(thm)],
% 8.13/1.50                [c_28202,c_20]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_29556,plain,
% 8.13/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 8.13/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.13/1.50      inference(renaming,[status(thm)],[c_29555]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_29565,plain,
% 8.13/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_790,c_29556]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_14,plain,
% 8.13/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.13/1.50      | ~ l1_pre_topc(X1)
% 8.13/1.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 8.13/1.50      inference(cnf_transformation,[],[f51]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_794,plain,
% 8.13/1.50      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 8.13/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.13/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_2578,plain,
% 8.13/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 8.13/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_790,c_794]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_1037,plain,
% 8.13/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.13/1.50      | ~ l1_pre_topc(sK0)
% 8.13/1.50      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 8.13/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_2915,plain,
% 8.13/1.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 8.13/1.50      inference(global_propositional_subsumption,
% 8.13/1.50                [status(thm)],
% 8.13/1.50                [c_2578,c_19,c_18,c_1037]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_29567,plain,
% 8.13/1.50      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 8.13/1.50      inference(light_normalisation,[status(thm)],[c_29565,c_2915]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_3,plain,
% 8.13/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 8.13/1.50      inference(cnf_transformation,[],[f40]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_804,plain,
% 8.13/1.50      ( r1_tarski(X0,X1) != iProver_top
% 8.13/1.50      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_29586,plain,
% 8.13/1.50      ( r1_tarski(X0,k2_tops_1(sK0,sK1)) != iProver_top
% 8.13/1.50      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) = iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_29567,c_804]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_31884,plain,
% 8.13/1.50      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 8.13/1.50      inference(superposition,[status(thm)],[c_805,c_29586]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_35705,plain,
% 8.13/1.50      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 8.13/1.50      inference(demodulation,[status(thm)],[c_35691,c_31884]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_16,negated_conjecture,
% 8.13/1.50      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 8.13/1.50      inference(cnf_transformation,[],[f56]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_792,plain,
% 8.13/1.50      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 8.13/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(c_3916,plain,
% 8.13/1.50      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 8.13/1.50      inference(demodulation,[status(thm)],[c_3913,c_792]) ).
% 8.13/1.50  
% 8.13/1.50  cnf(contradiction,plain,
% 8.13/1.50      ( $false ),
% 8.13/1.50      inference(minisat,[status(thm)],[c_35705,c_3916]) ).
% 8.13/1.50  
% 8.13/1.50  
% 8.13/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 8.13/1.50  
% 8.13/1.50  ------                               Statistics
% 8.13/1.50  
% 8.13/1.50  ------ Selected
% 8.13/1.50  
% 8.13/1.50  total_time:                             1.004
% 8.13/1.50  
%------------------------------------------------------------------------------
