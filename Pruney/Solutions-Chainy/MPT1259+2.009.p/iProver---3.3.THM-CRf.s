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
% DateTime   : Thu Dec  3 12:14:16 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 676 expanded)
%              Number of clauses        :   72 ( 226 expanded)
%              Number of leaves         :   16 ( 156 expanded)
%              Depth                    :   21
%              Number of atoms          :  283 (1898 expanded)
%              Number of equality atoms :  142 ( 626 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_tops_1(X0,k2_tops_1(X0,sK1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,sK1)))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f33,f32])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_705,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_709,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_711,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1279,plain,
    ( k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1))) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_711])).

cnf(c_7700,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_705,c_1279])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_873,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2977,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6924,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2977])).

cnf(c_7804,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7700,c_17,c_16,c_873,c_6924])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_712,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7807,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7804,c_712])).

cnf(c_20,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_874,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_7810,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7807,c_20,c_21,c_874])).

cnf(c_7823,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7810,c_1279])).

cnf(c_9052,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7823,c_20])).

cnf(c_9055,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9052,c_712])).

cnf(c_972,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_973,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_972])).

cnf(c_9375,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9055,c_20,c_21,c_874,c_973])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_713,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_729,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_713,c_5])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_710,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1946,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_729,c_710])).

cnf(c_1951,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1946,c_710])).

cnf(c_9397,plain,
    ( k7_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) ),
    inference(superposition,[status(thm)],[c_9375,c_1951])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_714,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1477,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
    inference(superposition,[status(thm)],[c_729,c_714])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_717,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_716,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1125,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_717,c_716])).

cnf(c_1807,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1477,c_1125])).

cnf(c_1812,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1807,c_712])).

cnf(c_1925,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1812,c_729])).

cnf(c_1932,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1925,c_714])).

cnf(c_1281,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_729,c_711])).

cnf(c_1810,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1807,c_1281])).

cnf(c_1937,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1932,c_1810])).

cnf(c_3068,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1946,c_1937])).

cnf(c_14019,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_9397,c_3068])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_708,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9396,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9375,c_708])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_706,plain,
    ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2430,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_xboole_0
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_705,c_706])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_905,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2907,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2430,c_18,c_17,c_16,c_905])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_707,plain,
    ( k2_pre_topc(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7827,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1))
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7810,c_707])).

cnf(c_970,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8149,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7827,c_18,c_17,c_16,c_873,c_970])).

cnf(c_9402,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9396,c_2907,c_8149])).

cnf(c_9912,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9402,c_20])).

cnf(c_18198,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_14019,c_9912])).

cnf(c_15,negated_conjecture,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18383,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_18198,c_15])).

cnf(c_18384,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_18383])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:59:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.71/1.61  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/1.61  
% 7.71/1.61  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.71/1.61  
% 7.71/1.61  ------  iProver source info
% 7.71/1.61  
% 7.71/1.61  git: date: 2020-06-30 10:37:57 +0100
% 7.71/1.61  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.71/1.61  git: non_committed_changes: false
% 7.71/1.61  git: last_make_outside_of_git: false
% 7.71/1.61  
% 7.71/1.61  ------ 
% 7.71/1.61  ------ Parsing...
% 7.71/1.61  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.71/1.61  
% 7.71/1.61  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.71/1.61  
% 7.71/1.61  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.71/1.61  
% 7.71/1.61  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.71/1.61  ------ Proving...
% 7.71/1.61  ------ Problem Properties 
% 7.71/1.61  
% 7.71/1.61  
% 7.71/1.61  clauses                                 18
% 7.71/1.61  conjectures                             4
% 7.71/1.61  EPR                                     4
% 7.71/1.61  Horn                                    18
% 7.71/1.61  unary                                   7
% 7.71/1.61  binary                                  6
% 7.71/1.61  lits                                    36
% 7.71/1.61  lits eq                                 11
% 7.71/1.61  fd_pure                                 0
% 7.71/1.61  fd_pseudo                               0
% 7.71/1.61  fd_cond                                 0
% 7.71/1.61  fd_pseudo_cond                          1
% 7.71/1.61  AC symbols                              0
% 7.71/1.61  
% 7.71/1.61  ------ Input Options Time Limit: Unbounded
% 7.71/1.61  
% 7.71/1.61  
% 7.71/1.61  ------ 
% 7.71/1.61  Current options:
% 7.71/1.61  ------ 
% 7.71/1.61  
% 7.71/1.61  
% 7.71/1.61  
% 7.71/1.61  
% 7.71/1.61  ------ Proving...
% 7.71/1.61  
% 7.71/1.61  
% 7.71/1.61  % SZS status Theorem for theBenchmark.p
% 7.71/1.61  
% 7.71/1.61   Resolution empty clause
% 7.71/1.61  
% 7.71/1.61  % SZS output start CNFRefutation for theBenchmark.p
% 7.71/1.61  
% 7.71/1.61  fof(f14,conjecture,(
% 7.71/1.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f15,negated_conjecture,(
% 7.71/1.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 7.71/1.61    inference(negated_conjecture,[],[f14])).
% 7.71/1.61  
% 7.71/1.61  fof(f27,plain,(
% 7.71/1.61    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.71/1.61    inference(ennf_transformation,[],[f15])).
% 7.71/1.61  
% 7.71/1.61  fof(f28,plain,(
% 7.71/1.61    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.71/1.61    inference(flattening,[],[f27])).
% 7.71/1.61  
% 7.71/1.61  fof(f33,plain,(
% 7.71/1.61    ( ! [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k2_tops_1(X0,k2_tops_1(X0,sK1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.71/1.61    introduced(choice_axiom,[])).
% 7.71/1.61  
% 7.71/1.61  fof(f32,plain,(
% 7.71/1.61    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.71/1.61    introduced(choice_axiom,[])).
% 7.71/1.61  
% 7.71/1.61  fof(f34,plain,(
% 7.71/1.61    (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.71/1.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f33,f32])).
% 7.71/1.61  
% 7.71/1.61  fof(f53,plain,(
% 7.71/1.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.71/1.61    inference(cnf_transformation,[],[f34])).
% 7.71/1.61  
% 7.71/1.61  fof(f10,axiom,(
% 7.71/1.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f20,plain,(
% 7.71/1.61    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.71/1.61    inference(ennf_transformation,[],[f10])).
% 7.71/1.61  
% 7.71/1.61  fof(f21,plain,(
% 7.71/1.61    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.71/1.61    inference(flattening,[],[f20])).
% 7.71/1.61  
% 7.71/1.61  fof(f47,plain,(
% 7.71/1.61    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.71/1.61    inference(cnf_transformation,[],[f21])).
% 7.71/1.61  
% 7.71/1.61  fof(f8,axiom,(
% 7.71/1.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f18,plain,(
% 7.71/1.61    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.71/1.61    inference(ennf_transformation,[],[f8])).
% 7.71/1.61  
% 7.71/1.61  fof(f45,plain,(
% 7.71/1.61    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.71/1.61    inference(cnf_transformation,[],[f18])).
% 7.71/1.61  
% 7.71/1.61  fof(f52,plain,(
% 7.71/1.61    l1_pre_topc(sK0)),
% 7.71/1.61    inference(cnf_transformation,[],[f34])).
% 7.71/1.61  
% 7.71/1.61  fof(f7,axiom,(
% 7.71/1.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f17,plain,(
% 7.71/1.61    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.71/1.61    inference(ennf_transformation,[],[f7])).
% 7.71/1.61  
% 7.71/1.61  fof(f44,plain,(
% 7.71/1.61    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.71/1.61    inference(cnf_transformation,[],[f17])).
% 7.71/1.61  
% 7.71/1.61  fof(f6,axiom,(
% 7.71/1.61    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f43,plain,(
% 7.71/1.61    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.71/1.61    inference(cnf_transformation,[],[f6])).
% 7.71/1.61  
% 7.71/1.61  fof(f4,axiom,(
% 7.71/1.61    ! [X0] : k2_subset_1(X0) = X0),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f41,plain,(
% 7.71/1.61    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.71/1.61    inference(cnf_transformation,[],[f4])).
% 7.71/1.61  
% 7.71/1.61  fof(f9,axiom,(
% 7.71/1.61    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f19,plain,(
% 7.71/1.61    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.71/1.61    inference(ennf_transformation,[],[f9])).
% 7.71/1.61  
% 7.71/1.61  fof(f46,plain,(
% 7.71/1.61    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.71/1.61    inference(cnf_transformation,[],[f19])).
% 7.71/1.61  
% 7.71/1.61  fof(f3,axiom,(
% 7.71/1.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f40,plain,(
% 7.71/1.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.71/1.61    inference(cnf_transformation,[],[f3])).
% 7.71/1.61  
% 7.71/1.61  fof(f58,plain,(
% 7.71/1.61    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.71/1.61    inference(definition_unfolding,[],[f46,f40])).
% 7.71/1.61  
% 7.71/1.61  fof(f5,axiom,(
% 7.71/1.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f16,plain,(
% 7.71/1.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.71/1.61    inference(ennf_transformation,[],[f5])).
% 7.71/1.61  
% 7.71/1.61  fof(f42,plain,(
% 7.71/1.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.71/1.61    inference(cnf_transformation,[],[f16])).
% 7.71/1.61  
% 7.71/1.61  fof(f57,plain,(
% 7.71/1.61    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.71/1.61    inference(definition_unfolding,[],[f42,f40])).
% 7.71/1.61  
% 7.71/1.61  fof(f1,axiom,(
% 7.71/1.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f29,plain,(
% 7.71/1.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.71/1.61    inference(nnf_transformation,[],[f1])).
% 7.71/1.61  
% 7.71/1.61  fof(f30,plain,(
% 7.71/1.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.71/1.61    inference(flattening,[],[f29])).
% 7.71/1.61  
% 7.71/1.61  fof(f36,plain,(
% 7.71/1.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.71/1.61    inference(cnf_transformation,[],[f30])).
% 7.71/1.61  
% 7.71/1.61  fof(f59,plain,(
% 7.71/1.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.71/1.61    inference(equality_resolution,[],[f36])).
% 7.71/1.61  
% 7.71/1.61  fof(f2,axiom,(
% 7.71/1.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f31,plain,(
% 7.71/1.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.71/1.61    inference(nnf_transformation,[],[f2])).
% 7.71/1.61  
% 7.71/1.61  fof(f39,plain,(
% 7.71/1.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.71/1.61    inference(cnf_transformation,[],[f31])).
% 7.71/1.61  
% 7.71/1.61  fof(f55,plain,(
% 7.71/1.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 7.71/1.61    inference(definition_unfolding,[],[f39,f40])).
% 7.71/1.61  
% 7.71/1.61  fof(f11,axiom,(
% 7.71/1.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f22,plain,(
% 7.71/1.61    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.71/1.61    inference(ennf_transformation,[],[f11])).
% 7.71/1.61  
% 7.71/1.61  fof(f48,plain,(
% 7.71/1.61    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.71/1.61    inference(cnf_transformation,[],[f22])).
% 7.71/1.61  
% 7.71/1.61  fof(f13,axiom,(
% 7.71/1.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f25,plain,(
% 7.71/1.61    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.71/1.61    inference(ennf_transformation,[],[f13])).
% 7.71/1.61  
% 7.71/1.61  fof(f26,plain,(
% 7.71/1.61    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.71/1.61    inference(flattening,[],[f25])).
% 7.71/1.61  
% 7.71/1.61  fof(f50,plain,(
% 7.71/1.61    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.71/1.61    inference(cnf_transformation,[],[f26])).
% 7.71/1.61  
% 7.71/1.61  fof(f51,plain,(
% 7.71/1.61    v2_pre_topc(sK0)),
% 7.71/1.61    inference(cnf_transformation,[],[f34])).
% 7.71/1.61  
% 7.71/1.61  fof(f12,axiom,(
% 7.71/1.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))))),
% 7.71/1.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.61  
% 7.71/1.61  fof(f23,plain,(
% 7.71/1.61    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.71/1.61    inference(ennf_transformation,[],[f12])).
% 7.71/1.61  
% 7.71/1.61  fof(f24,plain,(
% 7.71/1.61    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.71/1.61    inference(flattening,[],[f23])).
% 7.71/1.61  
% 7.71/1.61  fof(f49,plain,(
% 7.71/1.61    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.71/1.61    inference(cnf_transformation,[],[f24])).
% 7.71/1.61  
% 7.71/1.61  fof(f54,plain,(
% 7.71/1.61    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 7.71/1.61    inference(cnf_transformation,[],[f34])).
% 7.71/1.61  
% 7.71/1.61  cnf(c_16,negated_conjecture,
% 7.71/1.61      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.71/1.61      inference(cnf_transformation,[],[f53]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_705,plain,
% 7.71/1.61      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_11,plain,
% 7.71/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.71/1.61      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.71/1.61      | ~ l1_pre_topc(X1) ),
% 7.71/1.61      inference(cnf_transformation,[],[f47]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_709,plain,
% 7.71/1.61      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.71/1.61      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.71/1.61      | l1_pre_topc(X1) != iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_9,plain,
% 7.71/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.71/1.61      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.71/1.61      inference(cnf_transformation,[],[f45]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_711,plain,
% 7.71/1.61      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.71/1.61      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1279,plain,
% 7.71/1.61      ( k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1))) = k2_tops_1(X0,X1)
% 7.71/1.61      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.71/1.61      | l1_pre_topc(X0) != iProver_top ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_709,c_711]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_7700,plain,
% 7.71/1.61      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 7.71/1.61      | l1_pre_topc(sK0) != iProver_top ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_705,c_1279]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_17,negated_conjecture,
% 7.71/1.61      ( l1_pre_topc(sK0) ),
% 7.71/1.61      inference(cnf_transformation,[],[f52]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_873,plain,
% 7.71/1.61      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.71/1.61      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.71/1.61      | ~ l1_pre_topc(sK0) ),
% 7.71/1.61      inference(instantiation,[status(thm)],[c_11]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_2977,plain,
% 7.71/1.61      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X0))
% 7.71/1.61      | k3_subset_1(X0,k3_subset_1(X0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 7.71/1.61      inference(instantiation,[status(thm)],[c_9]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_6924,plain,
% 7.71/1.61      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.71/1.61      | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 7.71/1.61      inference(instantiation,[status(thm)],[c_2977]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_7804,plain,
% 7.71/1.61      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 7.71/1.61      inference(global_propositional_subsumption,
% 7.71/1.61                [status(thm)],
% 7.71/1.61                [c_7700,c_17,c_16,c_873,c_6924]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_8,plain,
% 7.71/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.71/1.61      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.71/1.61      inference(cnf_transformation,[],[f44]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_712,plain,
% 7.71/1.61      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.71/1.61      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_7807,plain,
% 7.71/1.61      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.71/1.61      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_7804,c_712]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_20,plain,
% 7.71/1.61      ( l1_pre_topc(sK0) = iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_21,plain,
% 7.71/1.61      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_874,plain,
% 7.71/1.61      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.71/1.61      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.71/1.61      | l1_pre_topc(sK0) != iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_873]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_7810,plain,
% 7.71/1.61      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.71/1.61      inference(global_propositional_subsumption,
% 7.71/1.61                [status(thm)],
% 7.71/1.61                [c_7807,c_20,c_21,c_874]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_7823,plain,
% 7.71/1.61      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1))
% 7.71/1.61      | l1_pre_topc(sK0) != iProver_top ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_7810,c_1279]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_9052,plain,
% 7.71/1.61      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 7.71/1.61      inference(global_propositional_subsumption,[status(thm)],[c_7823,c_20]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_9055,plain,
% 7.71/1.61      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.71/1.61      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_9052,c_712]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_972,plain,
% 7.71/1.61      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.71/1.61      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.71/1.61      | ~ l1_pre_topc(sK0) ),
% 7.71/1.61      inference(instantiation,[status(thm)],[c_11]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_973,plain,
% 7.71/1.61      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.71/1.61      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.71/1.61      | l1_pre_topc(sK0) != iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_972]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_9375,plain,
% 7.71/1.61      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.71/1.61      inference(global_propositional_subsumption,
% 7.71/1.61                [status(thm)],
% 7.71/1.61                [c_9055,c_20,c_21,c_874,c_973]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_7,plain,
% 7.71/1.61      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 7.71/1.61      inference(cnf_transformation,[],[f43]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_713,plain,
% 7.71/1.61      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_5,plain,
% 7.71/1.61      ( k2_subset_1(X0) = X0 ),
% 7.71/1.61      inference(cnf_transformation,[],[f41]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_729,plain,
% 7.71/1.61      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.71/1.61      inference(light_normalisation,[status(thm)],[c_713,c_5]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_10,plain,
% 7.71/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.71/1.61      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 7.71/1.61      inference(cnf_transformation,[],[f58]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_710,plain,
% 7.71/1.61      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 7.71/1.61      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1946,plain,
% 7.71/1.61      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_729,c_710]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1951,plain,
% 7.71/1.61      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 7.71/1.61      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.71/1.61      inference(demodulation,[status(thm)],[c_1946,c_710]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_9397,plain,
% 7.71/1.61      ( k7_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_9375,c_1951]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_6,plain,
% 7.71/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.71/1.61      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 7.71/1.61      inference(cnf_transformation,[],[f57]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_714,plain,
% 7.71/1.61      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 7.71/1.61      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1477,plain,
% 7.71/1.61      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_729,c_714]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f59]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_717,plain,
% 7.71/1.61      ( r1_tarski(X0,X0) = iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_3,plain,
% 7.71/1.61      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.71/1.61      inference(cnf_transformation,[],[f55]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_716,plain,
% 7.71/1.61      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 7.71/1.61      | r1_tarski(X0,X1) != iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1125,plain,
% 7.71/1.61      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_717,c_716]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1807,plain,
% 7.71/1.61      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 7.71/1.61      inference(light_normalisation,[status(thm)],[c_1477,c_1125]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1812,plain,
% 7.71/1.61      ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
% 7.71/1.61      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_1807,c_712]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1925,plain,
% 7.71/1.61      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.71/1.61      inference(global_propositional_subsumption,[status(thm)],[c_1812,c_729]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1932,plain,
% 7.71/1.61      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_1925,c_714]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1281,plain,
% 7.71/1.61      ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_729,c_711]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1810,plain,
% 7.71/1.61      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 7.71/1.61      inference(demodulation,[status(thm)],[c_1807,c_1281]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_1937,plain,
% 7.71/1.61      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 7.71/1.61      inference(light_normalisation,[status(thm)],[c_1932,c_1810]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_3068,plain,
% 7.71/1.61      ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_1946,c_1937]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_14019,plain,
% 7.71/1.61      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_9397,c_3068]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_12,plain,
% 7.71/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.71/1.61      | ~ l1_pre_topc(X1)
% 7.71/1.61      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.71/1.61      inference(cnf_transformation,[],[f48]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_708,plain,
% 7.71/1.61      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 7.71/1.61      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.71/1.61      | l1_pre_topc(X0) != iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_9396,plain,
% 7.71/1.61      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
% 7.71/1.61      | l1_pre_topc(sK0) != iProver_top ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_9375,c_708]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_14,plain,
% 7.71/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.71/1.61      | ~ v2_pre_topc(X1)
% 7.71/1.61      | ~ l1_pre_topc(X1)
% 7.71/1.61      | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
% 7.71/1.61      inference(cnf_transformation,[],[f50]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_706,plain,
% 7.71/1.61      ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
% 7.71/1.61      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.71/1.61      | v2_pre_topc(X0) != iProver_top
% 7.71/1.61      | l1_pre_topc(X0) != iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_2430,plain,
% 7.71/1.61      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_xboole_0
% 7.71/1.61      | v2_pre_topc(sK0) != iProver_top
% 7.71/1.61      | l1_pre_topc(sK0) != iProver_top ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_705,c_706]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_18,negated_conjecture,
% 7.71/1.61      ( v2_pre_topc(sK0) ),
% 7.71/1.61      inference(cnf_transformation,[],[f51]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_905,plain,
% 7.71/1.61      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.71/1.61      | ~ v2_pre_topc(sK0)
% 7.71/1.61      | ~ l1_pre_topc(sK0)
% 7.71/1.61      | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_xboole_0 ),
% 7.71/1.61      inference(instantiation,[status(thm)],[c_14]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_2907,plain,
% 7.71/1.61      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_xboole_0 ),
% 7.71/1.61      inference(global_propositional_subsumption,
% 7.71/1.61                [status(thm)],
% 7.71/1.61                [c_2430,c_18,c_17,c_16,c_905]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_13,plain,
% 7.71/1.61      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.71/1.61      | ~ v2_pre_topc(X1)
% 7.71/1.61      | ~ l1_pre_topc(X1)
% 7.71/1.61      | k2_pre_topc(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.71/1.61      inference(cnf_transformation,[],[f49]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_707,plain,
% 7.71/1.61      ( k2_pre_topc(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 7.71/1.61      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.71/1.61      | v2_pre_topc(X0) != iProver_top
% 7.71/1.61      | l1_pre_topc(X0) != iProver_top ),
% 7.71/1.61      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_7827,plain,
% 7.71/1.61      ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1))
% 7.71/1.61      | v2_pre_topc(sK0) != iProver_top
% 7.71/1.61      | l1_pre_topc(sK0) != iProver_top ),
% 7.71/1.61      inference(superposition,[status(thm)],[c_7810,c_707]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_970,plain,
% 7.71/1.61      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.71/1.61      | ~ v2_pre_topc(sK0)
% 7.71/1.61      | ~ l1_pre_topc(sK0)
% 7.71/1.61      | k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 7.71/1.61      inference(instantiation,[status(thm)],[c_13]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_8149,plain,
% 7.71/1.61      ( k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 7.71/1.61      inference(global_propositional_subsumption,
% 7.71/1.61                [status(thm)],
% 7.71/1.61                [c_7827,c_18,c_17,c_16,c_873,c_970]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_9402,plain,
% 7.71/1.61      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
% 7.71/1.61      | l1_pre_topc(sK0) != iProver_top ),
% 7.71/1.61      inference(light_normalisation,[status(thm)],[c_9396,c_2907,c_8149]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_9912,plain,
% 7.71/1.61      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
% 7.71/1.61      inference(global_propositional_subsumption,[status(thm)],[c_9402,c_20]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_18198,plain,
% 7.71/1.61      ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 7.71/1.61      inference(demodulation,[status(thm)],[c_14019,c_9912]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_15,negated_conjecture,
% 7.71/1.61      ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
% 7.71/1.61      inference(cnf_transformation,[],[f54]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_18383,plain,
% 7.71/1.61      ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 7.71/1.61      inference(demodulation,[status(thm)],[c_18198,c_15]) ).
% 7.71/1.61  
% 7.71/1.61  cnf(c_18384,plain,
% 7.71/1.61      ( $false ),
% 7.71/1.61      inference(equality_resolution_simp,[status(thm)],[c_18383]) ).
% 7.71/1.61  
% 7.71/1.61  
% 7.71/1.61  % SZS output end CNFRefutation for theBenchmark.p
% 7.71/1.61  
% 7.71/1.61  ------                               Statistics
% 7.71/1.61  
% 7.71/1.61  ------ Selected
% 7.71/1.61  
% 7.71/1.61  total_time:                             0.595
% 7.71/1.61  
%------------------------------------------------------------------------------
