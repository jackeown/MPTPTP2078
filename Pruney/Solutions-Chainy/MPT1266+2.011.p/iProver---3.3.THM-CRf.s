%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:59 EST 2020

% Result     : Theorem 23.97s
% Output     : CNFRefutation 23.97s
% Verified   : 
% Statistics : Number of formulae       :  160 (1936 expanded)
%              Number of clauses        :  105 ( 740 expanded)
%              Number of leaves         :   15 ( 393 expanded)
%              Depth                    :   25
%              Number of atoms          :  422 (6561 expanded)
%              Number of equality atoms :  230 (2363 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k1_xboole_0 != k1_tops_1(X0,sK1)
          | ~ v2_tops_1(sK1,X0) )
        & ( k1_xboole_0 = k1_tops_1(X0,sK1)
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_900,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_909,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1143,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_900,c_909])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_911,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1248,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1143,c_911])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_901,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_912,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1426,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_912])).

cnf(c_1677,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1248,c_1426])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_152,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_153,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_193,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_153])).

cnf(c_899,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_3146,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1677,c_899])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_194,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_153])).

cnf(c_898,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_3549,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | r1_tarski(sK1,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_898])).

cnf(c_3888,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3549,c_1677])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_910,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2188,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_910])).

cnf(c_2199,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2188,c_1248])).

cnf(c_21,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2596,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2199,c_21])).

cnf(c_2597,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2596])).

cnf(c_2604,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2597,c_912])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_915,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2944,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2604,c_915])).

cnf(c_5640,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3888,c_2944])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_914,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_57637,plain,
    ( r1_tarski(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5640,c_914])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_917,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_57684,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_57637,c_917])).

cnf(c_3147,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2604,c_899])).

cnf(c_11670,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(superposition,[status(thm)],[c_3888,c_3147])).

cnf(c_1678,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1248,c_901])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_908,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3113,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_908])).

cnf(c_3117,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3113,c_1248])).

cnf(c_3683,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3117,c_21])).

cnf(c_3684,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3683])).

cnf(c_3693,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1678,c_3684])).

cnf(c_3700,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3693,c_3146])).

cnf(c_11675,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_11670,c_3700])).

cnf(c_12058,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11675,c_914])).

cnf(c_18,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_902,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_904,plain,
    ( v2_tops_1(X0,X1) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1685,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_904])).

cnf(c_1686,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1685,c_1248])).

cnf(c_1920,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | v2_tops_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1686,c_21])).

cnf(c_1921,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1920])).

cnf(c_3552,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_1921])).

cnf(c_4990,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3552,c_1678])).

cnf(c_4991,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4990])).

cnf(c_14,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_906,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2214,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_906])).

cnf(c_2609,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(X0,sK0) != iProver_top
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2214,c_21])).

cnf(c_2610,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2609])).

cnf(c_3895,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3888,c_2610])).

cnf(c_4997,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4991,c_3895])).

cnf(c_46335,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_902,c_4997])).

cnf(c_46352,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_46335,c_3700])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_916,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3145,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_916,c_899])).

cnf(c_1421,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_916,c_915])).

cnf(c_3155,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3145,c_1421])).

cnf(c_46355,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_46352,c_3155])).

cnf(c_57743,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_57684,c_12058,c_46355])).

cnf(c_13,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_907,plain,
    ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
    | v1_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_57758,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_57743,c_907])).

cnf(c_57786,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_57758,c_1248])).

cnf(c_410,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2005,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_4150,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_23832,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4150])).

cnf(c_4130,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1998,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4129,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1998])).

cnf(c_15,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_905,plain,
    ( v2_tops_1(X0,X1) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2070,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_905])).

cnf(c_2075,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2070,c_1248])).

cnf(c_2755,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | v2_tops_1(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2075,c_21])).

cnf(c_2756,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2755])).

cnf(c_3551,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_2756])).

cnf(c_17,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_57786,c_46355,c_23832,c_4130,c_4129,c_3551,c_3549,c_1678,c_1677,c_24,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:46:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.97/3.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.97/3.51  
% 23.97/3.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.97/3.51  
% 23.97/3.51  ------  iProver source info
% 23.97/3.51  
% 23.97/3.51  git: date: 2020-06-30 10:37:57 +0100
% 23.97/3.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.97/3.51  git: non_committed_changes: false
% 23.97/3.51  git: last_make_outside_of_git: false
% 23.97/3.51  
% 23.97/3.51  ------ 
% 23.97/3.51  ------ Parsing...
% 23.97/3.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.97/3.51  
% 23.97/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.97/3.51  
% 23.97/3.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.97/3.51  
% 23.97/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.97/3.51  ------ Proving...
% 23.97/3.51  ------ Problem Properties 
% 23.97/3.51  
% 23.97/3.51  
% 23.97/3.51  clauses                                 20
% 23.97/3.51  conjectures                             4
% 23.97/3.51  EPR                                     4
% 23.97/3.51  Horn                                    19
% 23.97/3.51  unary                                   3
% 23.97/3.51  binary                                  10
% 23.97/3.51  lits                                    48
% 23.97/3.51  lits eq                                 10
% 23.97/3.51  fd_pure                                 0
% 23.97/3.51  fd_pseudo                               0
% 23.97/3.51  fd_cond                                 0
% 23.97/3.51  fd_pseudo_cond                          1
% 23.97/3.51  AC symbols                              0
% 23.97/3.51  
% 23.97/3.51  ------ Input Options Time Limit: Unbounded
% 23.97/3.51  
% 23.97/3.51  
% 23.97/3.51  ------ 
% 23.97/3.51  Current options:
% 23.97/3.51  ------ 
% 23.97/3.51  
% 23.97/3.51  
% 23.97/3.51  
% 23.97/3.51  
% 23.97/3.51  ------ Proving...
% 23.97/3.51  
% 23.97/3.51  
% 23.97/3.51  % SZS status Theorem for theBenchmark.p
% 23.97/3.51  
% 23.97/3.51  % SZS output start CNFRefutation for theBenchmark.p
% 23.97/3.51  
% 23.97/3.51  fof(f12,conjecture,(
% 23.97/3.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 23.97/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.97/3.51  
% 23.97/3.51  fof(f13,negated_conjecture,(
% 23.97/3.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 23.97/3.51    inference(negated_conjecture,[],[f12])).
% 23.97/3.51  
% 23.97/3.51  fof(f23,plain,(
% 23.97/3.51    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 23.97/3.51    inference(ennf_transformation,[],[f13])).
% 23.97/3.51  
% 23.97/3.51  fof(f30,plain,(
% 23.97/3.51    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 23.97/3.51    inference(nnf_transformation,[],[f23])).
% 23.97/3.51  
% 23.97/3.51  fof(f31,plain,(
% 23.97/3.51    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 23.97/3.51    inference(flattening,[],[f30])).
% 23.97/3.51  
% 23.97/3.51  fof(f33,plain,(
% 23.97/3.51    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK1) | ~v2_tops_1(sK1,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK1) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 23.97/3.51    introduced(choice_axiom,[])).
% 23.97/3.51  
% 23.97/3.51  fof(f32,plain,(
% 23.97/3.51    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 23.97/3.51    introduced(choice_axiom,[])).
% 23.97/3.51  
% 23.97/3.51  fof(f34,plain,(
% 23.97/3.51    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 23.97/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 23.97/3.51  
% 23.97/3.51  fof(f52,plain,(
% 23.97/3.51    l1_pre_topc(sK0)),
% 23.97/3.51    inference(cnf_transformation,[],[f34])).
% 23.97/3.51  
% 23.97/3.51  fof(f8,axiom,(
% 23.97/3.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 23.97/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.97/3.51  
% 23.97/3.51  fof(f19,plain,(
% 23.97/3.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 23.97/3.51    inference(ennf_transformation,[],[f8])).
% 23.97/3.51  
% 23.97/3.51  fof(f46,plain,(
% 23.97/3.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 23.97/3.51    inference(cnf_transformation,[],[f19])).
% 23.97/3.51  
% 23.97/3.51  fof(f6,axiom,(
% 23.97/3.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 23.97/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.97/3.51  
% 23.97/3.51  fof(f16,plain,(
% 23.97/3.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 23.97/3.51    inference(ennf_transformation,[],[f6])).
% 23.97/3.51  
% 23.97/3.51  fof(f44,plain,(
% 23.97/3.51    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 23.97/3.51    inference(cnf_transformation,[],[f16])).
% 23.97/3.51  
% 23.97/3.51  fof(f53,plain,(
% 23.97/3.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 23.97/3.51    inference(cnf_transformation,[],[f34])).
% 23.97/3.51  
% 23.97/3.51  fof(f5,axiom,(
% 23.97/3.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.97/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.97/3.51  
% 23.97/3.51  fof(f27,plain,(
% 23.97/3.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 23.97/3.51    inference(nnf_transformation,[],[f5])).
% 23.97/3.51  
% 23.97/3.51  fof(f42,plain,(
% 23.97/3.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 23.97/3.51    inference(cnf_transformation,[],[f27])).
% 23.97/3.51  
% 23.97/3.51  fof(f3,axiom,(
% 23.97/3.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 23.97/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.97/3.51  
% 23.97/3.51  fof(f14,plain,(
% 23.97/3.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.97/3.51    inference(ennf_transformation,[],[f3])).
% 23.97/3.51  
% 23.97/3.51  fof(f40,plain,(
% 23.97/3.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.97/3.51    inference(cnf_transformation,[],[f14])).
% 23.97/3.51  
% 23.97/3.51  fof(f43,plain,(
% 23.97/3.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 23.97/3.51    inference(cnf_transformation,[],[f27])).
% 23.97/3.51  
% 23.97/3.51  fof(f4,axiom,(
% 23.97/3.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 23.97/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.97/3.51  
% 23.97/3.51  fof(f15,plain,(
% 23.97/3.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.97/3.51    inference(ennf_transformation,[],[f4])).
% 23.97/3.51  
% 23.97/3.51  fof(f41,plain,(
% 23.97/3.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.97/3.51    inference(cnf_transformation,[],[f15])).
% 23.97/3.51  
% 23.97/3.51  fof(f7,axiom,(
% 23.97/3.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 23.97/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.97/3.51  
% 23.97/3.51  fof(f17,plain,(
% 23.97/3.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 23.97/3.51    inference(ennf_transformation,[],[f7])).
% 23.97/3.51  
% 23.97/3.51  fof(f18,plain,(
% 23.97/3.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 23.97/3.51    inference(flattening,[],[f17])).
% 23.97/3.51  
% 23.97/3.51  fof(f45,plain,(
% 23.97/3.51    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.97/3.51    inference(cnf_transformation,[],[f18])).
% 23.97/3.51  
% 23.97/3.51  fof(f2,axiom,(
% 23.97/3.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 23.97/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.97/3.51  
% 23.97/3.51  fof(f26,plain,(
% 23.97/3.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 23.97/3.51    inference(nnf_transformation,[],[f2])).
% 23.97/3.51  
% 23.97/3.51  fof(f39,plain,(
% 23.97/3.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 23.97/3.51    inference(cnf_transformation,[],[f26])).
% 23.97/3.51  
% 23.97/3.51  fof(f38,plain,(
% 23.97/3.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 23.97/3.51    inference(cnf_transformation,[],[f26])).
% 23.97/3.51  
% 23.97/3.51  fof(f1,axiom,(
% 23.97/3.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.97/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.97/3.51  
% 23.97/3.51  fof(f24,plain,(
% 23.97/3.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.97/3.51    inference(nnf_transformation,[],[f1])).
% 23.97/3.51  
% 23.97/3.51  fof(f25,plain,(
% 23.97/3.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.97/3.51    inference(flattening,[],[f24])).
% 23.97/3.51  
% 23.97/3.51  fof(f37,plain,(
% 23.97/3.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.97/3.51    inference(cnf_transformation,[],[f25])).
% 23.97/3.51  
% 23.97/3.51  fof(f9,axiom,(
% 23.97/3.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 23.97/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.97/3.51  
% 23.97/3.51  fof(f20,plain,(
% 23.97/3.51    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.97/3.51    inference(ennf_transformation,[],[f9])).
% 23.97/3.51  
% 23.97/3.51  fof(f47,plain,(
% 23.97/3.51    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.97/3.51    inference(cnf_transformation,[],[f20])).
% 23.97/3.51  
% 23.97/3.51  fof(f54,plain,(
% 23.97/3.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 23.97/3.51    inference(cnf_transformation,[],[f34])).
% 23.97/3.51  
% 23.97/3.51  fof(f11,axiom,(
% 23.97/3.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 23.97/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.97/3.51  
% 23.97/3.51  fof(f22,plain,(
% 23.97/3.51    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.97/3.51    inference(ennf_transformation,[],[f11])).
% 23.97/3.51  
% 23.97/3.51  fof(f29,plain,(
% 23.97/3.51    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.97/3.51    inference(nnf_transformation,[],[f22])).
% 23.97/3.51  
% 23.97/3.51  fof(f50,plain,(
% 23.97/3.51    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.97/3.51    inference(cnf_transformation,[],[f29])).
% 23.97/3.51  
% 23.97/3.51  fof(f10,axiom,(
% 23.97/3.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 23.97/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.97/3.51  
% 23.97/3.51  fof(f21,plain,(
% 23.97/3.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.97/3.51    inference(ennf_transformation,[],[f10])).
% 23.97/3.51  
% 23.97/3.51  fof(f28,plain,(
% 23.97/3.51    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.97/3.51    inference(nnf_transformation,[],[f21])).
% 23.97/3.51  
% 23.97/3.51  fof(f48,plain,(
% 23.97/3.51    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.97/3.51    inference(cnf_transformation,[],[f28])).
% 23.97/3.51  
% 23.97/3.51  fof(f36,plain,(
% 23.97/3.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 23.97/3.51    inference(cnf_transformation,[],[f25])).
% 23.97/3.51  
% 23.97/3.51  fof(f56,plain,(
% 23.97/3.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.97/3.51    inference(equality_resolution,[],[f36])).
% 23.97/3.51  
% 23.97/3.51  fof(f49,plain,(
% 23.97/3.51    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.97/3.51    inference(cnf_transformation,[],[f28])).
% 23.97/3.51  
% 23.97/3.51  fof(f51,plain,(
% 23.97/3.51    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.97/3.51    inference(cnf_transformation,[],[f29])).
% 23.97/3.51  
% 23.97/3.51  fof(f55,plain,(
% 23.97/3.51    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 23.97/3.51    inference(cnf_transformation,[],[f34])).
% 23.97/3.51  
% 23.97/3.51  cnf(c_20,negated_conjecture,
% 23.97/3.51      ( l1_pre_topc(sK0) ),
% 23.97/3.51      inference(cnf_transformation,[],[f52]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_900,plain,
% 23.97/3.51      ( l1_pre_topc(sK0) = iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_11,plain,
% 23.97/3.51      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 23.97/3.51      inference(cnf_transformation,[],[f46]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_909,plain,
% 23.97/3.51      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_1143,plain,
% 23.97/3.51      ( l1_struct_0(sK0) = iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_900,c_909]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_9,plain,
% 23.97/3.51      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 23.97/3.51      inference(cnf_transformation,[],[f44]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_911,plain,
% 23.97/3.51      ( u1_struct_0(X0) = k2_struct_0(X0)
% 23.97/3.51      | l1_struct_0(X0) != iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_1248,plain,
% 23.97/3.51      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_1143,c_911]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_19,negated_conjecture,
% 23.97/3.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 23.97/3.51      inference(cnf_transformation,[],[f53]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_901,plain,
% 23.97/3.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_8,plain,
% 23.97/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.97/3.51      inference(cnf_transformation,[],[f42]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_912,plain,
% 23.97/3.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.97/3.51      | r1_tarski(X0,X1) = iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_1426,plain,
% 23.97/3.51      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_901,c_912]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_1677,plain,
% 23.97/3.51      ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
% 23.97/3.51      inference(demodulation,[status(thm)],[c_1248,c_1426]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_5,plain,
% 23.97/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.97/3.51      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 23.97/3.51      inference(cnf_transformation,[],[f40]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_7,plain,
% 23.97/3.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.97/3.51      inference(cnf_transformation,[],[f43]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_152,plain,
% 23.97/3.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 23.97/3.51      inference(prop_impl,[status(thm)],[c_7]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_153,plain,
% 23.97/3.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.97/3.51      inference(renaming,[status(thm)],[c_152]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_193,plain,
% 23.97/3.51      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 23.97/3.51      inference(bin_hyper_res,[status(thm)],[c_5,c_153]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_899,plain,
% 23.97/3.51      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 23.97/3.51      | r1_tarski(X1,X0) != iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3146,plain,
% 23.97/3.51      ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_1677,c_899]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_6,plain,
% 23.97/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.97/3.51      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 23.97/3.51      inference(cnf_transformation,[],[f41]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_194,plain,
% 23.97/3.51      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 23.97/3.51      | ~ r1_tarski(X1,X0) ),
% 23.97/3.51      inference(bin_hyper_res,[status(thm)],[c_6,c_153]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_898,plain,
% 23.97/3.51      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 23.97/3.51      | r1_tarski(X1,X0) != iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_194]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3549,plain,
% 23.97/3.51      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 23.97/3.51      | r1_tarski(sK1,k2_struct_0(sK0)) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_3146,c_898]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3888,plain,
% 23.97/3.51      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 23.97/3.51      inference(global_propositional_subsumption,
% 23.97/3.51                [status(thm)],
% 23.97/3.51                [c_3549,c_1677]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_10,plain,
% 23.97/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.97/3.51      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.97/3.51      | ~ l1_pre_topc(X1) ),
% 23.97/3.51      inference(cnf_transformation,[],[f45]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_910,plain,
% 23.97/3.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.97/3.51      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 23.97/3.51      | l1_pre_topc(X1) != iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2188,plain,
% 23.97/3.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.97/3.51      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 23.97/3.51      | l1_pre_topc(sK0) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_1248,c_910]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2199,plain,
% 23.97/3.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 23.97/3.51      | l1_pre_topc(sK0) != iProver_top ),
% 23.97/3.51      inference(light_normalisation,[status(thm)],[c_2188,c_1248]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_21,plain,
% 23.97/3.51      ( l1_pre_topc(sK0) = iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2596,plain,
% 23.97/3.51      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.97/3.51      inference(global_propositional_subsumption,
% 23.97/3.51                [status(thm)],
% 23.97/3.51                [c_2199,c_21]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2597,plain,
% 23.97/3.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 23.97/3.51      inference(renaming,[status(thm)],[c_2596]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2604,plain,
% 23.97/3.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) = iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_2597,c_912]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3,plain,
% 23.97/3.51      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 23.97/3.51      inference(cnf_transformation,[],[f39]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_915,plain,
% 23.97/3.51      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 23.97/3.51      | r1_tarski(X0,X1) != iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2944,plain,
% 23.97/3.51      ( k4_xboole_0(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) = k1_xboole_0
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_2604,c_915]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_5640,plain,
% 23.97/3.51      ( k4_xboole_0(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) = k1_xboole_0 ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_3888,c_2944]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_4,plain,
% 23.97/3.51      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 23.97/3.51      inference(cnf_transformation,[],[f38]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_914,plain,
% 23.97/3.51      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 23.97/3.51      | r1_tarski(X0,X1) = iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_57637,plain,
% 23.97/3.51      ( r1_tarski(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) = iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_5640,c_914]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_0,plain,
% 23.97/3.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.97/3.51      inference(cnf_transformation,[],[f37]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_917,plain,
% 23.97/3.51      ( X0 = X1
% 23.97/3.51      | r1_tarski(X0,X1) != iProver_top
% 23.97/3.51      | r1_tarski(X1,X0) != iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_57684,plain,
% 23.97/3.51      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 23.97/3.51      | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_57637,c_917]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3147,plain,
% 23.97/3.51      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X0))
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_2604,c_899]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_11670,plain,
% 23.97/3.51      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_3888,c_3147]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_1678,plain,
% 23.97/3.51      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 23.97/3.51      inference(demodulation,[status(thm)],[c_1248,c_901]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_12,plain,
% 23.97/3.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.97/3.51      | ~ l1_pre_topc(X1)
% 23.97/3.51      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 23.97/3.51      inference(cnf_transformation,[],[f47]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_908,plain,
% 23.97/3.51      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 23.97/3.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.97/3.51      | l1_pre_topc(X0) != iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3113,plain,
% 23.97/3.51      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | l1_pre_topc(sK0) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_1248,c_908]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3117,plain,
% 23.97/3.51      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | l1_pre_topc(sK0) != iProver_top ),
% 23.97/3.51      inference(light_normalisation,[status(thm)],[c_3113,c_1248]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3683,plain,
% 23.97/3.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 23.97/3.51      inference(global_propositional_subsumption,
% 23.97/3.51                [status(thm)],
% 23.97/3.51                [c_3117,c_21]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3684,plain,
% 23.97/3.51      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.97/3.51      inference(renaming,[status(thm)],[c_3683]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3693,plain,
% 23.97/3.51      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_1678,c_3684]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3700,plain,
% 23.97/3.51      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 23.97/3.51      inference(light_normalisation,[status(thm)],[c_3693,c_3146]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_11675,plain,
% 23.97/3.51      ( k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 23.97/3.51      inference(light_normalisation,[status(thm)],[c_11670,c_3700]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_12058,plain,
% 23.97/3.51      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 23.97/3.51      | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_11675,c_914]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_18,negated_conjecture,
% 23.97/3.51      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 23.97/3.51      inference(cnf_transformation,[],[f54]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_902,plain,
% 23.97/3.51      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
% 23.97/3.51      | v2_tops_1(sK1,sK0) = iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_16,plain,
% 23.97/3.51      ( ~ v2_tops_1(X0,X1)
% 23.97/3.51      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 23.97/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.97/3.51      | ~ l1_pre_topc(X1) ),
% 23.97/3.51      inference(cnf_transformation,[],[f50]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_904,plain,
% 23.97/3.51      ( v2_tops_1(X0,X1) != iProver_top
% 23.97/3.51      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.97/3.51      | l1_pre_topc(X1) != iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_1685,plain,
% 23.97/3.51      ( v2_tops_1(X0,sK0) != iProver_top
% 23.97/3.51      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.97/3.51      | l1_pre_topc(sK0) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_1248,c_904]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_1686,plain,
% 23.97/3.51      ( v2_tops_1(X0,sK0) != iProver_top
% 23.97/3.51      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | l1_pre_topc(sK0) != iProver_top ),
% 23.97/3.51      inference(light_normalisation,[status(thm)],[c_1685,c_1248]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_1920,plain,
% 23.97/3.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 23.97/3.51      | v2_tops_1(X0,sK0) != iProver_top ),
% 23.97/3.51      inference(global_propositional_subsumption,
% 23.97/3.51                [status(thm)],
% 23.97/3.51                [c_1686,c_21]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_1921,plain,
% 23.97/3.51      ( v2_tops_1(X0,sK0) != iProver_top
% 23.97/3.51      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.97/3.51      inference(renaming,[status(thm)],[c_1920]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3552,plain,
% 23.97/3.51      ( v2_tops_1(sK1,sK0) != iProver_top
% 23.97/3.51      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 23.97/3.51      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_3146,c_1921]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_4990,plain,
% 23.97/3.51      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 23.97/3.51      | v2_tops_1(sK1,sK0) != iProver_top ),
% 23.97/3.51      inference(global_propositional_subsumption,
% 23.97/3.51                [status(thm)],
% 23.97/3.51                [c_3552,c_1678]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_4991,plain,
% 23.97/3.51      ( v2_tops_1(sK1,sK0) != iProver_top
% 23.97/3.51      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 23.97/3.51      inference(renaming,[status(thm)],[c_4990]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_14,plain,
% 23.97/3.51      ( ~ v1_tops_1(X0,X1)
% 23.97/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.97/3.51      | ~ l1_pre_topc(X1)
% 23.97/3.51      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 23.97/3.51      inference(cnf_transformation,[],[f48]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_906,plain,
% 23.97/3.51      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 23.97/3.51      | v1_tops_1(X1,X0) != iProver_top
% 23.97/3.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.97/3.51      | l1_pre_topc(X0) != iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2214,plain,
% 23.97/3.51      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 23.97/3.51      | v1_tops_1(X0,sK0) != iProver_top
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | l1_pre_topc(sK0) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_1248,c_906]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2609,plain,
% 23.97/3.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | v1_tops_1(X0,sK0) != iProver_top
% 23.97/3.51      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 23.97/3.51      inference(global_propositional_subsumption,
% 23.97/3.51                [status(thm)],
% 23.97/3.51                [c_2214,c_21]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2610,plain,
% 23.97/3.51      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 23.97/3.51      | v1_tops_1(X0,sK0) != iProver_top
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.97/3.51      inference(renaming,[status(thm)],[c_2609]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3895,plain,
% 23.97/3.51      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 23.97/3.51      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_3888,c_2610]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_4997,plain,
% 23.97/3.51      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 23.97/3.51      | v2_tops_1(sK1,sK0) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_4991,c_3895]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_46335,plain,
% 23.97/3.51      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 23.97/3.51      | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_902,c_4997]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_46352,plain,
% 23.97/3.51      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 23.97/3.51      | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_46335,c_3700]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_1,plain,
% 23.97/3.51      ( r1_tarski(X0,X0) ),
% 23.97/3.51      inference(cnf_transformation,[],[f56]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_916,plain,
% 23.97/3.51      ( r1_tarski(X0,X0) = iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3145,plain,
% 23.97/3.51      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_916,c_899]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_1421,plain,
% 23.97/3.51      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_916,c_915]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3155,plain,
% 23.97/3.51      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 23.97/3.51      inference(light_normalisation,[status(thm)],[c_3145,c_1421]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_46355,plain,
% 23.97/3.51      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 23.97/3.51      inference(demodulation,[status(thm)],[c_46352,c_3155]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_57743,plain,
% 23.97/3.51      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 23.97/3.51      inference(global_propositional_subsumption,
% 23.97/3.51                [status(thm)],
% 23.97/3.51                [c_57684,c_12058,c_46355]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_13,plain,
% 23.97/3.51      ( v1_tops_1(X0,X1)
% 23.97/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.97/3.51      | ~ l1_pre_topc(X1)
% 23.97/3.51      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 23.97/3.51      inference(cnf_transformation,[],[f49]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_907,plain,
% 23.97/3.51      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
% 23.97/3.51      | v1_tops_1(X1,X0) = iProver_top
% 23.97/3.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.97/3.51      | l1_pre_topc(X0) != iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_57758,plain,
% 23.97/3.51      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 23.97/3.51      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.97/3.51      | l1_pre_topc(sK0) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_57743,c_907]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_57786,plain,
% 23.97/3.51      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 23.97/3.51      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | l1_pre_topc(sK0) != iProver_top ),
% 23.97/3.51      inference(light_normalisation,[status(thm)],[c_57758,c_1248]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_410,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2005,plain,
% 23.97/3.51      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 23.97/3.51      inference(instantiation,[status(thm)],[c_410]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_4150,plain,
% 23.97/3.51      ( X0 != k1_xboole_0
% 23.97/3.51      | k1_xboole_0 = X0
% 23.97/3.51      | k1_xboole_0 != k1_xboole_0 ),
% 23.97/3.51      inference(instantiation,[status(thm)],[c_2005]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_23832,plain,
% 23.97/3.51      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 23.97/3.51      | k1_xboole_0 = k1_tops_1(sK0,sK1)
% 23.97/3.51      | k1_xboole_0 != k1_xboole_0 ),
% 23.97/3.51      inference(instantiation,[status(thm)],[c_4150]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_4130,plain,
% 23.97/3.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 23.97/3.51      inference(instantiation,[status(thm)],[c_1]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_1998,plain,
% 23.97/3.51      ( ~ r1_tarski(X0,k1_xboole_0)
% 23.97/3.51      | ~ r1_tarski(k1_xboole_0,X0)
% 23.97/3.51      | k1_xboole_0 = X0 ),
% 23.97/3.51      inference(instantiation,[status(thm)],[c_0]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_4129,plain,
% 23.97/3.51      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 23.97/3.51      | k1_xboole_0 = k1_xboole_0 ),
% 23.97/3.51      inference(instantiation,[status(thm)],[c_1998]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_15,plain,
% 23.97/3.51      ( v2_tops_1(X0,X1)
% 23.97/3.51      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 23.97/3.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.97/3.51      | ~ l1_pre_topc(X1) ),
% 23.97/3.51      inference(cnf_transformation,[],[f51]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_905,plain,
% 23.97/3.51      ( v2_tops_1(X0,X1) = iProver_top
% 23.97/3.51      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.97/3.51      | l1_pre_topc(X1) != iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2070,plain,
% 23.97/3.51      ( v2_tops_1(X0,sK0) = iProver_top
% 23.97/3.51      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.97/3.51      | l1_pre_topc(sK0) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_1248,c_905]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2075,plain,
% 23.97/3.51      ( v2_tops_1(X0,sK0) = iProver_top
% 23.97/3.51      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | l1_pre_topc(sK0) != iProver_top ),
% 23.97/3.51      inference(light_normalisation,[status(thm)],[c_2070,c_1248]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2755,plain,
% 23.97/3.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.97/3.51      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 23.97/3.51      | v2_tops_1(X0,sK0) = iProver_top ),
% 23.97/3.51      inference(global_propositional_subsumption,
% 23.97/3.51                [status(thm)],
% 23.97/3.51                [c_2075,c_21]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_2756,plain,
% 23.97/3.51      ( v2_tops_1(X0,sK0) = iProver_top
% 23.97/3.51      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 23.97/3.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.97/3.51      inference(renaming,[status(thm)],[c_2755]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_3551,plain,
% 23.97/3.51      ( v2_tops_1(sK1,sK0) = iProver_top
% 23.97/3.51      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
% 23.97/3.51      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.97/3.51      inference(superposition,[status(thm)],[c_3146,c_2756]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_17,negated_conjecture,
% 23.97/3.51      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 23.97/3.51      inference(cnf_transformation,[],[f55]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(c_24,plain,
% 23.97/3.51      ( k1_xboole_0 != k1_tops_1(sK0,sK1)
% 23.97/3.51      | v2_tops_1(sK1,sK0) != iProver_top ),
% 23.97/3.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.97/3.51  
% 23.97/3.51  cnf(contradiction,plain,
% 23.97/3.51      ( $false ),
% 23.97/3.51      inference(minisat,
% 23.97/3.51                [status(thm)],
% 23.97/3.51                [c_57786,c_46355,c_23832,c_4130,c_4129,c_3551,c_3549,
% 23.97/3.51                 c_1678,c_1677,c_24,c_21]) ).
% 23.97/3.51  
% 23.97/3.51  
% 23.97/3.51  % SZS output end CNFRefutation for theBenchmark.p
% 23.97/3.51  
% 23.97/3.51  ------                               Statistics
% 23.97/3.51  
% 23.97/3.51  ------ Selected
% 23.97/3.51  
% 23.97/3.51  total_time:                             2.93
% 23.97/3.51  
%------------------------------------------------------------------------------
