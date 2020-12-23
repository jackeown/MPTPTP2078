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
% DateTime   : Thu Dec  3 12:14:59 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  151 (1504 expanded)
%              Number of clauses        :   88 ( 532 expanded)
%              Number of leaves         :   18 ( 322 expanded)
%              Depth                    :   27
%              Number of atoms          :  382 (5248 expanded)
%              Number of equality atoms :  213 (2018 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f38,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f50,f44])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f47,f63])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f45,f63])).

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

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_874,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_883,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1264,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_883])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_885,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1634,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1264,c_885])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_875,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1717,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1634,c_875])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_889,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2248,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1717,c_889])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_887,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2667,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2248,c_887])).

cnf(c_2898,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2667,c_1717])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_884,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2503,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1634,c_884])).

cnf(c_2521,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2503,c_1634])).

cnf(c_22,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2911,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2521,c_22])).

cnf(c_2912,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2911])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_886,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2920,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2912,c_886])).

cnf(c_6456,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_2898,c_2920])).

cnf(c_19,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_876,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_878,plain,
    ( v2_tops_1(X0,X1) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1723,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1634,c_878])).

cnf(c_1724,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1723,c_1634])).

cnf(c_1972,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | v2_tops_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1724,c_22])).

cnf(c_1973,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1972])).

cnf(c_2668,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2248,c_1973])).

cnf(c_3046,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2668,c_1717])).

cnf(c_3047,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3046])).

cnf(c_15,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_880,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3394,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1634,c_880])).

cnf(c_3698,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(X0,sK0) != iProver_top
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3394,c_22])).

cnf(c_3699,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3698])).

cnf(c_3711,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2898,c_3699])).

cnf(c_4850,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3047,c_3711])).

cnf(c_5005,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_876,c_4850])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_882,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3563,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1634,c_882])).

cnf(c_3567,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3563,c_1634])).

cnf(c_3855,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3567,c_22])).

cnf(c_3856,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3855])).

cnf(c_3865,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1717,c_3856])).

cnf(c_3876,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3865,c_2248])).

cnf(c_5011,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5005,c_3876])).

cnf(c_7,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_888,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_902,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_888,c_5])).

cnf(c_2247,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_902,c_889])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_892,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_891,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1511,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_892,c_891])).

cnf(c_4479,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2247,c_1511])).

cnf(c_5014,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5011,c_4479])).

cnf(c_5115,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5014,c_3876])).

cnf(c_6463,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6456,c_5115])).

cnf(c_6464,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_6463,c_5])).

cnf(c_14,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_881,plain,
    ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
    | v1_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6725,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6464,c_881])).

cnf(c_6737,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6725,c_1634])).

cnf(c_18,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_877,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5117,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5014,c_877])).

cnf(c_5118,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5117])).

cnf(c_16,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_879,plain,
    ( v2_tops_1(X0,X1) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2108,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1634,c_879])).

cnf(c_2113,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2108,c_1634])).

cnf(c_3186,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | v2_tops_1(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2113,c_22])).

cnf(c_3187,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3186])).

cnf(c_3197,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2248,c_3187])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6737,c_5118,c_3197,c_2667,c_1717,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:52:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.89/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/0.99  
% 3.89/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.89/0.99  
% 3.89/0.99  ------  iProver source info
% 3.89/0.99  
% 3.89/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.89/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.89/0.99  git: non_committed_changes: false
% 3.89/0.99  git: last_make_outside_of_git: false
% 3.89/0.99  
% 3.89/0.99  ------ 
% 3.89/0.99  ------ Parsing...
% 3.89/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.89/0.99  
% 3.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.89/0.99  
% 3.89/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.89/0.99  
% 3.89/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/0.99  ------ Proving...
% 3.89/0.99  ------ Problem Properties 
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  clauses                                 21
% 3.89/0.99  conjectures                             4
% 3.89/0.99  EPR                                     4
% 3.89/0.99  Horn                                    20
% 3.89/0.99  unary                                   5
% 3.89/0.99  binary                                  9
% 3.89/0.99  lits                                    48
% 3.89/0.99  lits eq                                 12
% 3.89/0.99  fd_pure                                 0
% 3.89/0.99  fd_pseudo                               0
% 3.89/0.99  fd_cond                                 0
% 3.89/0.99  fd_pseudo_cond                          1
% 3.89/0.99  AC symbols                              0
% 3.89/0.99  
% 3.89/0.99  ------ Input Options Time Limit: Unbounded
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  ------ 
% 3.89/0.99  Current options:
% 3.89/0.99  ------ 
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  ------ Proving...
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  % SZS status Theorem for theBenchmark.p
% 3.89/0.99  
% 3.89/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.89/0.99  
% 3.89/0.99  fof(f16,conjecture,(
% 3.89/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f17,negated_conjecture,(
% 3.89/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.89/0.99    inference(negated_conjecture,[],[f16])).
% 3.89/0.99  
% 3.89/0.99  fof(f28,plain,(
% 3.89/0.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.89/0.99    inference(ennf_transformation,[],[f17])).
% 3.89/0.99  
% 3.89/0.99  fof(f34,plain,(
% 3.89/0.99    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.89/0.99    inference(nnf_transformation,[],[f28])).
% 3.89/0.99  
% 3.89/0.99  fof(f35,plain,(
% 3.89/0.99    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.89/0.99    inference(flattening,[],[f34])).
% 3.89/0.99  
% 3.89/0.99  fof(f37,plain,(
% 3.89/0.99    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK1) | ~v2_tops_1(sK1,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK1) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.89/0.99    introduced(choice_axiom,[])).
% 3.89/0.99  
% 3.89/0.99  fof(f36,plain,(
% 3.89/0.99    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.89/0.99    introduced(choice_axiom,[])).
% 3.89/0.99  
% 3.89/0.99  fof(f38,plain,(
% 3.89/0.99    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.89/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 3.89/0.99  
% 3.89/0.99  fof(f59,plain,(
% 3.89/0.99    l1_pre_topc(sK0)),
% 3.89/0.99    inference(cnf_transformation,[],[f38])).
% 3.89/0.99  
% 3.89/0.99  fof(f12,axiom,(
% 3.89/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f24,plain,(
% 3.89/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.89/0.99    inference(ennf_transformation,[],[f12])).
% 3.89/0.99  
% 3.89/0.99  fof(f53,plain,(
% 3.89/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f24])).
% 3.89/0.99  
% 3.89/0.99  fof(f10,axiom,(
% 3.89/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f21,plain,(
% 3.89/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.89/0.99    inference(ennf_transformation,[],[f10])).
% 3.89/0.99  
% 3.89/0.99  fof(f51,plain,(
% 3.89/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f21])).
% 3.89/0.99  
% 3.89/0.99  fof(f60,plain,(
% 3.89/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.89/0.99    inference(cnf_transformation,[],[f38])).
% 3.89/0.99  
% 3.89/0.99  fof(f5,axiom,(
% 3.89/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f18,plain,(
% 3.89/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.89/0.99    inference(ennf_transformation,[],[f5])).
% 3.89/0.99  
% 3.89/0.99  fof(f46,plain,(
% 3.89/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.89/0.99    inference(cnf_transformation,[],[f18])).
% 3.89/0.99  
% 3.89/0.99  fof(f7,axiom,(
% 3.89/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f19,plain,(
% 3.89/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.89/0.99    inference(ennf_transformation,[],[f7])).
% 3.89/0.99  
% 3.89/0.99  fof(f48,plain,(
% 3.89/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.89/0.99    inference(cnf_transformation,[],[f19])).
% 3.89/0.99  
% 3.89/0.99  fof(f11,axiom,(
% 3.89/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f22,plain,(
% 3.89/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.89/0.99    inference(ennf_transformation,[],[f11])).
% 3.89/0.99  
% 3.89/0.99  fof(f23,plain,(
% 3.89/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.89/0.99    inference(flattening,[],[f22])).
% 3.89/0.99  
% 3.89/0.99  fof(f52,plain,(
% 3.89/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f23])).
% 3.89/0.99  
% 3.89/0.99  fof(f8,axiom,(
% 3.89/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f20,plain,(
% 3.89/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.89/0.99    inference(ennf_transformation,[],[f8])).
% 3.89/0.99  
% 3.89/0.99  fof(f49,plain,(
% 3.89/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.89/0.99    inference(cnf_transformation,[],[f20])).
% 3.89/0.99  
% 3.89/0.99  fof(f61,plain,(
% 3.89/0.99    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 3.89/0.99    inference(cnf_transformation,[],[f38])).
% 3.89/0.99  
% 3.89/0.99  fof(f15,axiom,(
% 3.89/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f27,plain,(
% 3.89/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.89/0.99    inference(ennf_transformation,[],[f15])).
% 3.89/0.99  
% 3.89/0.99  fof(f33,plain,(
% 3.89/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.89/0.99    inference(nnf_transformation,[],[f27])).
% 3.89/0.99  
% 3.89/0.99  fof(f57,plain,(
% 3.89/0.99    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f33])).
% 3.89/0.99  
% 3.89/0.99  fof(f14,axiom,(
% 3.89/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f26,plain,(
% 3.89/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.89/0.99    inference(ennf_transformation,[],[f14])).
% 3.89/0.99  
% 3.89/0.99  fof(f32,plain,(
% 3.89/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.89/0.99    inference(nnf_transformation,[],[f26])).
% 3.89/0.99  
% 3.89/0.99  fof(f55,plain,(
% 3.89/0.99    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f32])).
% 3.89/0.99  
% 3.89/0.99  fof(f13,axiom,(
% 3.89/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f25,plain,(
% 3.89/0.99    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.89/0.99    inference(ennf_transformation,[],[f13])).
% 3.89/0.99  
% 3.89/0.99  fof(f54,plain,(
% 3.89/0.99    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f25])).
% 3.89/0.99  
% 3.89/0.99  fof(f6,axiom,(
% 3.89/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f47,plain,(
% 3.89/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.89/0.99    inference(cnf_transformation,[],[f6])).
% 3.89/0.99  
% 3.89/0.99  fof(f9,axiom,(
% 3.89/0.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f50,plain,(
% 3.89/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.89/0.99    inference(cnf_transformation,[],[f9])).
% 3.89/0.99  
% 3.89/0.99  fof(f3,axiom,(
% 3.89/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f44,plain,(
% 3.89/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f3])).
% 3.89/0.99  
% 3.89/0.99  fof(f63,plain,(
% 3.89/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.89/0.99    inference(definition_unfolding,[],[f50,f44])).
% 3.89/0.99  
% 3.89/0.99  fof(f65,plain,(
% 3.89/0.99    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 3.89/0.99    inference(definition_unfolding,[],[f47,f63])).
% 3.89/0.99  
% 3.89/0.99  fof(f4,axiom,(
% 3.89/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f45,plain,(
% 3.89/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.89/0.99    inference(cnf_transformation,[],[f4])).
% 3.89/0.99  
% 3.89/0.99  fof(f64,plain,(
% 3.89/0.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.89/0.99    inference(definition_unfolding,[],[f45,f63])).
% 3.89/0.99  
% 3.89/0.99  fof(f1,axiom,(
% 3.89/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f29,plain,(
% 3.89/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.89/0.99    inference(nnf_transformation,[],[f1])).
% 3.89/0.99  
% 3.89/0.99  fof(f30,plain,(
% 3.89/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.89/0.99    inference(flattening,[],[f29])).
% 3.89/0.99  
% 3.89/0.99  fof(f40,plain,(
% 3.89/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.89/0.99    inference(cnf_transformation,[],[f30])).
% 3.89/0.99  
% 3.89/0.99  fof(f66,plain,(
% 3.89/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.89/0.99    inference(equality_resolution,[],[f40])).
% 3.89/0.99  
% 3.89/0.99  fof(f2,axiom,(
% 3.89/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.89/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/0.99  
% 3.89/0.99  fof(f31,plain,(
% 3.89/0.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.89/0.99    inference(nnf_transformation,[],[f2])).
% 3.89/0.99  
% 3.89/0.99  fof(f43,plain,(
% 3.89/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f31])).
% 3.89/0.99  
% 3.89/0.99  fof(f56,plain,(
% 3.89/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f32])).
% 3.89/0.99  
% 3.89/0.99  fof(f62,plain,(
% 3.89/0.99    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 3.89/0.99    inference(cnf_transformation,[],[f38])).
% 3.89/0.99  
% 3.89/0.99  fof(f58,plain,(
% 3.89/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.89/0.99    inference(cnf_transformation,[],[f33])).
% 3.89/0.99  
% 3.89/0.99  cnf(c_21,negated_conjecture,
% 3.89/0.99      ( l1_pre_topc(sK0) ),
% 3.89/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_874,plain,
% 3.89/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_12,plain,
% 3.89/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.89/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_883,plain,
% 3.89/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1264,plain,
% 3.89/0.99      ( l1_struct_0(sK0) = iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_874,c_883]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_10,plain,
% 3.89/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.89/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_885,plain,
% 3.89/0.99      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.89/0.99      | l1_struct_0(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1634,plain,
% 3.89/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1264,c_885]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_20,negated_conjecture,
% 3.89/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.89/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_875,plain,
% 3.89/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1717,plain,
% 3.89/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_1634,c_875]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_6,plain,
% 3.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.89/0.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.89/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_889,plain,
% 3.89/0.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.89/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2248,plain,
% 3.89/0.99      ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1717,c_889]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_8,plain,
% 3.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.89/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.89/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_887,plain,
% 3.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.89/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2667,plain,
% 3.89/0.99      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.89/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_2248,c_887]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2898,plain,
% 3.89/0.99      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.89/0.99      inference(global_propositional_subsumption,
% 3.89/0.99                [status(thm)],
% 3.89/0.99                [c_2667,c_1717]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_11,plain,
% 3.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/0.99      | ~ l1_pre_topc(X1) ),
% 3.89/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_884,plain,
% 3.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.89/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.89/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2503,plain,
% 3.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.89/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1634,c_884]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2521,plain,
% 3.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.89/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_2503,c_1634]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_22,plain,
% 3.89/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2911,plain,
% 3.89/0.99      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.89/0.99      inference(global_propositional_subsumption,
% 3.89/0.99                [status(thm)],
% 3.89/0.99                [c_2521,c_22]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2912,plain,
% 3.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.89/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.89/0.99      inference(renaming,[status(thm)],[c_2911]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_9,plain,
% 3.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.89/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.89/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_886,plain,
% 3.89/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.89/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2920,plain,
% 3.89/0.99      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_2912,c_886]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_6456,plain,
% 3.89/0.99      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_2898,c_2920]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_19,negated_conjecture,
% 3.89/0.99      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 3.89/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_876,plain,
% 3.89/0.99      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
% 3.89/0.99      | v2_tops_1(sK1,sK0) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_17,plain,
% 3.89/0.99      ( ~ v2_tops_1(X0,X1)
% 3.89/0.99      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/0.99      | ~ l1_pre_topc(X1) ),
% 3.89/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_878,plain,
% 3.89/0.99      ( v2_tops_1(X0,X1) != iProver_top
% 3.89/0.99      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.89/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1723,plain,
% 3.89/0.99      ( v2_tops_1(X0,sK0) != iProver_top
% 3.89/0.99      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1634,c_878]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1724,plain,
% 3.89/0.99      ( v2_tops_1(X0,sK0) != iProver_top
% 3.89/0.99      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_1723,c_1634]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1972,plain,
% 3.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.89/0.99      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 3.89/0.99      | v2_tops_1(X0,sK0) != iProver_top ),
% 3.89/0.99      inference(global_propositional_subsumption,
% 3.89/0.99                [status(thm)],
% 3.89/0.99                [c_1724,c_22]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1973,plain,
% 3.89/0.99      ( v2_tops_1(X0,sK0) != iProver_top
% 3.89/0.99      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.89/0.99      inference(renaming,[status(thm)],[c_1972]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2668,plain,
% 3.89/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.89/0.99      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.89/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_2248,c_1973]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3046,plain,
% 3.89/0.99      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.89/0.99      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.89/0.99      inference(global_propositional_subsumption,
% 3.89/0.99                [status(thm)],
% 3.89/0.99                [c_2668,c_1717]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3047,plain,
% 3.89/0.99      ( v2_tops_1(sK1,sK0) != iProver_top
% 3.89/0.99      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 3.89/0.99      inference(renaming,[status(thm)],[c_3046]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_15,plain,
% 3.89/0.99      ( ~ v1_tops_1(X0,X1)
% 3.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/0.99      | ~ l1_pre_topc(X1)
% 3.89/0.99      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 3.89/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_880,plain,
% 3.89/0.99      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 3.89/0.99      | v1_tops_1(X1,X0) != iProver_top
% 3.89/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.89/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3394,plain,
% 3.89/0.99      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 3.89/0.99      | v1_tops_1(X0,sK0) != iProver_top
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1634,c_880]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3698,plain,
% 3.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.89/0.99      | v1_tops_1(X0,sK0) != iProver_top
% 3.89/0.99      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 3.89/0.99      inference(global_propositional_subsumption,
% 3.89/0.99                [status(thm)],
% 3.89/0.99                [c_3394,c_22]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3699,plain,
% 3.89/0.99      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 3.89/0.99      | v1_tops_1(X0,sK0) != iProver_top
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.89/0.99      inference(renaming,[status(thm)],[c_3698]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3711,plain,
% 3.89/0.99      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.89/0.99      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_2898,c_3699]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_4850,plain,
% 3.89/0.99      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.89/0.99      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_3047,c_3711]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_5005,plain,
% 3.89/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.89/0.99      | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_876,c_4850]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_13,plain,
% 3.89/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/0.99      | ~ l1_pre_topc(X1)
% 3.89/0.99      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.89/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_882,plain,
% 3.89/0.99      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 3.89/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.89/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3563,plain,
% 3.89/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1634,c_882]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3567,plain,
% 3.89/0.99      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_3563,c_1634]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3855,plain,
% 3.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.89/0.99      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 3.89/0.99      inference(global_propositional_subsumption,
% 3.89/0.99                [status(thm)],
% 3.89/0.99                [c_3567,c_22]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3856,plain,
% 3.89/0.99      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.89/0.99      inference(renaming,[status(thm)],[c_3855]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3865,plain,
% 3.89/0.99      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1717,c_3856]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3876,plain,
% 3.89/0.99      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_3865,c_2248]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_5011,plain,
% 3.89/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.89/0.99      | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_5005,c_3876]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_7,plain,
% 3.89/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 3.89/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_888,plain,
% 3.89/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_5,plain,
% 3.89/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.89/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_902,plain,
% 3.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_888,c_5]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2247,plain,
% 3.89/0.99      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_902,c_889]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1,plain,
% 3.89/0.99      ( r1_tarski(X0,X0) ),
% 3.89/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_892,plain,
% 3.89/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3,plain,
% 3.89/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.89/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_891,plain,
% 3.89/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.89/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_1511,plain,
% 3.89/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_892,c_891]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_4479,plain,
% 3.89/0.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_2247,c_1511]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_5014,plain,
% 3.89/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_5011,c_4479]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_5115,plain,
% 3.89/0.99      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_5014,c_3876]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_6463,plain,
% 3.89/0.99      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_6456,c_5115]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_6464,plain,
% 3.89/0.99      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_6463,c_5]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_14,plain,
% 3.89/0.99      ( v1_tops_1(X0,X1)
% 3.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/0.99      | ~ l1_pre_topc(X1)
% 3.89/0.99      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 3.89/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_881,plain,
% 3.89/0.99      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
% 3.89/0.99      | v1_tops_1(X1,X0) = iProver_top
% 3.89/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.89/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_6725,plain,
% 3.89/0.99      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.89/0.99      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_6464,c_881]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_6737,plain,
% 3.89/0.99      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.89/0.99      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_6725,c_1634]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_18,negated_conjecture,
% 3.89/0.99      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 3.89/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_877,plain,
% 3.89/0.99      ( k1_xboole_0 != k1_tops_1(sK0,sK1)
% 3.89/0.99      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_5117,plain,
% 3.89/0.99      ( k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.89/0.99      inference(demodulation,[status(thm)],[c_5014,c_877]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_5118,plain,
% 3.89/0.99      ( v2_tops_1(sK1,sK0) != iProver_top ),
% 3.89/0.99      inference(equality_resolution_simp,[status(thm)],[c_5117]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_16,plain,
% 3.89/0.99      ( v2_tops_1(X0,X1)
% 3.89/0.99      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.89/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.89/0.99      | ~ l1_pre_topc(X1) ),
% 3.89/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_879,plain,
% 3.89/0.99      ( v2_tops_1(X0,X1) = iProver_top
% 3.89/0.99      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.89/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.89/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2108,plain,
% 3.89/0.99      ( v2_tops_1(X0,sK0) = iProver_top
% 3.89/0.99      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_1634,c_879]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_2113,plain,
% 3.89/0.99      ( v2_tops_1(X0,sK0) = iProver_top
% 3.89/0.99      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.89/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.89/0.99      inference(light_normalisation,[status(thm)],[c_2108,c_1634]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3186,plain,
% 3.89/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.89/0.99      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.89/0.99      | v2_tops_1(X0,sK0) = iProver_top ),
% 3.89/0.99      inference(global_propositional_subsumption,
% 3.89/0.99                [status(thm)],
% 3.89/0.99                [c_2113,c_22]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3187,plain,
% 3.89/0.99      ( v2_tops_1(X0,sK0) = iProver_top
% 3.89/0.99      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 3.89/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.89/0.99      inference(renaming,[status(thm)],[c_3186]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(c_3197,plain,
% 3.89/0.99      ( v2_tops_1(sK1,sK0) = iProver_top
% 3.89/0.99      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
% 3.89/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.89/0.99      inference(superposition,[status(thm)],[c_2248,c_3187]) ).
% 3.89/0.99  
% 3.89/0.99  cnf(contradiction,plain,
% 3.89/0.99      ( $false ),
% 3.89/0.99      inference(minisat,
% 3.89/0.99                [status(thm)],
% 3.89/0.99                [c_6737,c_5118,c_3197,c_2667,c_1717,c_22]) ).
% 3.89/0.99  
% 3.89/0.99  
% 3.89/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.89/0.99  
% 3.89/0.99  ------                               Statistics
% 3.89/0.99  
% 3.89/0.99  ------ Selected
% 3.89/0.99  
% 3.89/0.99  total_time:                             0.213
% 3.89/0.99  
%------------------------------------------------------------------------------
