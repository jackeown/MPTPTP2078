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
% DateTime   : Thu Dec  3 12:13:37 EST 2020

% Result     : Theorem 15.20s
% Output     : CNFRefutation 15.20s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 558 expanded)
%              Number of clauses        :   83 ( 248 expanded)
%              Number of leaves         :   16 (  99 expanded)
%              Depth                    :   18
%              Number of atoms          :  329 (1427 expanded)
%              Number of equality atoms :  119 ( 383 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),X1)
      | ~ r1_tarski(k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f33,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f38,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f38])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_158,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_159,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_158])).

cnf(c_194,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_159])).

cnf(c_1101,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1102,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3178,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_1102])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X0),X2)
    | r1_tarski(k3_subset_1(X1,X2),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(k3_subset_1(X1,X2),X0)
    | r1_tarski(k3_subset_1(X1,X0),X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_159])).

cnf(c_634,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_635,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_634])).

cnf(c_660,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(k3_subset_1(X1,X2),X0)
    | r1_tarski(k3_subset_1(X1,X0),X2) ),
    inference(bin_hyper_res,[status(thm)],[c_196,c_635])).

cnf(c_1098,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X2),X0) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_3292,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3178,c_1098])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1107,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_24058,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X1),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3292,c_1107])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1104,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1649,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1102])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1108,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2481,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_1108])).

cnf(c_24097,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_24058,c_2481])).

cnf(c_52074,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24097,c_1649])).

cnf(c_6,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1105,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1119,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1105,c_5])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_1099,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_1566,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_1119,c_1099])).

cnf(c_3291,plain,
    ( k3_subset_1(X0,X1) = X0
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,k3_subset_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3178,c_1108])).

cnf(c_3533,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = u1_struct_0(sK0)
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1566,c_3291])).

cnf(c_3538,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0)
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3533,c_1566])).

cnf(c_19,negated_conjecture,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_15,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_273,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_15,c_14])).

cnf(c_349,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_273,c_20])).

cnf(c_350,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_1122,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) != u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_19,c_350])).

cnf(c_5150,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3538,c_1122])).

cnf(c_52163,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_xboole_0),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_52074,c_5150])).

cnf(c_52178,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_52074,c_1566])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_287,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_288,plain,
    ( v4_pre_topc(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_300,plain,
    ( v4_pre_topc(k1_xboole_0,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_288,c_10])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_311,plain,
    ( v4_pre_topc(k1_xboole_0,X0)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_300,c_21])).

cnf(c_312,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_305,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_314,plain,
    ( v4_pre_topc(k1_xboole_0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_21,c_20,c_305])).

cnf(c_17,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_366,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_367,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0
    | sK0 != sK0
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_314,c_367])).

cnf(c_391,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_397,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_391,c_10])).

cnf(c_52391,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_52178,c_397])).

cnf(c_52518,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_xboole_0),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_52163,c_52391])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_195,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_159])).

cnf(c_1100,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_195])).

cnf(c_2858,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1107,c_1100])).

cnf(c_52197,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_52074,c_2858])).

cnf(c_52519,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_xboole_0),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_52518,c_52197])).

cnf(c_52522,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_52519,c_397])).

cnf(c_1354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1776,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_1777,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1776])).

cnf(c_1360,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1363,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1360])).

cnf(c_1203,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1205,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1203])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52522,c_1777,c_1363,c_1205])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.20/2.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.20/2.51  
% 15.20/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.20/2.51  
% 15.20/2.51  ------  iProver source info
% 15.20/2.51  
% 15.20/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.20/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.20/2.51  git: non_committed_changes: false
% 15.20/2.51  git: last_make_outside_of_git: false
% 15.20/2.51  
% 15.20/2.51  ------ 
% 15.20/2.51  
% 15.20/2.51  ------ Input Options
% 15.20/2.51  
% 15.20/2.51  --out_options                           all
% 15.20/2.51  --tptp_safe_out                         true
% 15.20/2.51  --problem_path                          ""
% 15.20/2.51  --include_path                          ""
% 15.20/2.51  --clausifier                            res/vclausify_rel
% 15.20/2.51  --clausifier_options                    --mode clausify
% 15.20/2.51  --stdin                                 false
% 15.20/2.51  --stats_out                             all
% 15.20/2.51  
% 15.20/2.51  ------ General Options
% 15.20/2.51  
% 15.20/2.51  --fof                                   false
% 15.20/2.51  --time_out_real                         305.
% 15.20/2.51  --time_out_virtual                      -1.
% 15.20/2.51  --symbol_type_check                     false
% 15.20/2.51  --clausify_out                          false
% 15.20/2.51  --sig_cnt_out                           false
% 15.20/2.51  --trig_cnt_out                          false
% 15.20/2.51  --trig_cnt_out_tolerance                1.
% 15.20/2.51  --trig_cnt_out_sk_spl                   false
% 15.20/2.51  --abstr_cl_out                          false
% 15.20/2.51  
% 15.20/2.51  ------ Global Options
% 15.20/2.51  
% 15.20/2.51  --schedule                              default
% 15.20/2.51  --add_important_lit                     false
% 15.20/2.51  --prop_solver_per_cl                    1000
% 15.20/2.51  --min_unsat_core                        false
% 15.20/2.51  --soft_assumptions                      false
% 15.20/2.51  --soft_lemma_size                       3
% 15.20/2.51  --prop_impl_unit_size                   0
% 15.20/2.51  --prop_impl_unit                        []
% 15.20/2.51  --share_sel_clauses                     true
% 15.20/2.51  --reset_solvers                         false
% 15.20/2.51  --bc_imp_inh                            [conj_cone]
% 15.20/2.51  --conj_cone_tolerance                   3.
% 15.20/2.51  --extra_neg_conj                        none
% 15.20/2.51  --large_theory_mode                     true
% 15.20/2.51  --prolific_symb_bound                   200
% 15.20/2.51  --lt_threshold                          2000
% 15.20/2.51  --clause_weak_htbl                      true
% 15.20/2.51  --gc_record_bc_elim                     false
% 15.20/2.51  
% 15.20/2.51  ------ Preprocessing Options
% 15.20/2.51  
% 15.20/2.51  --preprocessing_flag                    true
% 15.20/2.51  --time_out_prep_mult                    0.1
% 15.20/2.51  --splitting_mode                        input
% 15.20/2.51  --splitting_grd                         true
% 15.20/2.51  --splitting_cvd                         false
% 15.20/2.51  --splitting_cvd_svl                     false
% 15.20/2.51  --splitting_nvd                         32
% 15.20/2.51  --sub_typing                            true
% 15.20/2.51  --prep_gs_sim                           true
% 15.20/2.51  --prep_unflatten                        true
% 15.20/2.51  --prep_res_sim                          true
% 15.20/2.51  --prep_upred                            true
% 15.20/2.51  --prep_sem_filter                       exhaustive
% 15.20/2.51  --prep_sem_filter_out                   false
% 15.20/2.51  --pred_elim                             true
% 15.20/2.51  --res_sim_input                         true
% 15.20/2.51  --eq_ax_congr_red                       true
% 15.20/2.51  --pure_diseq_elim                       true
% 15.20/2.51  --brand_transform                       false
% 15.20/2.51  --non_eq_to_eq                          false
% 15.20/2.51  --prep_def_merge                        true
% 15.20/2.51  --prep_def_merge_prop_impl              false
% 15.20/2.51  --prep_def_merge_mbd                    true
% 15.20/2.51  --prep_def_merge_tr_red                 false
% 15.20/2.51  --prep_def_merge_tr_cl                  false
% 15.20/2.51  --smt_preprocessing                     true
% 15.20/2.51  --smt_ac_axioms                         fast
% 15.20/2.51  --preprocessed_out                      false
% 15.20/2.51  --preprocessed_stats                    false
% 15.20/2.51  
% 15.20/2.51  ------ Abstraction refinement Options
% 15.20/2.51  
% 15.20/2.51  --abstr_ref                             []
% 15.20/2.51  --abstr_ref_prep                        false
% 15.20/2.51  --abstr_ref_until_sat                   false
% 15.20/2.51  --abstr_ref_sig_restrict                funpre
% 15.20/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.20/2.51  --abstr_ref_under                       []
% 15.20/2.51  
% 15.20/2.51  ------ SAT Options
% 15.20/2.51  
% 15.20/2.51  --sat_mode                              false
% 15.20/2.51  --sat_fm_restart_options                ""
% 15.20/2.51  --sat_gr_def                            false
% 15.20/2.51  --sat_epr_types                         true
% 15.20/2.51  --sat_non_cyclic_types                  false
% 15.20/2.51  --sat_finite_models                     false
% 15.20/2.51  --sat_fm_lemmas                         false
% 15.20/2.51  --sat_fm_prep                           false
% 15.20/2.51  --sat_fm_uc_incr                        true
% 15.20/2.51  --sat_out_model                         small
% 15.20/2.51  --sat_out_clauses                       false
% 15.20/2.51  
% 15.20/2.51  ------ QBF Options
% 15.20/2.51  
% 15.20/2.51  --qbf_mode                              false
% 15.20/2.51  --qbf_elim_univ                         false
% 15.20/2.51  --qbf_dom_inst                          none
% 15.20/2.51  --qbf_dom_pre_inst                      false
% 15.20/2.51  --qbf_sk_in                             false
% 15.20/2.51  --qbf_pred_elim                         true
% 15.20/2.51  --qbf_split                             512
% 15.20/2.51  
% 15.20/2.51  ------ BMC1 Options
% 15.20/2.51  
% 15.20/2.51  --bmc1_incremental                      false
% 15.20/2.51  --bmc1_axioms                           reachable_all
% 15.20/2.51  --bmc1_min_bound                        0
% 15.20/2.51  --bmc1_max_bound                        -1
% 15.20/2.51  --bmc1_max_bound_default                -1
% 15.20/2.51  --bmc1_symbol_reachability              true
% 15.20/2.51  --bmc1_property_lemmas                  false
% 15.20/2.51  --bmc1_k_induction                      false
% 15.20/2.51  --bmc1_non_equiv_states                 false
% 15.20/2.51  --bmc1_deadlock                         false
% 15.20/2.51  --bmc1_ucm                              false
% 15.20/2.51  --bmc1_add_unsat_core                   none
% 15.20/2.51  --bmc1_unsat_core_children              false
% 15.20/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.20/2.51  --bmc1_out_stat                         full
% 15.20/2.51  --bmc1_ground_init                      false
% 15.20/2.51  --bmc1_pre_inst_next_state              false
% 15.20/2.51  --bmc1_pre_inst_state                   false
% 15.20/2.51  --bmc1_pre_inst_reach_state             false
% 15.20/2.51  --bmc1_out_unsat_core                   false
% 15.20/2.51  --bmc1_aig_witness_out                  false
% 15.20/2.51  --bmc1_verbose                          false
% 15.20/2.51  --bmc1_dump_clauses_tptp                false
% 15.20/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.20/2.51  --bmc1_dump_file                        -
% 15.20/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.20/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.20/2.51  --bmc1_ucm_extend_mode                  1
% 15.20/2.51  --bmc1_ucm_init_mode                    2
% 15.20/2.51  --bmc1_ucm_cone_mode                    none
% 15.20/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.20/2.51  --bmc1_ucm_relax_model                  4
% 15.20/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.20/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.20/2.51  --bmc1_ucm_layered_model                none
% 15.20/2.51  --bmc1_ucm_max_lemma_size               10
% 15.20/2.51  
% 15.20/2.51  ------ AIG Options
% 15.20/2.51  
% 15.20/2.51  --aig_mode                              false
% 15.20/2.51  
% 15.20/2.51  ------ Instantiation Options
% 15.20/2.51  
% 15.20/2.51  --instantiation_flag                    true
% 15.20/2.51  --inst_sos_flag                         false
% 15.20/2.51  --inst_sos_phase                        true
% 15.20/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.20/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.20/2.51  --inst_lit_sel_side                     num_symb
% 15.20/2.51  --inst_solver_per_active                1400
% 15.20/2.51  --inst_solver_calls_frac                1.
% 15.20/2.51  --inst_passive_queue_type               priority_queues
% 15.20/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.20/2.51  --inst_passive_queues_freq              [25;2]
% 15.20/2.51  --inst_dismatching                      true
% 15.20/2.51  --inst_eager_unprocessed_to_passive     true
% 15.20/2.51  --inst_prop_sim_given                   true
% 15.20/2.51  --inst_prop_sim_new                     false
% 15.20/2.51  --inst_subs_new                         false
% 15.20/2.51  --inst_eq_res_simp                      false
% 15.20/2.51  --inst_subs_given                       false
% 15.20/2.51  --inst_orphan_elimination               true
% 15.20/2.51  --inst_learning_loop_flag               true
% 15.20/2.51  --inst_learning_start                   3000
% 15.20/2.51  --inst_learning_factor                  2
% 15.20/2.51  --inst_start_prop_sim_after_learn       3
% 15.20/2.51  --inst_sel_renew                        solver
% 15.20/2.51  --inst_lit_activity_flag                true
% 15.20/2.51  --inst_restr_to_given                   false
% 15.20/2.51  --inst_activity_threshold               500
% 15.20/2.51  --inst_out_proof                        true
% 15.20/2.51  
% 15.20/2.51  ------ Resolution Options
% 15.20/2.51  
% 15.20/2.51  --resolution_flag                       true
% 15.20/2.51  --res_lit_sel                           adaptive
% 15.20/2.51  --res_lit_sel_side                      none
% 15.20/2.51  --res_ordering                          kbo
% 15.20/2.51  --res_to_prop_solver                    active
% 15.20/2.51  --res_prop_simpl_new                    false
% 15.20/2.51  --res_prop_simpl_given                  true
% 15.20/2.51  --res_passive_queue_type                priority_queues
% 15.20/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.20/2.51  --res_passive_queues_freq               [15;5]
% 15.20/2.51  --res_forward_subs                      full
% 15.20/2.51  --res_backward_subs                     full
% 15.20/2.51  --res_forward_subs_resolution           true
% 15.20/2.51  --res_backward_subs_resolution          true
% 15.20/2.51  --res_orphan_elimination                true
% 15.20/2.51  --res_time_limit                        2.
% 15.20/2.51  --res_out_proof                         true
% 15.20/2.51  
% 15.20/2.51  ------ Superposition Options
% 15.20/2.51  
% 15.20/2.51  --superposition_flag                    true
% 15.20/2.51  --sup_passive_queue_type                priority_queues
% 15.20/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.20/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.20/2.51  --demod_completeness_check              fast
% 15.20/2.51  --demod_use_ground                      true
% 15.20/2.51  --sup_to_prop_solver                    passive
% 15.20/2.51  --sup_prop_simpl_new                    true
% 15.20/2.51  --sup_prop_simpl_given                  true
% 15.20/2.51  --sup_fun_splitting                     false
% 15.20/2.51  --sup_smt_interval                      50000
% 15.20/2.51  
% 15.20/2.51  ------ Superposition Simplification Setup
% 15.20/2.51  
% 15.20/2.51  --sup_indices_passive                   []
% 15.20/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.20/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.20/2.51  --sup_full_bw                           [BwDemod]
% 15.20/2.51  --sup_immed_triv                        [TrivRules]
% 15.20/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.20/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.20/2.51  --sup_immed_bw_main                     []
% 15.20/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.20/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.20/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.20/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.20/2.51  
% 15.20/2.51  ------ Combination Options
% 15.20/2.51  
% 15.20/2.51  --comb_res_mult                         3
% 15.20/2.51  --comb_sup_mult                         2
% 15.20/2.51  --comb_inst_mult                        10
% 15.20/2.51  
% 15.20/2.51  ------ Debug Options
% 15.20/2.51  
% 15.20/2.51  --dbg_backtrace                         false
% 15.20/2.51  --dbg_dump_prop_clauses                 false
% 15.20/2.51  --dbg_dump_prop_clauses_file            -
% 15.20/2.51  --dbg_out_stat                          false
% 15.20/2.51  ------ Parsing...
% 15.20/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.20/2.51  
% 15.20/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 15.20/2.51  
% 15.20/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.20/2.51  
% 15.20/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.20/2.51  ------ Proving...
% 15.20/2.51  ------ Problem Properties 
% 15.20/2.51  
% 15.20/2.51  
% 15.20/2.51  clauses                                 15
% 15.20/2.51  conjectures                             1
% 15.20/2.51  EPR                                     3
% 15.20/2.51  Horn                                    15
% 15.20/2.51  unary                                   7
% 15.20/2.51  binary                                  5
% 15.20/2.51  lits                                    27
% 15.20/2.51  lits eq                                 7
% 15.20/2.51  fd_pure                                 0
% 15.20/2.51  fd_pseudo                               0
% 15.20/2.51  fd_cond                                 0
% 15.20/2.51  fd_pseudo_cond                          1
% 15.20/2.51  AC symbols                              0
% 15.20/2.51  
% 15.20/2.51  ------ Schedule dynamic 5 is on 
% 15.20/2.51  
% 15.20/2.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.20/2.51  
% 15.20/2.51  
% 15.20/2.51  ------ 
% 15.20/2.51  Current options:
% 15.20/2.51  ------ 
% 15.20/2.51  
% 15.20/2.51  ------ Input Options
% 15.20/2.51  
% 15.20/2.51  --out_options                           all
% 15.20/2.51  --tptp_safe_out                         true
% 15.20/2.51  --problem_path                          ""
% 15.20/2.51  --include_path                          ""
% 15.20/2.51  --clausifier                            res/vclausify_rel
% 15.20/2.51  --clausifier_options                    --mode clausify
% 15.20/2.51  --stdin                                 false
% 15.20/2.51  --stats_out                             all
% 15.20/2.51  
% 15.20/2.51  ------ General Options
% 15.20/2.51  
% 15.20/2.51  --fof                                   false
% 15.20/2.51  --time_out_real                         305.
% 15.20/2.51  --time_out_virtual                      -1.
% 15.20/2.51  --symbol_type_check                     false
% 15.20/2.51  --clausify_out                          false
% 15.20/2.51  --sig_cnt_out                           false
% 15.20/2.51  --trig_cnt_out                          false
% 15.20/2.51  --trig_cnt_out_tolerance                1.
% 15.20/2.51  --trig_cnt_out_sk_spl                   false
% 15.20/2.51  --abstr_cl_out                          false
% 15.20/2.51  
% 15.20/2.51  ------ Global Options
% 15.20/2.51  
% 15.20/2.51  --schedule                              default
% 15.20/2.51  --add_important_lit                     false
% 15.20/2.51  --prop_solver_per_cl                    1000
% 15.20/2.51  --min_unsat_core                        false
% 15.20/2.51  --soft_assumptions                      false
% 15.20/2.51  --soft_lemma_size                       3
% 15.20/2.51  --prop_impl_unit_size                   0
% 15.20/2.51  --prop_impl_unit                        []
% 15.20/2.51  --share_sel_clauses                     true
% 15.20/2.51  --reset_solvers                         false
% 15.20/2.51  --bc_imp_inh                            [conj_cone]
% 15.20/2.51  --conj_cone_tolerance                   3.
% 15.20/2.51  --extra_neg_conj                        none
% 15.20/2.51  --large_theory_mode                     true
% 15.20/2.51  --prolific_symb_bound                   200
% 15.20/2.51  --lt_threshold                          2000
% 15.20/2.51  --clause_weak_htbl                      true
% 15.20/2.51  --gc_record_bc_elim                     false
% 15.20/2.51  
% 15.20/2.51  ------ Preprocessing Options
% 15.20/2.51  
% 15.20/2.51  --preprocessing_flag                    true
% 15.20/2.51  --time_out_prep_mult                    0.1
% 15.20/2.51  --splitting_mode                        input
% 15.20/2.51  --splitting_grd                         true
% 15.20/2.51  --splitting_cvd                         false
% 15.20/2.51  --splitting_cvd_svl                     false
% 15.20/2.51  --splitting_nvd                         32
% 15.20/2.51  --sub_typing                            true
% 15.20/2.51  --prep_gs_sim                           true
% 15.20/2.51  --prep_unflatten                        true
% 15.20/2.51  --prep_res_sim                          true
% 15.20/2.51  --prep_upred                            true
% 15.20/2.51  --prep_sem_filter                       exhaustive
% 15.20/2.51  --prep_sem_filter_out                   false
% 15.20/2.51  --pred_elim                             true
% 15.20/2.51  --res_sim_input                         true
% 15.20/2.51  --eq_ax_congr_red                       true
% 15.20/2.51  --pure_diseq_elim                       true
% 15.20/2.51  --brand_transform                       false
% 15.20/2.51  --non_eq_to_eq                          false
% 15.20/2.51  --prep_def_merge                        true
% 15.20/2.51  --prep_def_merge_prop_impl              false
% 15.20/2.51  --prep_def_merge_mbd                    true
% 15.20/2.51  --prep_def_merge_tr_red                 false
% 15.20/2.51  --prep_def_merge_tr_cl                  false
% 15.20/2.51  --smt_preprocessing                     true
% 15.20/2.51  --smt_ac_axioms                         fast
% 15.20/2.51  --preprocessed_out                      false
% 15.20/2.51  --preprocessed_stats                    false
% 15.20/2.51  
% 15.20/2.51  ------ Abstraction refinement Options
% 15.20/2.51  
% 15.20/2.51  --abstr_ref                             []
% 15.20/2.51  --abstr_ref_prep                        false
% 15.20/2.51  --abstr_ref_until_sat                   false
% 15.20/2.51  --abstr_ref_sig_restrict                funpre
% 15.20/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.20/2.51  --abstr_ref_under                       []
% 15.20/2.51  
% 15.20/2.51  ------ SAT Options
% 15.20/2.51  
% 15.20/2.51  --sat_mode                              false
% 15.20/2.51  --sat_fm_restart_options                ""
% 15.20/2.51  --sat_gr_def                            false
% 15.20/2.51  --sat_epr_types                         true
% 15.20/2.51  --sat_non_cyclic_types                  false
% 15.20/2.51  --sat_finite_models                     false
% 15.20/2.51  --sat_fm_lemmas                         false
% 15.20/2.51  --sat_fm_prep                           false
% 15.20/2.51  --sat_fm_uc_incr                        true
% 15.20/2.51  --sat_out_model                         small
% 15.20/2.51  --sat_out_clauses                       false
% 15.20/2.51  
% 15.20/2.51  ------ QBF Options
% 15.20/2.51  
% 15.20/2.51  --qbf_mode                              false
% 15.20/2.51  --qbf_elim_univ                         false
% 15.20/2.51  --qbf_dom_inst                          none
% 15.20/2.51  --qbf_dom_pre_inst                      false
% 15.20/2.51  --qbf_sk_in                             false
% 15.20/2.51  --qbf_pred_elim                         true
% 15.20/2.51  --qbf_split                             512
% 15.20/2.51  
% 15.20/2.51  ------ BMC1 Options
% 15.20/2.51  
% 15.20/2.51  --bmc1_incremental                      false
% 15.20/2.51  --bmc1_axioms                           reachable_all
% 15.20/2.51  --bmc1_min_bound                        0
% 15.20/2.51  --bmc1_max_bound                        -1
% 15.20/2.51  --bmc1_max_bound_default                -1
% 15.20/2.51  --bmc1_symbol_reachability              true
% 15.20/2.51  --bmc1_property_lemmas                  false
% 15.20/2.51  --bmc1_k_induction                      false
% 15.20/2.51  --bmc1_non_equiv_states                 false
% 15.20/2.51  --bmc1_deadlock                         false
% 15.20/2.51  --bmc1_ucm                              false
% 15.20/2.51  --bmc1_add_unsat_core                   none
% 15.20/2.51  --bmc1_unsat_core_children              false
% 15.20/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.20/2.51  --bmc1_out_stat                         full
% 15.20/2.51  --bmc1_ground_init                      false
% 15.20/2.51  --bmc1_pre_inst_next_state              false
% 15.20/2.51  --bmc1_pre_inst_state                   false
% 15.20/2.51  --bmc1_pre_inst_reach_state             false
% 15.20/2.51  --bmc1_out_unsat_core                   false
% 15.20/2.51  --bmc1_aig_witness_out                  false
% 15.20/2.51  --bmc1_verbose                          false
% 15.20/2.51  --bmc1_dump_clauses_tptp                false
% 15.20/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.20/2.51  --bmc1_dump_file                        -
% 15.20/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.20/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.20/2.51  --bmc1_ucm_extend_mode                  1
% 15.20/2.51  --bmc1_ucm_init_mode                    2
% 15.20/2.51  --bmc1_ucm_cone_mode                    none
% 15.20/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.20/2.51  --bmc1_ucm_relax_model                  4
% 15.20/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.20/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.20/2.51  --bmc1_ucm_layered_model                none
% 15.20/2.51  --bmc1_ucm_max_lemma_size               10
% 15.20/2.51  
% 15.20/2.51  ------ AIG Options
% 15.20/2.51  
% 15.20/2.51  --aig_mode                              false
% 15.20/2.51  
% 15.20/2.51  ------ Instantiation Options
% 15.20/2.51  
% 15.20/2.51  --instantiation_flag                    true
% 15.20/2.51  --inst_sos_flag                         false
% 15.20/2.51  --inst_sos_phase                        true
% 15.20/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.20/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.20/2.51  --inst_lit_sel_side                     none
% 15.20/2.51  --inst_solver_per_active                1400
% 15.20/2.51  --inst_solver_calls_frac                1.
% 15.20/2.51  --inst_passive_queue_type               priority_queues
% 15.20/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.20/2.51  --inst_passive_queues_freq              [25;2]
% 15.20/2.51  --inst_dismatching                      true
% 15.20/2.51  --inst_eager_unprocessed_to_passive     true
% 15.20/2.51  --inst_prop_sim_given                   true
% 15.20/2.51  --inst_prop_sim_new                     false
% 15.20/2.51  --inst_subs_new                         false
% 15.20/2.51  --inst_eq_res_simp                      false
% 15.20/2.51  --inst_subs_given                       false
% 15.20/2.51  --inst_orphan_elimination               true
% 15.20/2.51  --inst_learning_loop_flag               true
% 15.20/2.51  --inst_learning_start                   3000
% 15.20/2.51  --inst_learning_factor                  2
% 15.20/2.51  --inst_start_prop_sim_after_learn       3
% 15.20/2.51  --inst_sel_renew                        solver
% 15.20/2.51  --inst_lit_activity_flag                true
% 15.20/2.51  --inst_restr_to_given                   false
% 15.20/2.51  --inst_activity_threshold               500
% 15.20/2.51  --inst_out_proof                        true
% 15.20/2.51  
% 15.20/2.51  ------ Resolution Options
% 15.20/2.51  
% 15.20/2.51  --resolution_flag                       false
% 15.20/2.51  --res_lit_sel                           adaptive
% 15.20/2.51  --res_lit_sel_side                      none
% 15.20/2.51  --res_ordering                          kbo
% 15.20/2.51  --res_to_prop_solver                    active
% 15.20/2.51  --res_prop_simpl_new                    false
% 15.20/2.51  --res_prop_simpl_given                  true
% 15.20/2.51  --res_passive_queue_type                priority_queues
% 15.20/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.20/2.51  --res_passive_queues_freq               [15;5]
% 15.20/2.51  --res_forward_subs                      full
% 15.20/2.51  --res_backward_subs                     full
% 15.20/2.51  --res_forward_subs_resolution           true
% 15.20/2.51  --res_backward_subs_resolution          true
% 15.20/2.51  --res_orphan_elimination                true
% 15.20/2.51  --res_time_limit                        2.
% 15.20/2.51  --res_out_proof                         true
% 15.20/2.51  
% 15.20/2.51  ------ Superposition Options
% 15.20/2.51  
% 15.20/2.51  --superposition_flag                    true
% 15.20/2.51  --sup_passive_queue_type                priority_queues
% 15.20/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.20/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.20/2.51  --demod_completeness_check              fast
% 15.20/2.51  --demod_use_ground                      true
% 15.20/2.51  --sup_to_prop_solver                    passive
% 15.20/2.51  --sup_prop_simpl_new                    true
% 15.20/2.51  --sup_prop_simpl_given                  true
% 15.20/2.51  --sup_fun_splitting                     false
% 15.20/2.51  --sup_smt_interval                      50000
% 15.20/2.51  
% 15.20/2.51  ------ Superposition Simplification Setup
% 15.20/2.51  
% 15.20/2.51  --sup_indices_passive                   []
% 15.20/2.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.20/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.20/2.51  --sup_full_bw                           [BwDemod]
% 15.20/2.51  --sup_immed_triv                        [TrivRules]
% 15.20/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.20/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.20/2.51  --sup_immed_bw_main                     []
% 15.20/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.20/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.20/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.20/2.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.20/2.51  
% 15.20/2.51  ------ Combination Options
% 15.20/2.51  
% 15.20/2.51  --comb_res_mult                         3
% 15.20/2.51  --comb_sup_mult                         2
% 15.20/2.51  --comb_inst_mult                        10
% 15.20/2.51  
% 15.20/2.51  ------ Debug Options
% 15.20/2.51  
% 15.20/2.51  --dbg_backtrace                         false
% 15.20/2.51  --dbg_dump_prop_clauses                 false
% 15.20/2.51  --dbg_dump_prop_clauses_file            -
% 15.20/2.51  --dbg_out_stat                          false
% 15.20/2.51  
% 15.20/2.51  
% 15.20/2.51  
% 15.20/2.51  
% 15.20/2.51  ------ Proving...
% 15.20/2.51  
% 15.20/2.51  
% 15.20/2.51  % SZS status Theorem for theBenchmark.p
% 15.20/2.51  
% 15.20/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.20/2.51  
% 15.20/2.51  fof(f6,axiom,(
% 15.20/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f22,plain,(
% 15.20/2.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.51    inference(ennf_transformation,[],[f6])).
% 15.20/2.51  
% 15.20/2.51  fof(f47,plain,(
% 15.20/2.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.51    inference(cnf_transformation,[],[f22])).
% 15.20/2.51  
% 15.20/2.51  fof(f10,axiom,(
% 15.20/2.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f37,plain,(
% 15.20/2.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.20/2.51    inference(nnf_transformation,[],[f10])).
% 15.20/2.51  
% 15.20/2.51  fof(f52,plain,(
% 15.20/2.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.20/2.51    inference(cnf_transformation,[],[f37])).
% 15.20/2.51  
% 15.20/2.51  fof(f51,plain,(
% 15.20/2.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.20/2.51    inference(cnf_transformation,[],[f37])).
% 15.20/2.51  
% 15.20/2.51  fof(f8,axiom,(
% 15.20/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f24,plain,(
% 15.20/2.51    ! [X0,X1] : (! [X2] : ((r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.51    inference(ennf_transformation,[],[f8])).
% 15.20/2.51  
% 15.20/2.51  fof(f25,plain,(
% 15.20/2.51    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.51    inference(flattening,[],[f24])).
% 15.20/2.51  
% 15.20/2.51  fof(f49,plain,(
% 15.20/2.51    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.51    inference(cnf_transformation,[],[f25])).
% 15.20/2.51  
% 15.20/2.51  fof(f2,axiom,(
% 15.20/2.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f35,plain,(
% 15.20/2.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.20/2.51    inference(nnf_transformation,[],[f2])).
% 15.20/2.51  
% 15.20/2.51  fof(f36,plain,(
% 15.20/2.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.20/2.51    inference(flattening,[],[f35])).
% 15.20/2.51  
% 15.20/2.51  fof(f41,plain,(
% 15.20/2.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.20/2.51    inference(cnf_transformation,[],[f36])).
% 15.20/2.51  
% 15.20/2.51  fof(f63,plain,(
% 15.20/2.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.20/2.51    inference(equality_resolution,[],[f41])).
% 15.20/2.51  
% 15.20/2.51  fof(f9,axiom,(
% 15.20/2.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f50,plain,(
% 15.20/2.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.20/2.51    inference(cnf_transformation,[],[f9])).
% 15.20/2.51  
% 15.20/2.51  fof(f43,plain,(
% 15.20/2.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.20/2.51    inference(cnf_transformation,[],[f36])).
% 15.20/2.51  
% 15.20/2.51  fof(f5,axiom,(
% 15.20/2.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f46,plain,(
% 15.20/2.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 15.20/2.51    inference(cnf_transformation,[],[f5])).
% 15.20/2.51  
% 15.20/2.51  fof(f4,axiom,(
% 15.20/2.51    ! [X0] : k2_subset_1(X0) = X0),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f45,plain,(
% 15.20/2.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 15.20/2.51    inference(cnf_transformation,[],[f4])).
% 15.20/2.51  
% 15.20/2.51  fof(f16,axiom,(
% 15.20/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f32,plain,(
% 15.20/2.51    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.20/2.51    inference(ennf_transformation,[],[f16])).
% 15.20/2.51  
% 15.20/2.51  fof(f58,plain,(
% 15.20/2.51    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.20/2.51    inference(cnf_transformation,[],[f32])).
% 15.20/2.51  
% 15.20/2.51  fof(f17,conjecture,(
% 15.20/2.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f18,negated_conjecture,(
% 15.20/2.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 15.20/2.51    inference(negated_conjecture,[],[f17])).
% 15.20/2.51  
% 15.20/2.51  fof(f33,plain,(
% 15.20/2.51    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.20/2.51    inference(ennf_transformation,[],[f18])).
% 15.20/2.51  
% 15.20/2.51  fof(f34,plain,(
% 15.20/2.51    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.20/2.51    inference(flattening,[],[f33])).
% 15.20/2.51  
% 15.20/2.51  fof(f38,plain,(
% 15.20/2.51    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 15.20/2.51    introduced(choice_axiom,[])).
% 15.20/2.51  
% 15.20/2.51  fof(f39,plain,(
% 15.20/2.51    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 15.20/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f38])).
% 15.20/2.51  
% 15.20/2.51  fof(f60,plain,(
% 15.20/2.51    l1_pre_topc(sK0)),
% 15.20/2.51    inference(cnf_transformation,[],[f39])).
% 15.20/2.51  
% 15.20/2.51  fof(f61,plain,(
% 15.20/2.51    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 15.20/2.51    inference(cnf_transformation,[],[f39])).
% 15.20/2.51  
% 15.20/2.51  fof(f14,axiom,(
% 15.20/2.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f29,plain,(
% 15.20/2.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 15.20/2.51    inference(ennf_transformation,[],[f14])).
% 15.20/2.51  
% 15.20/2.51  fof(f55,plain,(
% 15.20/2.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 15.20/2.51    inference(cnf_transformation,[],[f29])).
% 15.20/2.51  
% 15.20/2.51  fof(f13,axiom,(
% 15.20/2.51    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f28,plain,(
% 15.20/2.51    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 15.20/2.51    inference(ennf_transformation,[],[f13])).
% 15.20/2.51  
% 15.20/2.51  fof(f54,plain,(
% 15.20/2.51    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 15.20/2.51    inference(cnf_transformation,[],[f28])).
% 15.20/2.51  
% 15.20/2.51  fof(f1,axiom,(
% 15.20/2.51    v1_xboole_0(k1_xboole_0)),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f40,plain,(
% 15.20/2.51    v1_xboole_0(k1_xboole_0)),
% 15.20/2.51    inference(cnf_transformation,[],[f1])).
% 15.20/2.51  
% 15.20/2.51  fof(f12,axiom,(
% 15.20/2.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f26,plain,(
% 15.20/2.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.20/2.51    inference(ennf_transformation,[],[f12])).
% 15.20/2.51  
% 15.20/2.51  fof(f27,plain,(
% 15.20/2.51    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.20/2.51    inference(flattening,[],[f26])).
% 15.20/2.51  
% 15.20/2.51  fof(f53,plain,(
% 15.20/2.51    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.20/2.51    inference(cnf_transformation,[],[f27])).
% 15.20/2.51  
% 15.20/2.51  fof(f59,plain,(
% 15.20/2.51    v2_pre_topc(sK0)),
% 15.20/2.51    inference(cnf_transformation,[],[f39])).
% 15.20/2.51  
% 15.20/2.51  fof(f15,axiom,(
% 15.20/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f30,plain,(
% 15.20/2.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.20/2.51    inference(ennf_transformation,[],[f15])).
% 15.20/2.51  
% 15.20/2.51  fof(f31,plain,(
% 15.20/2.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.20/2.51    inference(flattening,[],[f30])).
% 15.20/2.51  
% 15.20/2.51  fof(f56,plain,(
% 15.20/2.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.20/2.51    inference(cnf_transformation,[],[f31])).
% 15.20/2.51  
% 15.20/2.51  fof(f7,axiom,(
% 15.20/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 15.20/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.51  
% 15.20/2.51  fof(f23,plain,(
% 15.20/2.51    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.51    inference(ennf_transformation,[],[f7])).
% 15.20/2.51  
% 15.20/2.51  fof(f48,plain,(
% 15.20/2.51    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.51    inference(cnf_transformation,[],[f23])).
% 15.20/2.51  
% 15.20/2.51  cnf(c_7,plain,
% 15.20/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.51      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 15.20/2.51      inference(cnf_transformation,[],[f47]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_11,plain,
% 15.20/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.20/2.51      inference(cnf_transformation,[],[f52]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_158,plain,
% 15.20/2.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.20/2.51      inference(prop_impl,[status(thm)],[c_11]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_159,plain,
% 15.20/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.20/2.51      inference(renaming,[status(thm)],[c_158]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_194,plain,
% 15.20/2.51      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 15.20/2.51      | ~ r1_tarski(X1,X0) ),
% 15.20/2.51      inference(bin_hyper_res,[status(thm)],[c_7,c_159]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1101,plain,
% 15.20/2.51      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 15.20/2.51      | r1_tarski(X1,X0) != iProver_top ),
% 15.20/2.51      inference(predicate_to_equality,[status(thm)],[c_194]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_12,plain,
% 15.20/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.20/2.51      inference(cnf_transformation,[],[f51]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1102,plain,
% 15.20/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.20/2.51      | r1_tarski(X0,X1) = iProver_top ),
% 15.20/2.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_3178,plain,
% 15.20/2.51      ( r1_tarski(X0,X1) != iProver_top
% 15.20/2.51      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 15.20/2.51      inference(superposition,[status(thm)],[c_1101,c_1102]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_9,plain,
% 15.20/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.20/2.51      | ~ r1_tarski(k3_subset_1(X1,X0),X2)
% 15.20/2.51      | r1_tarski(k3_subset_1(X1,X2),X0) ),
% 15.20/2.51      inference(cnf_transformation,[],[f49]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_196,plain,
% 15.20/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.51      | ~ r1_tarski(X2,X1)
% 15.20/2.51      | ~ r1_tarski(k3_subset_1(X1,X2),X0)
% 15.20/2.51      | r1_tarski(k3_subset_1(X1,X0),X2) ),
% 15.20/2.51      inference(bin_hyper_res,[status(thm)],[c_9,c_159]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_634,plain,
% 15.20/2.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.20/2.51      inference(prop_impl,[status(thm)],[c_11]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_635,plain,
% 15.20/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.20/2.51      inference(renaming,[status(thm)],[c_634]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_660,plain,
% 15.20/2.51      ( ~ r1_tarski(X0,X1)
% 15.20/2.51      | ~ r1_tarski(X2,X1)
% 15.20/2.51      | ~ r1_tarski(k3_subset_1(X1,X2),X0)
% 15.20/2.51      | r1_tarski(k3_subset_1(X1,X0),X2) ),
% 15.20/2.51      inference(bin_hyper_res,[status(thm)],[c_196,c_635]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1098,plain,
% 15.20/2.51      ( r1_tarski(X0,X1) != iProver_top
% 15.20/2.51      | r1_tarski(X2,X1) != iProver_top
% 15.20/2.51      | r1_tarski(k3_subset_1(X1,X2),X0) != iProver_top
% 15.20/2.51      | r1_tarski(k3_subset_1(X1,X0),X2) = iProver_top ),
% 15.20/2.51      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_3292,plain,
% 15.20/2.51      ( r1_tarski(X0,X1) != iProver_top
% 15.20/2.51      | r1_tarski(X1,X1) != iProver_top
% 15.20/2.51      | r1_tarski(k3_subset_1(X1,X1),X0) = iProver_top ),
% 15.20/2.51      inference(superposition,[status(thm)],[c_3178,c_1098]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_3,plain,
% 15.20/2.51      ( r1_tarski(X0,X0) ),
% 15.20/2.51      inference(cnf_transformation,[],[f63]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1107,plain,
% 15.20/2.51      ( r1_tarski(X0,X0) = iProver_top ),
% 15.20/2.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_24058,plain,
% 15.20/2.51      ( r1_tarski(X0,X1) != iProver_top
% 15.20/2.51      | r1_tarski(k3_subset_1(X1,X1),X0) = iProver_top ),
% 15.20/2.51      inference(forward_subsumption_resolution,
% 15.20/2.51                [status(thm)],
% 15.20/2.51                [c_3292,c_1107]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_10,plain,
% 15.20/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.20/2.51      inference(cnf_transformation,[],[f50]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1104,plain,
% 15.20/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.20/2.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1649,plain,
% 15.20/2.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.20/2.51      inference(superposition,[status(thm)],[c_1104,c_1102]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1,plain,
% 15.20/2.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.20/2.51      inference(cnf_transformation,[],[f43]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1108,plain,
% 15.20/2.51      ( X0 = X1
% 15.20/2.51      | r1_tarski(X0,X1) != iProver_top
% 15.20/2.51      | r1_tarski(X1,X0) != iProver_top ),
% 15.20/2.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_2481,plain,
% 15.20/2.51      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.20/2.51      inference(superposition,[status(thm)],[c_1649,c_1108]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_24097,plain,
% 15.20/2.51      ( k3_subset_1(X0,X0) = k1_xboole_0
% 15.20/2.51      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 15.20/2.51      inference(superposition,[status(thm)],[c_24058,c_2481]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_52074,plain,
% 15.20/2.51      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 15.20/2.51      inference(global_propositional_subsumption,
% 15.20/2.51                [status(thm)],
% 15.20/2.51                [c_24097,c_1649]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_6,plain,
% 15.20/2.51      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 15.20/2.51      inference(cnf_transformation,[],[f46]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1105,plain,
% 15.20/2.51      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 15.20/2.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_5,plain,
% 15.20/2.51      ( k2_subset_1(X0) = X0 ),
% 15.20/2.51      inference(cnf_transformation,[],[f45]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1119,plain,
% 15.20/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.20/2.51      inference(light_normalisation,[status(thm)],[c_1105,c_5]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_18,plain,
% 15.20/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.20/2.51      | ~ l1_pre_topc(X1)
% 15.20/2.51      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 15.20/2.51      inference(cnf_transformation,[],[f58]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_20,negated_conjecture,
% 15.20/2.51      ( l1_pre_topc(sK0) ),
% 15.20/2.51      inference(cnf_transformation,[],[f60]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_354,plain,
% 15.20/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.20/2.51      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 15.20/2.51      | sK0 != X1 ),
% 15.20/2.51      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_355,plain,
% 15.20/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.51      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 15.20/2.51      inference(unflattening,[status(thm)],[c_354]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1099,plain,
% 15.20/2.51      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 15.20/2.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.51      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1566,plain,
% 15.20/2.51      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
% 15.20/2.51      inference(superposition,[status(thm)],[c_1119,c_1099]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_3291,plain,
% 15.20/2.51      ( k3_subset_1(X0,X1) = X0
% 15.20/2.51      | r1_tarski(X1,X0) != iProver_top
% 15.20/2.51      | r1_tarski(X0,k3_subset_1(X0,X1)) != iProver_top ),
% 15.20/2.51      inference(superposition,[status(thm)],[c_3178,c_1108]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_3533,plain,
% 15.20/2.51      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = u1_struct_0(sK0)
% 15.20/2.51      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_struct_0(sK0)) != iProver_top
% 15.20/2.51      | r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.51      inference(superposition,[status(thm)],[c_1566,c_3291]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_3538,plain,
% 15.20/2.51      ( k1_tops_1(sK0,u1_struct_0(sK0)) = u1_struct_0(sK0)
% 15.20/2.51      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_struct_0(sK0)) != iProver_top
% 15.20/2.51      | r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.51      inference(demodulation,[status(thm)],[c_3533,c_1566]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_19,negated_conjecture,
% 15.20/2.51      ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
% 15.20/2.51      inference(cnf_transformation,[],[f61]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_15,plain,
% 15.20/2.51      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 15.20/2.51      inference(cnf_transformation,[],[f55]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_14,plain,
% 15.20/2.51      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 15.20/2.51      inference(cnf_transformation,[],[f54]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_273,plain,
% 15.20/2.51      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 15.20/2.51      inference(resolution,[status(thm)],[c_15,c_14]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_349,plain,
% 15.20/2.51      ( k2_struct_0(X0) = u1_struct_0(X0) | sK0 != X0 ),
% 15.20/2.51      inference(resolution_lifted,[status(thm)],[c_273,c_20]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_350,plain,
% 15.20/2.51      ( k2_struct_0(sK0) = u1_struct_0(sK0) ),
% 15.20/2.51      inference(unflattening,[status(thm)],[c_349]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1122,plain,
% 15.20/2.51      ( k1_tops_1(sK0,u1_struct_0(sK0)) != u1_struct_0(sK0) ),
% 15.20/2.51      inference(light_normalisation,[status(thm)],[c_19,c_350]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_5150,plain,
% 15.20/2.51      ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_struct_0(sK0)) != iProver_top
% 15.20/2.51      | r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.51      inference(global_propositional_subsumption,
% 15.20/2.51                [status(thm)],
% 15.20/2.51                [c_3538,c_1122]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_52163,plain,
% 15.20/2.51      ( r1_tarski(k2_pre_topc(sK0,k1_xboole_0),u1_struct_0(sK0)) != iProver_top
% 15.20/2.51      | r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.51      inference(demodulation,[status(thm)],[c_52074,c_5150]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_52178,plain,
% 15.20/2.51      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
% 15.20/2.51      inference(demodulation,[status(thm)],[c_52074,c_1566]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_0,plain,
% 15.20/2.51      ( v1_xboole_0(k1_xboole_0) ),
% 15.20/2.51      inference(cnf_transformation,[],[f40]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_13,plain,
% 15.20/2.51      ( v4_pre_topc(X0,X1)
% 15.20/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.20/2.51      | ~ v2_pre_topc(X1)
% 15.20/2.51      | ~ l1_pre_topc(X1)
% 15.20/2.51      | ~ v1_xboole_0(X0) ),
% 15.20/2.51      inference(cnf_transformation,[],[f53]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_287,plain,
% 15.20/2.51      ( v4_pre_topc(X0,X1)
% 15.20/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.20/2.51      | ~ v2_pre_topc(X1)
% 15.20/2.51      | ~ l1_pre_topc(X1)
% 15.20/2.51      | k1_xboole_0 != X0 ),
% 15.20/2.51      inference(resolution_lifted,[status(thm)],[c_0,c_13]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_288,plain,
% 15.20/2.51      ( v4_pre_topc(k1_xboole_0,X0)
% 15.20/2.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 15.20/2.51      | ~ v2_pre_topc(X0)
% 15.20/2.51      | ~ l1_pre_topc(X0) ),
% 15.20/2.51      inference(unflattening,[status(thm)],[c_287]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_300,plain,
% 15.20/2.51      ( v4_pre_topc(k1_xboole_0,X0)
% 15.20/2.51      | ~ v2_pre_topc(X0)
% 15.20/2.51      | ~ l1_pre_topc(X0) ),
% 15.20/2.51      inference(forward_subsumption_resolution,
% 15.20/2.51                [status(thm)],
% 15.20/2.51                [c_288,c_10]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_21,negated_conjecture,
% 15.20/2.51      ( v2_pre_topc(sK0) ),
% 15.20/2.51      inference(cnf_transformation,[],[f59]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_311,plain,
% 15.20/2.51      ( v4_pre_topc(k1_xboole_0,X0) | ~ l1_pre_topc(X0) | sK0 != X0 ),
% 15.20/2.51      inference(resolution_lifted,[status(thm)],[c_300,c_21]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_312,plain,
% 15.20/2.51      ( v4_pre_topc(k1_xboole_0,sK0) | ~ l1_pre_topc(sK0) ),
% 15.20/2.51      inference(unflattening,[status(thm)],[c_311]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_305,plain,
% 15.20/2.51      ( v4_pre_topc(k1_xboole_0,sK0)
% 15.20/2.51      | ~ v2_pre_topc(sK0)
% 15.20/2.51      | ~ l1_pre_topc(sK0) ),
% 15.20/2.51      inference(instantiation,[status(thm)],[c_300]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_314,plain,
% 15.20/2.51      ( v4_pre_topc(k1_xboole_0,sK0) ),
% 15.20/2.51      inference(global_propositional_subsumption,
% 15.20/2.51                [status(thm)],
% 15.20/2.51                [c_312,c_21,c_20,c_305]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_17,plain,
% 15.20/2.51      ( ~ v4_pre_topc(X0,X1)
% 15.20/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.20/2.51      | ~ l1_pre_topc(X1)
% 15.20/2.51      | k2_pre_topc(X1,X0) = X0 ),
% 15.20/2.51      inference(cnf_transformation,[],[f56]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_366,plain,
% 15.20/2.51      ( ~ v4_pre_topc(X0,X1)
% 15.20/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.20/2.51      | k2_pre_topc(X1,X0) = X0
% 15.20/2.51      | sK0 != X1 ),
% 15.20/2.51      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_367,plain,
% 15.20/2.51      ( ~ v4_pre_topc(X0,sK0)
% 15.20/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.51      | k2_pre_topc(sK0,X0) = X0 ),
% 15.20/2.51      inference(unflattening,[status(thm)],[c_366]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_390,plain,
% 15.20/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.51      | k2_pre_topc(sK0,X0) = X0
% 15.20/2.51      | sK0 != sK0
% 15.20/2.51      | k1_xboole_0 != X0 ),
% 15.20/2.51      inference(resolution_lifted,[status(thm)],[c_314,c_367]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_391,plain,
% 15.20/2.51      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.51      | k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
% 15.20/2.51      inference(unflattening,[status(thm)],[c_390]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_397,plain,
% 15.20/2.51      ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
% 15.20/2.51      inference(forward_subsumption_resolution,
% 15.20/2.51                [status(thm)],
% 15.20/2.51                [c_391,c_10]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_52391,plain,
% 15.20/2.51      ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
% 15.20/2.51      inference(light_normalisation,[status(thm)],[c_52178,c_397]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_52518,plain,
% 15.20/2.51      ( r1_tarski(k2_pre_topc(sK0,k1_xboole_0),u1_struct_0(sK0)) != iProver_top
% 15.20/2.51      | r1_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) != iProver_top ),
% 15.20/2.51      inference(light_normalisation,[status(thm)],[c_52163,c_52391]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_8,plain,
% 15.20/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.51      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 15.20/2.51      inference(cnf_transformation,[],[f48]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_195,plain,
% 15.20/2.51      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 15.20/2.51      inference(bin_hyper_res,[status(thm)],[c_8,c_159]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1100,plain,
% 15.20/2.51      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 15.20/2.51      | r1_tarski(X1,X0) != iProver_top ),
% 15.20/2.51      inference(predicate_to_equality,[status(thm)],[c_195]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_2858,plain,
% 15.20/2.51      ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
% 15.20/2.51      inference(superposition,[status(thm)],[c_1107,c_1100]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_52197,plain,
% 15.20/2.51      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 15.20/2.51      inference(demodulation,[status(thm)],[c_52074,c_2858]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_52519,plain,
% 15.20/2.51      ( r1_tarski(k2_pre_topc(sK0,k1_xboole_0),u1_struct_0(sK0)) != iProver_top
% 15.20/2.51      | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top ),
% 15.20/2.51      inference(demodulation,[status(thm)],[c_52518,c_52197]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_52522,plain,
% 15.20/2.51      ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top
% 15.20/2.51      | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) != iProver_top ),
% 15.20/2.51      inference(light_normalisation,[status(thm)],[c_52519,c_397]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1354,plain,
% 15.20/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.51      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 15.20/2.51      inference(instantiation,[status(thm)],[c_12]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1776,plain,
% 15.20/2.51      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.51      | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
% 15.20/2.51      inference(instantiation,[status(thm)],[c_1354]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1777,plain,
% 15.20/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.20/2.51      | r1_tarski(k1_xboole_0,u1_struct_0(sK0)) = iProver_top ),
% 15.20/2.51      inference(predicate_to_equality,[status(thm)],[c_1776]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1360,plain,
% 15.20/2.51      ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
% 15.20/2.51      inference(instantiation,[status(thm)],[c_3]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1363,plain,
% 15.20/2.51      ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) = iProver_top ),
% 15.20/2.51      inference(predicate_to_equality,[status(thm)],[c_1360]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1203,plain,
% 15.20/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.20/2.51      inference(instantiation,[status(thm)],[c_10]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(c_1205,plain,
% 15.20/2.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.20/2.51      inference(predicate_to_equality,[status(thm)],[c_1203]) ).
% 15.20/2.51  
% 15.20/2.51  cnf(contradiction,plain,
% 15.20/2.51      ( $false ),
% 15.20/2.51      inference(minisat,[status(thm)],[c_52522,c_1777,c_1363,c_1205]) ).
% 15.20/2.51  
% 15.20/2.51  
% 15.20/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.20/2.51  
% 15.20/2.51  ------                               Statistics
% 15.20/2.51  
% 15.20/2.51  ------ General
% 15.20/2.51  
% 15.20/2.51  abstr_ref_over_cycles:                  0
% 15.20/2.51  abstr_ref_under_cycles:                 0
% 15.20/2.51  gc_basic_clause_elim:                   0
% 15.20/2.51  forced_gc_time:                         0
% 15.20/2.51  parsing_time:                           0.008
% 15.20/2.51  unif_index_cands_time:                  0.
% 15.20/2.51  unif_index_add_time:                    0.
% 15.20/2.51  orderings_time:                         0.
% 15.20/2.51  out_proof_time:                         0.011
% 15.20/2.51  total_time:                             1.53
% 15.20/2.51  num_of_symbols:                         47
% 15.20/2.51  num_of_terms:                           37456
% 15.20/2.51  
% 15.20/2.51  ------ Preprocessing
% 15.20/2.51  
% 15.20/2.51  num_of_splits:                          0
% 15.20/2.51  num_of_split_atoms:                     0
% 15.20/2.51  num_of_reused_defs:                     0
% 15.20/2.51  num_eq_ax_congr_red:                    11
% 15.20/2.51  num_of_sem_filtered_clauses:            1
% 15.20/2.51  num_of_subtypes:                        0
% 15.20/2.51  monotx_restored_types:                  0
% 15.20/2.51  sat_num_of_epr_types:                   0
% 15.20/2.51  sat_num_of_non_cyclic_types:            0
% 15.20/2.51  sat_guarded_non_collapsed_types:        0
% 15.20/2.51  num_pure_diseq_elim:                    0
% 15.20/2.51  simp_replaced_by:                       0
% 15.20/2.51  res_preprocessed:                       87
% 15.20/2.51  prep_upred:                             0
% 15.20/2.51  prep_unflattend:                        24
% 15.20/2.51  smt_new_axioms:                         0
% 15.20/2.51  pred_elim_cands:                        2
% 15.20/2.51  pred_elim:                              5
% 15.20/2.51  pred_elim_cl:                           6
% 15.20/2.51  pred_elim_cycles:                       7
% 15.20/2.51  merged_defs:                            8
% 15.20/2.51  merged_defs_ncl:                        0
% 15.20/2.51  bin_hyper_res:                          12
% 15.20/2.51  prep_cycles:                            4
% 15.20/2.51  pred_elim_time:                         0.008
% 15.20/2.51  splitting_time:                         0.
% 15.20/2.51  sem_filter_time:                        0.
% 15.20/2.51  monotx_time:                            0.
% 15.20/2.51  subtype_inf_time:                       0.
% 15.20/2.51  
% 15.20/2.51  ------ Problem properties
% 15.20/2.51  
% 15.20/2.51  clauses:                                15
% 15.20/2.51  conjectures:                            1
% 15.20/2.51  epr:                                    3
% 15.20/2.51  horn:                                   15
% 15.20/2.51  ground:                                 3
% 15.20/2.51  unary:                                  7
% 15.20/2.51  binary:                                 5
% 15.20/2.51  lits:                                   27
% 15.20/2.51  lits_eq:                                7
% 15.20/2.51  fd_pure:                                0
% 15.20/2.51  fd_pseudo:                              0
% 15.20/2.51  fd_cond:                                0
% 15.20/2.51  fd_pseudo_cond:                         1
% 15.20/2.51  ac_symbols:                             0
% 15.20/2.51  
% 15.20/2.51  ------ Propositional Solver
% 15.20/2.51  
% 15.20/2.51  prop_solver_calls:                      32
% 15.20/2.51  prop_fast_solver_calls:                 1516
% 15.20/2.51  smt_solver_calls:                       0
% 15.20/2.51  smt_fast_solver_calls:                  0
% 15.20/2.51  prop_num_of_clauses:                    16282
% 15.20/2.51  prop_preprocess_simplified:             20972
% 15.20/2.51  prop_fo_subsumed:                       17
% 15.20/2.51  prop_solver_time:                       0.
% 15.20/2.51  smt_solver_time:                        0.
% 15.20/2.51  smt_fast_solver_time:                   0.
% 15.20/2.51  prop_fast_solver_time:                  0.
% 15.20/2.51  prop_unsat_core_time:                   0.001
% 15.20/2.51  
% 15.20/2.51  ------ QBF
% 15.20/2.51  
% 15.20/2.51  qbf_q_res:                              0
% 15.20/2.51  qbf_num_tautologies:                    0
% 15.20/2.51  qbf_prep_cycles:                        0
% 15.20/2.51  
% 15.20/2.51  ------ BMC1
% 15.20/2.51  
% 15.20/2.51  bmc1_current_bound:                     -1
% 15.20/2.51  bmc1_last_solved_bound:                 -1
% 15.20/2.51  bmc1_unsat_core_size:                   -1
% 15.20/2.51  bmc1_unsat_core_parents_size:           -1
% 15.20/2.51  bmc1_merge_next_fun:                    0
% 15.20/2.51  bmc1_unsat_core_clauses_time:           0.
% 15.20/2.51  
% 15.20/2.51  ------ Instantiation
% 15.20/2.51  
% 15.20/2.51  inst_num_of_clauses:                    3673
% 15.20/2.51  inst_num_in_passive:                    503
% 15.20/2.51  inst_num_in_active:                     1413
% 15.20/2.51  inst_num_in_unprocessed:                1757
% 15.20/2.51  inst_num_of_loops:                      1460
% 15.20/2.51  inst_num_of_learning_restarts:          0
% 15.20/2.51  inst_num_moves_active_passive:          43
% 15.20/2.51  inst_lit_activity:                      0
% 15.20/2.51  inst_lit_activity_moves:                0
% 15.20/2.51  inst_num_tautologies:                   0
% 15.20/2.51  inst_num_prop_implied:                  0
% 15.20/2.51  inst_num_existing_simplified:           0
% 15.20/2.51  inst_num_eq_res_simplified:             0
% 15.20/2.51  inst_num_child_elim:                    0
% 15.20/2.51  inst_num_of_dismatching_blockings:      2891
% 15.20/2.51  inst_num_of_non_proper_insts:           5456
% 15.20/2.51  inst_num_of_duplicates:                 0
% 15.20/2.51  inst_inst_num_from_inst_to_res:         0
% 15.20/2.51  inst_dismatching_checking_time:         0.
% 15.20/2.51  
% 15.20/2.51  ------ Resolution
% 15.20/2.51  
% 15.20/2.51  res_num_of_clauses:                     0
% 15.20/2.51  res_num_in_passive:                     0
% 15.20/2.51  res_num_in_active:                      0
% 15.20/2.51  res_num_of_loops:                       91
% 15.20/2.51  res_forward_subset_subsumed:            491
% 15.20/2.51  res_backward_subset_subsumed:           4
% 15.20/2.51  res_forward_subsumed:                   0
% 15.20/2.51  res_backward_subsumed:                  0
% 15.20/2.51  res_forward_subsumption_resolution:     2
% 15.20/2.51  res_backward_subsumption_resolution:    0
% 15.20/2.51  res_clause_to_clause_subsumption:       49317
% 15.20/2.51  res_orphan_elimination:                 0
% 15.20/2.51  res_tautology_del:                      686
% 15.20/2.51  res_num_eq_res_simplified:              0
% 15.20/2.51  res_num_sel_changes:                    0
% 15.20/2.51  res_moves_from_active_to_pass:          0
% 15.20/2.51  
% 15.20/2.51  ------ Superposition
% 15.20/2.51  
% 15.20/2.51  sup_time_total:                         0.
% 15.20/2.51  sup_time_generating:                    0.
% 15.20/2.51  sup_time_sim_full:                      0.
% 15.20/2.51  sup_time_sim_immed:                     0.
% 15.20/2.51  
% 15.20/2.51  sup_num_of_clauses:                     1776
% 15.20/2.51  sup_num_in_active:                      129
% 15.20/2.51  sup_num_in_passive:                     1647
% 15.20/2.51  sup_num_of_loops:                       291
% 15.20/2.51  sup_fw_superposition:                   1446
% 15.20/2.51  sup_bw_superposition:                   1252
% 15.20/2.51  sup_immediate_simplified:               684
% 15.20/2.51  sup_given_eliminated:                   0
% 15.20/2.51  comparisons_done:                       0
% 15.20/2.51  comparisons_avoided:                    0
% 15.20/2.51  
% 15.20/2.51  ------ Simplifications
% 15.20/2.51  
% 15.20/2.51  
% 15.20/2.51  sim_fw_subset_subsumed:                 65
% 15.20/2.51  sim_bw_subset_subsumed:                 33
% 15.20/2.51  sim_fw_subsumed:                        315
% 15.20/2.51  sim_bw_subsumed:                        17
% 15.20/2.51  sim_fw_subsumption_res:                 1
% 15.20/2.51  sim_bw_subsumption_res:                 0
% 15.20/2.51  sim_tautology_del:                      32
% 15.20/2.51  sim_eq_tautology_del:                   131
% 15.20/2.51  sim_eq_res_simp:                        0
% 15.20/2.51  sim_fw_demodulated:                     336
% 15.20/2.51  sim_bw_demodulated:                     162
% 15.20/2.51  sim_light_normalised:                   374
% 15.20/2.51  sim_joinable_taut:                      0
% 15.20/2.51  sim_joinable_simp:                      0
% 15.20/2.51  sim_ac_normalised:                      0
% 15.20/2.51  sim_smt_subsumption:                    0
% 15.20/2.51  
%------------------------------------------------------------------------------
