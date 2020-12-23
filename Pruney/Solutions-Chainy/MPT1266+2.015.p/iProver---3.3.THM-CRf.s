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
% DateTime   : Thu Dec  3 12:15:00 EST 2020

% Result     : Theorem 23.80s
% Output     : CNFRefutation 23.80s
% Verified   : 
% Statistics : Number of formulae       :  160 (1419 expanded)
%              Number of clauses        :   95 ( 513 expanded)
%              Number of leaves         :   20 ( 302 expanded)
%              Depth                    :   30
%              Number of atoms          :  376 (4788 expanded)
%              Number of equality atoms :  220 (1858 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

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

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f48,f43])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f46,f62])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_661,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_665,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_649,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_658,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1205,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_649,c_658])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_660,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1334,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1205,c_660])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_659,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2082,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_659])).

cnf(c_2100,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2082,c_1334])).

cnf(c_20,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2516,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2100,c_20])).

cnf(c_2517,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2516])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_664,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2524,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2517,c_664])).

cnf(c_4763,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X0))
    | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_2524])).

cnf(c_10442,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))) ),
    inference(superposition,[status(thm)],[c_665,c_4763])).

cnf(c_17,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_651,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_650,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1401,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1334,c_650])).

cnf(c_1950,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1401,c_664])).

cnf(c_15,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_653,plain,
    ( v2_tops_1(X0,X1) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1403,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_653])).

cnf(c_1404,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1403,c_1334])).

cnf(c_1514,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | v2_tops_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1404,c_20])).

cnf(c_1515,plain,
    ( v2_tops_1(X0,sK0) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1514])).

cnf(c_2339,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1950,c_1515])).

cnf(c_2742,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2339,c_1401])).

cnf(c_2743,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2742])).

cnf(c_13,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_655,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2121,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_655])).

cnf(c_2751,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(X0,sK0) != iProver_top
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2121,c_20])).

cnf(c_2752,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2751])).

cnf(c_2760,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_2752])).

cnf(c_4159,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),X0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_2760])).

cnf(c_8407,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2743,c_4159])).

cnf(c_9442,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_651,c_8407])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_657,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3066,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_657])).

cnf(c_3070,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3066,c_1334])).

cnf(c_3614,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3070,c_20])).

cnf(c_3615,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3614])).

cnf(c_3624,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1401,c_3615])).

cnf(c_3631,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3624,c_1950])).

cnf(c_9715,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_9442,c_3631])).

cnf(c_5,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_663,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_663,c_3])).

cnf(c_1949,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_679,c_664])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_676,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_0,c_2])).

cnf(c_1954,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1949,c_676])).

cnf(c_9718,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9715,c_1954])).

cnf(c_9721,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9718,c_3631])).

cnf(c_11605,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10442,c_9721])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_662,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2525,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2517,c_662])).

cnf(c_5154,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_2525])).

cnf(c_11652,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) ),
    inference(superposition,[status(thm)],[c_665,c_5154])).

cnf(c_11667,plain,
    ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) ),
    inference(light_normalisation,[status(thm)],[c_11652,c_10442])).

cnf(c_81918,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11605,c_11667])).

cnf(c_82019,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_81918,c_3])).

cnf(c_12,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_656,plain,
    ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
    | v1_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_82038,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_82019,c_656])).

cnf(c_82146,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_82038,c_1334])).

cnf(c_14,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_654,plain,
    ( v2_tops_1(X0,X1) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1797,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_654])).

cnf(c_1802,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1797,c_1334])).

cnf(c_3753,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | v2_tops_1(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1802,c_20])).

cnf(c_3754,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3753])).

cnf(c_3765,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1950,c_3754])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_652,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9723,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9718,c_652])).

cnf(c_9724,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9723])).

cnf(c_82901,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_82146,c_20,c_1401,c_3765,c_9724])).

cnf(c_82906,plain,
    ( r1_tarski(k4_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_82901])).

cnf(c_83107,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_82906,c_665])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:31:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.80/3.45  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.80/3.45  
% 23.80/3.45  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.80/3.45  
% 23.80/3.45  ------  iProver source info
% 23.80/3.45  
% 23.80/3.45  git: date: 2020-06-30 10:37:57 +0100
% 23.80/3.45  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.80/3.45  git: non_committed_changes: false
% 23.80/3.45  git: last_make_outside_of_git: false
% 23.80/3.45  
% 23.80/3.45  ------ 
% 23.80/3.45  ------ Parsing...
% 23.80/3.45  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.80/3.45  
% 23.80/3.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 23.80/3.45  
% 23.80/3.45  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.80/3.45  
% 23.80/3.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.80/3.45  ------ Proving...
% 23.80/3.45  ------ Problem Properties 
% 23.80/3.45  
% 23.80/3.45  
% 23.80/3.45  clauses                                 20
% 23.80/3.45  conjectures                             4
% 23.80/3.45  EPR                                     2
% 23.80/3.45  Horn                                    19
% 23.80/3.45  unary                                   7
% 23.80/3.45  binary                                  7
% 23.80/3.45  lits                                    43
% 23.80/3.45  lits eq                                 11
% 23.80/3.45  fd_pure                                 0
% 23.80/3.45  fd_pseudo                               0
% 23.80/3.45  fd_cond                                 0
% 23.80/3.45  fd_pseudo_cond                          0
% 23.80/3.45  AC symbols                              0
% 23.80/3.45  
% 23.80/3.45  ------ Input Options Time Limit: Unbounded
% 23.80/3.45  
% 23.80/3.45  
% 23.80/3.45  ------ 
% 23.80/3.45  Current options:
% 23.80/3.45  ------ 
% 23.80/3.45  
% 23.80/3.45  
% 23.80/3.45  
% 23.80/3.45  
% 23.80/3.45  ------ Proving...
% 23.80/3.45  
% 23.80/3.45  
% 23.80/3.45  % SZS status Theorem for theBenchmark.p
% 23.80/3.45  
% 23.80/3.45   Resolution empty clause
% 23.80/3.45  
% 23.80/3.45  % SZS output start CNFRefutation for theBenchmark.p
% 23.80/3.45  
% 23.80/3.45  fof(f11,axiom,(
% 23.80/3.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f20,plain,(
% 23.80/3.45    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 23.80/3.45    inference(unused_predicate_definition_removal,[],[f11])).
% 23.80/3.45  
% 23.80/3.45  fof(f23,plain,(
% 23.80/3.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 23.80/3.45    inference(ennf_transformation,[],[f20])).
% 23.80/3.45  
% 23.80/3.45  fof(f49,plain,(
% 23.80/3.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 23.80/3.45    inference(cnf_transformation,[],[f23])).
% 23.80/3.45  
% 23.80/3.45  fof(f2,axiom,(
% 23.80/3.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f40,plain,(
% 23.80/3.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 23.80/3.45    inference(cnf_transformation,[],[f2])).
% 23.80/3.45  
% 23.80/3.45  fof(f18,conjecture,(
% 23.80/3.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f19,negated_conjecture,(
% 23.80/3.45    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 23.80/3.45    inference(negated_conjecture,[],[f18])).
% 23.80/3.45  
% 23.80/3.45  fof(f31,plain,(
% 23.80/3.45    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 23.80/3.45    inference(ennf_transformation,[],[f19])).
% 23.80/3.45  
% 23.80/3.45  fof(f34,plain,(
% 23.80/3.45    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 23.80/3.45    inference(nnf_transformation,[],[f31])).
% 23.80/3.45  
% 23.80/3.45  fof(f35,plain,(
% 23.80/3.45    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 23.80/3.45    inference(flattening,[],[f34])).
% 23.80/3.45  
% 23.80/3.45  fof(f37,plain,(
% 23.80/3.45    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK1) | ~v2_tops_1(sK1,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK1) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 23.80/3.45    introduced(choice_axiom,[])).
% 23.80/3.45  
% 23.80/3.45  fof(f36,plain,(
% 23.80/3.45    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 23.80/3.45    introduced(choice_axiom,[])).
% 23.80/3.45  
% 23.80/3.45  fof(f38,plain,(
% 23.80/3.45    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 23.80/3.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 23.80/3.45  
% 23.80/3.45  fof(f58,plain,(
% 23.80/3.45    l1_pre_topc(sK0)),
% 23.80/3.45    inference(cnf_transformation,[],[f38])).
% 23.80/3.45  
% 23.80/3.45  fof(f14,axiom,(
% 23.80/3.45    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f27,plain,(
% 23.80/3.45    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 23.80/3.45    inference(ennf_transformation,[],[f14])).
% 23.80/3.45  
% 23.80/3.45  fof(f52,plain,(
% 23.80/3.45    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 23.80/3.45    inference(cnf_transformation,[],[f27])).
% 23.80/3.45  
% 23.80/3.45  fof(f12,axiom,(
% 23.80/3.45    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f24,plain,(
% 23.80/3.45    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 23.80/3.45    inference(ennf_transformation,[],[f12])).
% 23.80/3.45  
% 23.80/3.45  fof(f50,plain,(
% 23.80/3.45    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 23.80/3.45    inference(cnf_transformation,[],[f24])).
% 23.80/3.45  
% 23.80/3.45  fof(f13,axiom,(
% 23.80/3.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f25,plain,(
% 23.80/3.45    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 23.80/3.45    inference(ennf_transformation,[],[f13])).
% 23.80/3.45  
% 23.80/3.45  fof(f26,plain,(
% 23.80/3.45    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 23.80/3.45    inference(flattening,[],[f25])).
% 23.80/3.45  
% 23.80/3.45  fof(f51,plain,(
% 23.80/3.45    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.80/3.45    inference(cnf_transformation,[],[f26])).
% 23.80/3.45  
% 23.80/3.45  fof(f7,axiom,(
% 23.80/3.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f21,plain,(
% 23.80/3.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.80/3.45    inference(ennf_transformation,[],[f7])).
% 23.80/3.45  
% 23.80/3.45  fof(f45,plain,(
% 23.80/3.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.80/3.45    inference(cnf_transformation,[],[f21])).
% 23.80/3.45  
% 23.80/3.45  fof(f60,plain,(
% 23.80/3.45    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 23.80/3.45    inference(cnf_transformation,[],[f38])).
% 23.80/3.45  
% 23.80/3.45  fof(f59,plain,(
% 23.80/3.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 23.80/3.45    inference(cnf_transformation,[],[f38])).
% 23.80/3.45  
% 23.80/3.45  fof(f17,axiom,(
% 23.80/3.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f30,plain,(
% 23.80/3.45    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.80/3.45    inference(ennf_transformation,[],[f17])).
% 23.80/3.45  
% 23.80/3.45  fof(f33,plain,(
% 23.80/3.45    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.80/3.45    inference(nnf_transformation,[],[f30])).
% 23.80/3.45  
% 23.80/3.45  fof(f56,plain,(
% 23.80/3.45    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.80/3.45    inference(cnf_transformation,[],[f33])).
% 23.80/3.45  
% 23.80/3.45  fof(f16,axiom,(
% 23.80/3.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f29,plain,(
% 23.80/3.45    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.80/3.45    inference(ennf_transformation,[],[f16])).
% 23.80/3.45  
% 23.80/3.45  fof(f32,plain,(
% 23.80/3.45    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.80/3.45    inference(nnf_transformation,[],[f29])).
% 23.80/3.45  
% 23.80/3.45  fof(f54,plain,(
% 23.80/3.45    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.80/3.45    inference(cnf_transformation,[],[f32])).
% 23.80/3.45  
% 23.80/3.45  fof(f15,axiom,(
% 23.80/3.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f28,plain,(
% 23.80/3.45    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.80/3.45    inference(ennf_transformation,[],[f15])).
% 23.80/3.45  
% 23.80/3.45  fof(f53,plain,(
% 23.80/3.45    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.80/3.45    inference(cnf_transformation,[],[f28])).
% 23.80/3.45  
% 23.80/3.45  fof(f8,axiom,(
% 23.80/3.45    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f46,plain,(
% 23.80/3.45    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 23.80/3.45    inference(cnf_transformation,[],[f8])).
% 23.80/3.45  
% 23.80/3.45  fof(f10,axiom,(
% 23.80/3.45    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f48,plain,(
% 23.80/3.45    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 23.80/3.45    inference(cnf_transformation,[],[f10])).
% 23.80/3.45  
% 23.80/3.45  fof(f5,axiom,(
% 23.80/3.45    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f43,plain,(
% 23.80/3.45    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 23.80/3.45    inference(cnf_transformation,[],[f5])).
% 23.80/3.45  
% 23.80/3.45  fof(f62,plain,(
% 23.80/3.45    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 23.80/3.45    inference(definition_unfolding,[],[f48,f43])).
% 23.80/3.45  
% 23.80/3.45  fof(f65,plain,(
% 23.80/3.45    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 23.80/3.45    inference(definition_unfolding,[],[f46,f62])).
% 23.80/3.45  
% 23.80/3.45  fof(f6,axiom,(
% 23.80/3.45    ! [X0] : k2_subset_1(X0) = X0),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f44,plain,(
% 23.80/3.45    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 23.80/3.45    inference(cnf_transformation,[],[f6])).
% 23.80/3.45  
% 23.80/3.45  fof(f64,plain,(
% 23.80/3.45    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 23.80/3.45    inference(definition_unfolding,[],[f44,f62])).
% 23.80/3.45  
% 23.80/3.45  fof(f1,axiom,(
% 23.80/3.45    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f39,plain,(
% 23.80/3.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 23.80/3.45    inference(cnf_transformation,[],[f1])).
% 23.80/3.45  
% 23.80/3.45  fof(f4,axiom,(
% 23.80/3.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f42,plain,(
% 23.80/3.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.80/3.45    inference(cnf_transformation,[],[f4])).
% 23.80/3.45  
% 23.80/3.45  fof(f63,plain,(
% 23.80/3.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 23.80/3.45    inference(definition_unfolding,[],[f39,f42])).
% 23.80/3.45  
% 23.80/3.45  fof(f3,axiom,(
% 23.80/3.45    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f41,plain,(
% 23.80/3.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.80/3.45    inference(cnf_transformation,[],[f3])).
% 23.80/3.45  
% 23.80/3.45  fof(f9,axiom,(
% 23.80/3.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 23.80/3.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.80/3.45  
% 23.80/3.45  fof(f22,plain,(
% 23.80/3.45    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.80/3.45    inference(ennf_transformation,[],[f9])).
% 23.80/3.45  
% 23.80/3.45  fof(f47,plain,(
% 23.80/3.45    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.80/3.45    inference(cnf_transformation,[],[f22])).
% 23.80/3.45  
% 23.80/3.45  fof(f55,plain,(
% 23.80/3.45    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.80/3.45    inference(cnf_transformation,[],[f32])).
% 23.80/3.45  
% 23.80/3.45  fof(f57,plain,(
% 23.80/3.45    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.80/3.45    inference(cnf_transformation,[],[f33])).
% 23.80/3.45  
% 23.80/3.45  fof(f61,plain,(
% 23.80/3.45    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 23.80/3.45    inference(cnf_transformation,[],[f38])).
% 23.80/3.45  
% 23.80/3.45  cnf(c_7,plain,
% 23.80/3.45      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.80/3.45      inference(cnf_transformation,[],[f49]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_661,plain,
% 23.80/3.45      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 23.80/3.45      | r1_tarski(X0,X1) != iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1,plain,
% 23.80/3.45      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 23.80/3.45      inference(cnf_transformation,[],[f40]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_665,plain,
% 23.80/3.45      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_19,negated_conjecture,
% 23.80/3.45      ( l1_pre_topc(sK0) ),
% 23.80/3.45      inference(cnf_transformation,[],[f58]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_649,plain,
% 23.80/3.45      ( l1_pre_topc(sK0) = iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_10,plain,
% 23.80/3.45      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 23.80/3.45      inference(cnf_transformation,[],[f52]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_658,plain,
% 23.80/3.45      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1205,plain,
% 23.80/3.45      ( l1_struct_0(sK0) = iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_649,c_658]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_8,plain,
% 23.80/3.45      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 23.80/3.45      inference(cnf_transformation,[],[f50]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_660,plain,
% 23.80/3.45      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_struct_0(X0) != iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1334,plain,
% 23.80/3.45      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_1205,c_660]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_9,plain,
% 23.80/3.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.45      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.45      | ~ l1_pre_topc(X1) ),
% 23.80/3.45      inference(cnf_transformation,[],[f51]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_659,plain,
% 23.80/3.45      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.80/3.45      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 23.80/3.45      | l1_pre_topc(X1) != iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2082,plain,
% 23.80/3.45      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.80/3.45      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 23.80/3.45      | l1_pre_topc(sK0) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_1334,c_659]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2100,plain,
% 23.80/3.45      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.80/3.45      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 23.80/3.45      | l1_pre_topc(sK0) != iProver_top ),
% 23.80/3.45      inference(light_normalisation,[status(thm)],[c_2082,c_1334]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_20,plain,
% 23.80/3.45      ( l1_pre_topc(sK0) = iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2516,plain,
% 23.80/3.45      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.80/3.45      inference(global_propositional_subsumption,[status(thm)],[c_2100,c_20]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2517,plain,
% 23.80/3.45      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.80/3.45      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 23.80/3.45      inference(renaming,[status(thm)],[c_2516]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_4,plain,
% 23.80/3.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.80/3.45      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 23.80/3.45      inference(cnf_transformation,[],[f45]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_664,plain,
% 23.80/3.45      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 23.80/3.45      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2524,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X0))
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_2517,c_664]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_4763,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X0))
% 23.80/3.45      | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_661,c_2524]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_10442,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))) ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_665,c_4763]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_17,negated_conjecture,
% 23.80/3.45      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 23.80/3.45      inference(cnf_transformation,[],[f60]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_651,plain,
% 23.80/3.45      ( k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) = iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_18,negated_conjecture,
% 23.80/3.45      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 23.80/3.45      inference(cnf_transformation,[],[f59]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_650,plain,
% 23.80/3.45      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1401,plain,
% 23.80/3.45      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 23.80/3.45      inference(demodulation,[status(thm)],[c_1334,c_650]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1950,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_1401,c_664]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_15,plain,
% 23.80/3.45      ( ~ v2_tops_1(X0,X1)
% 23.80/3.45      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 23.80/3.45      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.45      | ~ l1_pre_topc(X1) ),
% 23.80/3.45      inference(cnf_transformation,[],[f56]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_653,plain,
% 23.80/3.45      ( v2_tops_1(X0,X1) != iProver_top
% 23.80/3.45      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.80/3.45      | l1_pre_topc(X1) != iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1403,plain,
% 23.80/3.45      ( v2_tops_1(X0,sK0) != iProver_top
% 23.80/3.45      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.80/3.45      | l1_pre_topc(sK0) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_1334,c_653]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1404,plain,
% 23.80/3.45      ( v2_tops_1(X0,sK0) != iProver_top
% 23.80/3.45      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.80/3.45      | l1_pre_topc(sK0) != iProver_top ),
% 23.80/3.45      inference(light_normalisation,[status(thm)],[c_1403,c_1334]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1514,plain,
% 23.80/3.45      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.80/3.45      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 23.80/3.45      | v2_tops_1(X0,sK0) != iProver_top ),
% 23.80/3.45      inference(global_propositional_subsumption,[status(thm)],[c_1404,c_20]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1515,plain,
% 23.80/3.45      ( v2_tops_1(X0,sK0) != iProver_top
% 23.80/3.45      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) = iProver_top
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.80/3.45      inference(renaming,[status(thm)],[c_1514]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2339,plain,
% 23.80/3.45      ( v2_tops_1(sK1,sK0) != iProver_top
% 23.80/3.45      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 23.80/3.45      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_1950,c_1515]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2742,plain,
% 23.80/3.45      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 23.80/3.45      | v2_tops_1(sK1,sK0) != iProver_top ),
% 23.80/3.45      inference(global_propositional_subsumption,[status(thm)],[c_2339,c_1401]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2743,plain,
% 23.80/3.45      ( v2_tops_1(sK1,sK0) != iProver_top
% 23.80/3.45      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 23.80/3.45      inference(renaming,[status(thm)],[c_2742]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_13,plain,
% 23.80/3.45      ( ~ v1_tops_1(X0,X1)
% 23.80/3.45      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.45      | ~ l1_pre_topc(X1)
% 23.80/3.45      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 23.80/3.45      inference(cnf_transformation,[],[f54]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_655,plain,
% 23.80/3.45      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 23.80/3.45      | v1_tops_1(X1,X0) != iProver_top
% 23.80/3.45      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.80/3.45      | l1_pre_topc(X0) != iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2121,plain,
% 23.80/3.45      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 23.80/3.45      | v1_tops_1(X0,sK0) != iProver_top
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.80/3.45      | l1_pre_topc(sK0) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_1334,c_655]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2751,plain,
% 23.80/3.45      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.80/3.45      | v1_tops_1(X0,sK0) != iProver_top
% 23.80/3.45      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 23.80/3.45      inference(global_propositional_subsumption,[status(thm)],[c_2121,c_20]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2752,plain,
% 23.80/3.45      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 23.80/3.45      | v1_tops_1(X0,sK0) != iProver_top
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.80/3.45      inference(renaming,[status(thm)],[c_2751]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2760,plain,
% 23.80/3.45      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 23.80/3.45      | v1_tops_1(X0,sK0) != iProver_top
% 23.80/3.45      | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_661,c_2752]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_4159,plain,
% 23.80/3.45      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 23.80/3.45      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),X0),sK0) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_665,c_2760]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_8407,plain,
% 23.80/3.45      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 23.80/3.45      | v2_tops_1(sK1,sK0) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_2743,c_4159]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_9442,plain,
% 23.80/3.45      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 23.80/3.45      | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_651,c_8407]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_11,plain,
% 23.80/3.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.45      | ~ l1_pre_topc(X1)
% 23.80/3.45      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 23.80/3.45      inference(cnf_transformation,[],[f53]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_657,plain,
% 23.80/3.45      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 23.80/3.45      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.80/3.45      | l1_pre_topc(X0) != iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_3066,plain,
% 23.80/3.45      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.80/3.45      | l1_pre_topc(sK0) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_1334,c_657]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_3070,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.80/3.45      | l1_pre_topc(sK0) != iProver_top ),
% 23.80/3.45      inference(light_normalisation,[status(thm)],[c_3066,c_1334]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_3614,plain,
% 23.80/3.45      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.80/3.45      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 23.80/3.45      inference(global_propositional_subsumption,[status(thm)],[c_3070,c_20]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_3615,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.80/3.45      inference(renaming,[status(thm)],[c_3614]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_3624,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_1401,c_3615]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_3631,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 23.80/3.45      inference(light_normalisation,[status(thm)],[c_3624,c_1950]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_9715,plain,
% 23.80/3.45      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 23.80/3.45      | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_9442,c_3631]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_5,plain,
% 23.80/3.45      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 23.80/3.45      inference(cnf_transformation,[],[f65]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_663,plain,
% 23.80/3.45      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_3,plain,
% 23.80/3.45      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 23.80/3.45      inference(cnf_transformation,[],[f64]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_679,plain,
% 23.80/3.45      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 23.80/3.45      inference(light_normalisation,[status(thm)],[c_663,c_3]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1949,plain,
% 23.80/3.45      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_679,c_664]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_0,plain,
% 23.80/3.45      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 23.80/3.45      inference(cnf_transformation,[],[f63]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2,plain,
% 23.80/3.45      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.80/3.45      inference(cnf_transformation,[],[f41]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_676,plain,
% 23.80/3.45      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.80/3.45      inference(light_normalisation,[status(thm)],[c_0,c_2]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1954,plain,
% 23.80/3.45      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 23.80/3.45      inference(light_normalisation,[status(thm)],[c_1949,c_676]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_9718,plain,
% 23.80/3.45      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 23.80/3.45      inference(demodulation,[status(thm)],[c_9715,c_1954]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_9721,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 23.80/3.45      inference(demodulation,[status(thm)],[c_9718,c_3631]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_11605,plain,
% 23.80/3.45      ( k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_10442,c_9721]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_6,plain,
% 23.80/3.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.80/3.45      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 23.80/3.45      inference(cnf_transformation,[],[f47]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_662,plain,
% 23.80/3.45      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 23.80/3.45      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_2525,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_2517,c_662]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_5154,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 23.80/3.45      | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_661,c_2525]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_11652,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_665,c_5154]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_11667,plain,
% 23.80/3.45      ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) ),
% 23.80/3.45      inference(light_normalisation,[status(thm)],[c_11652,c_10442]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_81918,plain,
% 23.80/3.45      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_11605,c_11667]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_82019,plain,
% 23.80/3.45      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 23.80/3.45      inference(demodulation,[status(thm)],[c_81918,c_3]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_12,plain,
% 23.80/3.45      ( v1_tops_1(X0,X1)
% 23.80/3.45      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.45      | ~ l1_pre_topc(X1)
% 23.80/3.45      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 23.80/3.45      inference(cnf_transformation,[],[f55]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_656,plain,
% 23.80/3.45      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
% 23.80/3.45      | v1_tops_1(X1,X0) = iProver_top
% 23.80/3.45      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.80/3.45      | l1_pre_topc(X0) != iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_82038,plain,
% 23.80/3.45      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 23.80/3.45      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.80/3.45      | l1_pre_topc(sK0) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_82019,c_656]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_82146,plain,
% 23.80/3.45      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 23.80/3.45      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.80/3.45      | l1_pre_topc(sK0) != iProver_top ),
% 23.80/3.45      inference(light_normalisation,[status(thm)],[c_82038,c_1334]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_14,plain,
% 23.80/3.45      ( v2_tops_1(X0,X1)
% 23.80/3.45      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 23.80/3.45      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.80/3.45      | ~ l1_pre_topc(X1) ),
% 23.80/3.45      inference(cnf_transformation,[],[f57]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_654,plain,
% 23.80/3.45      ( v2_tops_1(X0,X1) = iProver_top
% 23.80/3.45      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 23.80/3.45      | l1_pre_topc(X1) != iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1797,plain,
% 23.80/3.45      ( v2_tops_1(X0,sK0) = iProver_top
% 23.80/3.45      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.80/3.45      | l1_pre_topc(sK0) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_1334,c_654]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_1802,plain,
% 23.80/3.45      ( v2_tops_1(X0,sK0) = iProver_top
% 23.80/3.45      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.80/3.45      | l1_pre_topc(sK0) != iProver_top ),
% 23.80/3.45      inference(light_normalisation,[status(thm)],[c_1797,c_1334]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_3753,plain,
% 23.80/3.45      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.80/3.45      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 23.80/3.45      | v2_tops_1(X0,sK0) = iProver_top ),
% 23.80/3.45      inference(global_propositional_subsumption,[status(thm)],[c_1802,c_20]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_3754,plain,
% 23.80/3.45      ( v2_tops_1(X0,sK0) = iProver_top
% 23.80/3.45      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 23.80/3.45      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.80/3.45      inference(renaming,[status(thm)],[c_3753]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_3765,plain,
% 23.80/3.45      ( v2_tops_1(sK1,sK0) = iProver_top
% 23.80/3.45      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
% 23.80/3.45      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_1950,c_3754]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_16,negated_conjecture,
% 23.80/3.45      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 23.80/3.45      inference(cnf_transformation,[],[f61]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_652,plain,
% 23.80/3.45      ( k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) != iProver_top ),
% 23.80/3.45      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_9723,plain,
% 23.80/3.45      ( k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) != iProver_top ),
% 23.80/3.45      inference(demodulation,[status(thm)],[c_9718,c_652]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_9724,plain,
% 23.80/3.45      ( v2_tops_1(sK1,sK0) != iProver_top ),
% 23.80/3.45      inference(equality_resolution_simp,[status(thm)],[c_9723]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_82901,plain,
% 23.80/3.45      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.80/3.45      inference(global_propositional_subsumption,
% 23.80/3.45                [status(thm)],
% 23.80/3.45                [c_82146,c_20,c_1401,c_3765,c_9724]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_82906,plain,
% 23.80/3.45      ( r1_tarski(k4_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) != iProver_top ),
% 23.80/3.45      inference(superposition,[status(thm)],[c_661,c_82901]) ).
% 23.80/3.45  
% 23.80/3.45  cnf(c_83107,plain,
% 23.80/3.45      ( $false ),
% 23.80/3.45      inference(forward_subsumption_resolution,[status(thm)],[c_82906,c_665]) ).
% 23.80/3.45  
% 23.80/3.45  
% 23.80/3.45  % SZS output end CNFRefutation for theBenchmark.p
% 23.80/3.45  
% 23.80/3.45  ------                               Statistics
% 23.80/3.45  
% 23.80/3.45  ------ Selected
% 23.80/3.45  
% 23.80/3.45  total_time:                             2.911
% 23.80/3.45  
%------------------------------------------------------------------------------
