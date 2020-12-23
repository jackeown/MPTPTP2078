%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:00 EST 2020

% Result     : Theorem 15.49s
% Output     : CNFRefutation 15.49s
% Verified   : 
% Statistics : Number of formulae       :  141 (1355 expanded)
%              Number of clauses        :   86 ( 486 expanded)
%              Number of leaves         :   17 ( 292 expanded)
%              Depth                    :   24
%              Number of atoms          :  343 (4727 expanded)
%              Number of equality atoms :  193 (1815 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

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

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_604,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_613,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1131,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_613])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_615,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1383,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1131,c_615])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_605,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_619,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1373,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_605,c_619])).

cnf(c_1676,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1383,c_1373])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_617,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2021,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1676,c_617])).

cnf(c_1677,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1383,c_605])).

cnf(c_2807,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2021,c_1677])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_614,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2215,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_614])).

cnf(c_2233,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2215,c_1383])).

cnf(c_19,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2916,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2233,c_19])).

cnf(c_2917,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2916])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_616,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2925,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2917,c_616])).

cnf(c_7544,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_2807,c_2925])).

cnf(c_16,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_606,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_608,plain,
    ( v2_tops_1(X0,X1) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1480,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1373,c_608])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2623,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1480,c_19,c_20])).

cnf(c_2627,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2623,c_1383])).

cnf(c_12,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_610,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2254,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_610])).

cnf(c_2941,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(X0,sK0) != iProver_top
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2254,c_19])).

cnf(c_2942,plain,
    ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | v1_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2941])).

cnf(c_2953,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2807,c_2942])).

cnf(c_4579,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2627,c_2953])).

cnf(c_5514,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_606,c_4579])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_612,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3274,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_612])).

cnf(c_3278,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3274,c_1383])).

cnf(c_4012,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3278,c_19])).

cnf(c_4013,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4012])).

cnf(c_4022,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1677,c_4013])).

cnf(c_4037,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_4022,c_1676])).

cnf(c_5520,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5514,c_4037])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_618,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_628,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_618,c_2])).

cnf(c_1374,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_628,c_619])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_631,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_0,c_1])).

cnf(c_1376,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1374,c_631])).

cnf(c_5523,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5520,c_1376])).

cnf(c_5748,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5523,c_4037])).

cnf(c_7559,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7544,c_5748])).

cnf(c_1238,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_628,c_616])).

cnf(c_3465,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1238,c_1376])).

cnf(c_7560,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_7559,c_3465])).

cnf(c_11,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_611,plain,
    ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
    | v1_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_48812,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7560,c_611])).

cnf(c_48835,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_48812,c_1383])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_607,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5750,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5523,c_607])).

cnf(c_5751,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5750])).

cnf(c_13,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_609,plain,
    ( v2_tops_1(X0,X1) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2005,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_609])).

cnf(c_2010,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2005,c_1383])).

cnf(c_3241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | v2_tops_1(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2010,c_19])).

cnf(c_3242,plain,
    ( v2_tops_1(X0,sK0) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3241])).

cnf(c_3251,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1676,c_3242])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48835,c_5751,c_3251,c_2021,c_1677,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.49/2.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.49/2.51  
% 15.49/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.49/2.51  
% 15.49/2.51  ------  iProver source info
% 15.49/2.51  
% 15.49/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.49/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.49/2.51  git: non_committed_changes: false
% 15.49/2.51  git: last_make_outside_of_git: false
% 15.49/2.51  
% 15.49/2.51  ------ 
% 15.49/2.51  ------ Parsing...
% 15.49/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.49/2.51  
% 15.49/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.49/2.51  
% 15.49/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.49/2.51  
% 15.49/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.49/2.51  ------ Proving...
% 15.49/2.51  ------ Problem Properties 
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  clauses                                 19
% 15.49/2.51  conjectures                             4
% 15.49/2.51  EPR                                     2
% 15.49/2.51  Horn                                    18
% 15.49/2.51  unary                                   6
% 15.49/2.51  binary                                  7
% 15.49/2.51  lits                                    42
% 15.49/2.51  lits eq                                 11
% 15.49/2.51  fd_pure                                 0
% 15.49/2.51  fd_pseudo                               0
% 15.49/2.51  fd_cond                                 0
% 15.49/2.51  fd_pseudo_cond                          0
% 15.49/2.51  AC symbols                              0
% 15.49/2.51  
% 15.49/2.51  ------ Input Options Time Limit: Unbounded
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  ------ 
% 15.49/2.51  Current options:
% 15.49/2.51  ------ 
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  ------ Proving...
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  % SZS status Theorem for theBenchmark.p
% 15.49/2.51  
% 15.49/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.49/2.51  
% 15.49/2.51  fof(f15,conjecture,(
% 15.49/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f16,negated_conjecture,(
% 15.49/2.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 15.49/2.51    inference(negated_conjecture,[],[f15])).
% 15.49/2.51  
% 15.49/2.51  fof(f27,plain,(
% 15.49/2.51    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.49/2.51    inference(ennf_transformation,[],[f16])).
% 15.49/2.51  
% 15.49/2.51  fof(f30,plain,(
% 15.49/2.51    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.49/2.51    inference(nnf_transformation,[],[f27])).
% 15.49/2.51  
% 15.49/2.51  fof(f31,plain,(
% 15.49/2.51    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.49/2.51    inference(flattening,[],[f30])).
% 15.49/2.51  
% 15.49/2.51  fof(f33,plain,(
% 15.49/2.51    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK1) | ~v2_tops_1(sK1,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK1) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.49/2.51    introduced(choice_axiom,[])).
% 15.49/2.51  
% 15.49/2.51  fof(f32,plain,(
% 15.49/2.51    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 15.49/2.51    introduced(choice_axiom,[])).
% 15.49/2.51  
% 15.49/2.51  fof(f34,plain,(
% 15.49/2.51    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 15.49/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 15.49/2.51  
% 15.49/2.51  fof(f51,plain,(
% 15.49/2.51    l1_pre_topc(sK0)),
% 15.49/2.51    inference(cnf_transformation,[],[f34])).
% 15.49/2.51  
% 15.49/2.51  fof(f11,axiom,(
% 15.49/2.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f23,plain,(
% 15.49/2.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 15.49/2.51    inference(ennf_transformation,[],[f11])).
% 15.49/2.51  
% 15.49/2.51  fof(f45,plain,(
% 15.49/2.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f23])).
% 15.49/2.51  
% 15.49/2.51  fof(f9,axiom,(
% 15.49/2.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f20,plain,(
% 15.49/2.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 15.49/2.51    inference(ennf_transformation,[],[f9])).
% 15.49/2.51  
% 15.49/2.51  fof(f43,plain,(
% 15.49/2.51    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f20])).
% 15.49/2.51  
% 15.49/2.51  fof(f52,plain,(
% 15.49/2.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.49/2.51    inference(cnf_transformation,[],[f34])).
% 15.49/2.51  
% 15.49/2.51  fof(f5,axiom,(
% 15.49/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f17,plain,(
% 15.49/2.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.49/2.51    inference(ennf_transformation,[],[f5])).
% 15.49/2.51  
% 15.49/2.51  fof(f39,plain,(
% 15.49/2.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.49/2.51    inference(cnf_transformation,[],[f17])).
% 15.49/2.51  
% 15.49/2.51  fof(f7,axiom,(
% 15.49/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f18,plain,(
% 15.49/2.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.49/2.51    inference(ennf_transformation,[],[f7])).
% 15.49/2.51  
% 15.49/2.51  fof(f41,plain,(
% 15.49/2.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.49/2.51    inference(cnf_transformation,[],[f18])).
% 15.49/2.51  
% 15.49/2.51  fof(f10,axiom,(
% 15.49/2.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f21,plain,(
% 15.49/2.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.49/2.51    inference(ennf_transformation,[],[f10])).
% 15.49/2.51  
% 15.49/2.51  fof(f22,plain,(
% 15.49/2.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.49/2.51    inference(flattening,[],[f21])).
% 15.49/2.51  
% 15.49/2.51  fof(f44,plain,(
% 15.49/2.51    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f22])).
% 15.49/2.51  
% 15.49/2.51  fof(f8,axiom,(
% 15.49/2.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f19,plain,(
% 15.49/2.51    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.49/2.51    inference(ennf_transformation,[],[f8])).
% 15.49/2.51  
% 15.49/2.51  fof(f42,plain,(
% 15.49/2.51    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.49/2.51    inference(cnf_transformation,[],[f19])).
% 15.49/2.51  
% 15.49/2.51  fof(f53,plain,(
% 15.49/2.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 15.49/2.51    inference(cnf_transformation,[],[f34])).
% 15.49/2.51  
% 15.49/2.51  fof(f14,axiom,(
% 15.49/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f26,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.49/2.51    inference(ennf_transformation,[],[f14])).
% 15.49/2.51  
% 15.49/2.51  fof(f29,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.49/2.51    inference(nnf_transformation,[],[f26])).
% 15.49/2.51  
% 15.49/2.51  fof(f49,plain,(
% 15.49/2.51    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f29])).
% 15.49/2.51  
% 15.49/2.51  fof(f13,axiom,(
% 15.49/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f25,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.49/2.51    inference(ennf_transformation,[],[f13])).
% 15.49/2.51  
% 15.49/2.51  fof(f28,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.49/2.51    inference(nnf_transformation,[],[f25])).
% 15.49/2.51  
% 15.49/2.51  fof(f47,plain,(
% 15.49/2.51    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f28])).
% 15.49/2.51  
% 15.49/2.51  fof(f12,axiom,(
% 15.49/2.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f24,plain,(
% 15.49/2.51    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.49/2.51    inference(ennf_transformation,[],[f12])).
% 15.49/2.51  
% 15.49/2.51  fof(f46,plain,(
% 15.49/2.51    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f24])).
% 15.49/2.51  
% 15.49/2.51  fof(f6,axiom,(
% 15.49/2.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f40,plain,(
% 15.49/2.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 15.49/2.51    inference(cnf_transformation,[],[f6])).
% 15.49/2.51  
% 15.49/2.51  fof(f4,axiom,(
% 15.49/2.51    ! [X0] : k2_subset_1(X0) = X0),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f38,plain,(
% 15.49/2.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 15.49/2.51    inference(cnf_transformation,[],[f4])).
% 15.49/2.51  
% 15.49/2.51  fof(f1,axiom,(
% 15.49/2.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f35,plain,(
% 15.49/2.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f1])).
% 15.49/2.51  
% 15.49/2.51  fof(f3,axiom,(
% 15.49/2.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f37,plain,(
% 15.49/2.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.49/2.51    inference(cnf_transformation,[],[f3])).
% 15.49/2.51  
% 15.49/2.51  fof(f55,plain,(
% 15.49/2.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 15.49/2.51    inference(definition_unfolding,[],[f35,f37])).
% 15.49/2.51  
% 15.49/2.51  fof(f2,axiom,(
% 15.49/2.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.49/2.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.51  
% 15.49/2.51  fof(f36,plain,(
% 15.49/2.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.49/2.51    inference(cnf_transformation,[],[f2])).
% 15.49/2.51  
% 15.49/2.51  fof(f48,plain,(
% 15.49/2.51    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f28])).
% 15.49/2.51  
% 15.49/2.51  fof(f54,plain,(
% 15.49/2.51    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 15.49/2.51    inference(cnf_transformation,[],[f34])).
% 15.49/2.51  
% 15.49/2.51  fof(f50,plain,(
% 15.49/2.51    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.49/2.51    inference(cnf_transformation,[],[f29])).
% 15.49/2.51  
% 15.49/2.51  cnf(c_18,negated_conjecture,
% 15.49/2.51      ( l1_pre_topc(sK0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f51]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_604,plain,
% 15.49/2.51      ( l1_pre_topc(sK0) = iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_9,plain,
% 15.49/2.51      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f45]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_613,plain,
% 15.49/2.51      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1131,plain,
% 15.49/2.51      ( l1_struct_0(sK0) = iProver_top ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_604,c_613]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_7,plain,
% 15.49/2.51      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f43]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_615,plain,
% 15.49/2.51      ( u1_struct_0(X0) = k2_struct_0(X0)
% 15.49/2.51      | l1_struct_0(X0) != iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1383,plain,
% 15.49/2.51      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_1131,c_615]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_17,negated_conjecture,
% 15.49/2.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.49/2.51      inference(cnf_transformation,[],[f52]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_605,plain,
% 15.49/2.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.49/2.51      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f39]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_619,plain,
% 15.49/2.51      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 15.49/2.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1373,plain,
% 15.49/2.51      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_605,c_619]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1676,plain,
% 15.49/2.51      ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 15.49/2.51      inference(demodulation,[status(thm)],[c_1383,c_1373]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.49/2.51      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 15.49/2.51      inference(cnf_transformation,[],[f41]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_617,plain,
% 15.49/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.49/2.51      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2021,plain,
% 15.49/2.51      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 15.49/2.51      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_1676,c_617]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1677,plain,
% 15.49/2.51      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 15.49/2.51      inference(demodulation,[status(thm)],[c_1383,c_605]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2807,plain,
% 15.49/2.51      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_2021,c_1677]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_8,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.49/2.51      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.49/2.51      | ~ l1_pre_topc(X1) ),
% 15.49/2.51      inference(cnf_transformation,[],[f44]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_614,plain,
% 15.49/2.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.49/2.51      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 15.49/2.51      | l1_pre_topc(X1) != iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2215,plain,
% 15.49/2.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.49/2.51      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 15.49/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_1383,c_614]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2233,plain,
% 15.49/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.49/2.51      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 15.49/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.49/2.51      inference(light_normalisation,[status(thm)],[c_2215,c_1383]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_19,plain,
% 15.49/2.51      ( l1_pre_topc(sK0) = iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2916,plain,
% 15.49/2.51      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 15.49/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_2233,c_19]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2917,plain,
% 15.49/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.49/2.51      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_2916]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_6,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.49/2.51      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 15.49/2.51      inference(cnf_transformation,[],[f42]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_616,plain,
% 15.49/2.51      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 15.49/2.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2925,plain,
% 15.49/2.51      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 15.49/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_2917,c_616]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_7544,plain,
% 15.49/2.51      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_2807,c_2925]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_16,negated_conjecture,
% 15.49/2.51      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 15.49/2.51      inference(cnf_transformation,[],[f53]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_606,plain,
% 15.49/2.51      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
% 15.49/2.51      | v2_tops_1(sK1,sK0) = iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_14,plain,
% 15.49/2.51      ( ~ v2_tops_1(X0,X1)
% 15.49/2.51      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 15.49/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.49/2.51      | ~ l1_pre_topc(X1) ),
% 15.49/2.51      inference(cnf_transformation,[],[f49]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_608,plain,
% 15.49/2.51      ( v2_tops_1(X0,X1) != iProver_top
% 15.49/2.51      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 15.49/2.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.49/2.51      | l1_pre_topc(X1) != iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1480,plain,
% 15.49/2.51      ( v2_tops_1(sK1,sK0) != iProver_top
% 15.49/2.51      | v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top
% 15.49/2.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.49/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_1373,c_608]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_20,plain,
% 15.49/2.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2623,plain,
% 15.49/2.51      ( v2_tops_1(sK1,sK0) != iProver_top
% 15.49/2.51      | v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) = iProver_top ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_1480,c_19,c_20]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2627,plain,
% 15.49/2.51      ( v2_tops_1(sK1,sK0) != iProver_top
% 15.49/2.51      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top ),
% 15.49/2.51      inference(light_normalisation,[status(thm)],[c_2623,c_1383]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_12,plain,
% 15.49/2.51      ( ~ v1_tops_1(X0,X1)
% 15.49/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.49/2.51      | ~ l1_pre_topc(X1)
% 15.49/2.51      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 15.49/2.51      inference(cnf_transformation,[],[f47]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_610,plain,
% 15.49/2.51      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 15.49/2.51      | v1_tops_1(X1,X0) != iProver_top
% 15.49/2.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.49/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2254,plain,
% 15.49/2.51      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 15.49/2.51      | v1_tops_1(X0,sK0) != iProver_top
% 15.49/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.49/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_1383,c_610]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2941,plain,
% 15.49/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.49/2.51      | v1_tops_1(X0,sK0) != iProver_top
% 15.49/2.51      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_2254,c_19]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2942,plain,
% 15.49/2.51      ( k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 15.49/2.51      | v1_tops_1(X0,sK0) != iProver_top
% 15.49/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_2941]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2953,plain,
% 15.49/2.51      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 15.49/2.51      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_2807,c_2942]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_4579,plain,
% 15.49/2.51      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 15.49/2.51      | v2_tops_1(sK1,sK0) != iProver_top ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_2627,c_2953]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5514,plain,
% 15.49/2.51      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 15.49/2.51      | k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_606,c_4579]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_10,plain,
% 15.49/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.49/2.51      | ~ l1_pre_topc(X1)
% 15.49/2.51      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 15.49/2.51      inference(cnf_transformation,[],[f46]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_612,plain,
% 15.49/2.51      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 15.49/2.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.49/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3274,plain,
% 15.49/2.51      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 15.49/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.49/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_1383,c_612]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3278,plain,
% 15.49/2.51      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 15.49/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.49/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.49/2.51      inference(light_normalisation,[status(thm)],[c_3274,c_1383]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_4012,plain,
% 15.49/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.49/2.51      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_3278,c_19]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_4013,plain,
% 15.49/2.51      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 15.49/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_4012]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_4022,plain,
% 15.49/2.51      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_1677,c_4013]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_4037,plain,
% 15.49/2.51      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 15.49/2.51      inference(light_normalisation,[status(thm)],[c_4022,c_1676]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5520,plain,
% 15.49/2.51      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 15.49/2.51      | k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_5514,c_4037]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_4,plain,
% 15.49/2.51      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 15.49/2.51      inference(cnf_transformation,[],[f40]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_618,plain,
% 15.49/2.51      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2,plain,
% 15.49/2.51      ( k2_subset_1(X0) = X0 ),
% 15.49/2.51      inference(cnf_transformation,[],[f38]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_628,plain,
% 15.49/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.49/2.51      inference(light_normalisation,[status(thm)],[c_618,c_2]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1374,plain,
% 15.49/2.51      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_628,c_619]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_0,plain,
% 15.49/2.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 15.49/2.51      inference(cnf_transformation,[],[f55]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1,plain,
% 15.49/2.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.49/2.51      inference(cnf_transformation,[],[f36]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_631,plain,
% 15.49/2.51      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.49/2.51      inference(light_normalisation,[status(thm)],[c_0,c_1]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1376,plain,
% 15.49/2.51      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 15.49/2.51      inference(light_normalisation,[status(thm)],[c_1374,c_631]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5523,plain,
% 15.49/2.51      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 15.49/2.51      inference(demodulation,[status(thm)],[c_5520,c_1376]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5748,plain,
% 15.49/2.51      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 15.49/2.51      inference(demodulation,[status(thm)],[c_5523,c_4037]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_7559,plain,
% 15.49/2.51      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) ),
% 15.49/2.51      inference(light_normalisation,[status(thm)],[c_7544,c_5748]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_1238,plain,
% 15.49/2.51      ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_628,c_616]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3465,plain,
% 15.49/2.51      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 15.49/2.51      inference(light_normalisation,[status(thm)],[c_1238,c_1376]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_7560,plain,
% 15.49/2.51      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 15.49/2.51      inference(demodulation,[status(thm)],[c_7559,c_3465]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_11,plain,
% 15.49/2.51      ( v1_tops_1(X0,X1)
% 15.49/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.49/2.51      | ~ l1_pre_topc(X1)
% 15.49/2.51      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 15.49/2.51      inference(cnf_transformation,[],[f48]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_611,plain,
% 15.49/2.51      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
% 15.49/2.51      | v1_tops_1(X1,X0) = iProver_top
% 15.49/2.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.49/2.51      | l1_pre_topc(X0) != iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_48812,plain,
% 15.49/2.51      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 15.49/2.51      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.49/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_7560,c_611]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_48835,plain,
% 15.49/2.51      ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) = iProver_top
% 15.49/2.51      | m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.49/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.49/2.51      inference(light_normalisation,[status(thm)],[c_48812,c_1383]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_15,negated_conjecture,
% 15.49/2.51      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 15.49/2.51      inference(cnf_transformation,[],[f54]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_607,plain,
% 15.49/2.51      ( k1_xboole_0 != k1_tops_1(sK0,sK1)
% 15.49/2.51      | v2_tops_1(sK1,sK0) != iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5750,plain,
% 15.49/2.51      ( k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) != iProver_top ),
% 15.49/2.51      inference(demodulation,[status(thm)],[c_5523,c_607]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_5751,plain,
% 15.49/2.51      ( v2_tops_1(sK1,sK0) != iProver_top ),
% 15.49/2.51      inference(equality_resolution_simp,[status(thm)],[c_5750]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_13,plain,
% 15.49/2.51      ( v2_tops_1(X0,X1)
% 15.49/2.51      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 15.49/2.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.49/2.51      | ~ l1_pre_topc(X1) ),
% 15.49/2.51      inference(cnf_transformation,[],[f50]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_609,plain,
% 15.49/2.51      ( v2_tops_1(X0,X1) = iProver_top
% 15.49/2.51      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 15.49/2.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.49/2.51      | l1_pre_topc(X1) != iProver_top ),
% 15.49/2.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2005,plain,
% 15.49/2.51      ( v2_tops_1(X0,sK0) = iProver_top
% 15.49/2.51      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 15.49/2.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.49/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_1383,c_609]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_2010,plain,
% 15.49/2.51      ( v2_tops_1(X0,sK0) = iProver_top
% 15.49/2.51      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 15.49/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.49/2.51      | l1_pre_topc(sK0) != iProver_top ),
% 15.49/2.51      inference(light_normalisation,[status(thm)],[c_2005,c_1383]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3241,plain,
% 15.49/2.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.49/2.51      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 15.49/2.51      | v2_tops_1(X0,sK0) = iProver_top ),
% 15.49/2.51      inference(global_propositional_subsumption,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_2010,c_19]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3242,plain,
% 15.49/2.51      ( v2_tops_1(X0,sK0) = iProver_top
% 15.49/2.51      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) != iProver_top
% 15.49/2.51      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 15.49/2.51      inference(renaming,[status(thm)],[c_3241]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(c_3251,plain,
% 15.49/2.51      ( v2_tops_1(sK1,sK0) = iProver_top
% 15.49/2.51      | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) != iProver_top
% 15.49/2.51      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 15.49/2.51      inference(superposition,[status(thm)],[c_1676,c_3242]) ).
% 15.49/2.51  
% 15.49/2.51  cnf(contradiction,plain,
% 15.49/2.51      ( $false ),
% 15.49/2.51      inference(minisat,
% 15.49/2.51                [status(thm)],
% 15.49/2.51                [c_48835,c_5751,c_3251,c_2021,c_1677,c_19]) ).
% 15.49/2.51  
% 15.49/2.51  
% 15.49/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.49/2.51  
% 15.49/2.51  ------                               Statistics
% 15.49/2.51  
% 15.49/2.51  ------ Selected
% 15.49/2.51  
% 15.49/2.51  total_time:                             1.697
% 15.49/2.51  
%------------------------------------------------------------------------------
