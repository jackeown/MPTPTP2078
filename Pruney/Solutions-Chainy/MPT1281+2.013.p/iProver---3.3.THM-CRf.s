%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:41 EST 2020

% Result     : Theorem 23.62s
% Output     : CNFRefutation 23.62s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 314 expanded)
%              Number of clauses        :   56 (  94 expanded)
%              Number of leaves         :   13 (  78 expanded)
%              Depth                    :   17
%              Number of atoms          :  233 (1075 expanded)
%              Number of equality atoms :   79 ( 110 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1)))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
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

fof(f29,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28,f27])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_513,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_210,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_509,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_197,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_198,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_510,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_198])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_515,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2250,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k2_xboole_0(X0,k2_tops_1(sK0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_510,c_515])).

cnf(c_8142,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k2_tops_1(sK0,X1)) = k2_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_509,c_2250])).

cnf(c_81726,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0)) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_513,c_8142])).

cnf(c_81759,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_509,c_81726])).

cnf(c_88230,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_513,c_81759])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_185,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_511,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_718,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_509,c_511])).

cnf(c_3173,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_513,c_718])).

cnf(c_6,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_164,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_165,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_164])).

cnf(c_167,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_165,c_14,c_13])).

cnf(c_3185,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3173,c_167])).

cnf(c_88242,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_88230,c_3185])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_173,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_174,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_173])).

cnf(c_512,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k2_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_868,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_167,c_512])).

cnf(c_16,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_585,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_586,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_1374,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_868,c_16,c_586])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_517,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1379,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1374,c_517])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_516,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_967,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_516])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_518,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1355,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_518])).

cnf(c_3641,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_xboole_0(X0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1379,c_1355])).

cnf(c_88379,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_88242,c_3641])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_514,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_527,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_514,c_167])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_88379,c_527])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:18:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.62/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.62/3.49  
% 23.62/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.62/3.49  
% 23.62/3.49  ------  iProver source info
% 23.62/3.49  
% 23.62/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.62/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.62/3.49  git: non_committed_changes: false
% 23.62/3.49  git: last_make_outside_of_git: false
% 23.62/3.49  
% 23.62/3.49  ------ 
% 23.62/3.49  
% 23.62/3.49  ------ Input Options
% 23.62/3.49  
% 23.62/3.49  --out_options                           all
% 23.62/3.49  --tptp_safe_out                         true
% 23.62/3.49  --problem_path                          ""
% 23.62/3.49  --include_path                          ""
% 23.62/3.49  --clausifier                            res/vclausify_rel
% 23.62/3.49  --clausifier_options                    --mode clausify
% 23.62/3.49  --stdin                                 false
% 23.62/3.49  --stats_out                             all
% 23.62/3.49  
% 23.62/3.49  ------ General Options
% 23.62/3.49  
% 23.62/3.49  --fof                                   false
% 23.62/3.49  --time_out_real                         305.
% 23.62/3.49  --time_out_virtual                      -1.
% 23.62/3.49  --symbol_type_check                     false
% 23.62/3.49  --clausify_out                          false
% 23.62/3.49  --sig_cnt_out                           false
% 23.62/3.49  --trig_cnt_out                          false
% 23.62/3.49  --trig_cnt_out_tolerance                1.
% 23.62/3.49  --trig_cnt_out_sk_spl                   false
% 23.62/3.49  --abstr_cl_out                          false
% 23.62/3.49  
% 23.62/3.49  ------ Global Options
% 23.62/3.49  
% 23.62/3.49  --schedule                              default
% 23.62/3.49  --add_important_lit                     false
% 23.62/3.49  --prop_solver_per_cl                    1000
% 23.62/3.49  --min_unsat_core                        false
% 23.62/3.49  --soft_assumptions                      false
% 23.62/3.49  --soft_lemma_size                       3
% 23.62/3.49  --prop_impl_unit_size                   0
% 23.62/3.49  --prop_impl_unit                        []
% 23.62/3.49  --share_sel_clauses                     true
% 23.62/3.49  --reset_solvers                         false
% 23.62/3.49  --bc_imp_inh                            [conj_cone]
% 23.62/3.49  --conj_cone_tolerance                   3.
% 23.62/3.49  --extra_neg_conj                        none
% 23.62/3.49  --large_theory_mode                     true
% 23.62/3.49  --prolific_symb_bound                   200
% 23.62/3.49  --lt_threshold                          2000
% 23.62/3.49  --clause_weak_htbl                      true
% 23.62/3.49  --gc_record_bc_elim                     false
% 23.62/3.49  
% 23.62/3.49  ------ Preprocessing Options
% 23.62/3.49  
% 23.62/3.49  --preprocessing_flag                    true
% 23.62/3.49  --time_out_prep_mult                    0.1
% 23.62/3.49  --splitting_mode                        input
% 23.62/3.49  --splitting_grd                         true
% 23.62/3.49  --splitting_cvd                         false
% 23.62/3.49  --splitting_cvd_svl                     false
% 23.62/3.49  --splitting_nvd                         32
% 23.62/3.49  --sub_typing                            true
% 23.62/3.49  --prep_gs_sim                           true
% 23.62/3.49  --prep_unflatten                        true
% 23.62/3.49  --prep_res_sim                          true
% 23.62/3.49  --prep_upred                            true
% 23.62/3.49  --prep_sem_filter                       exhaustive
% 23.62/3.49  --prep_sem_filter_out                   false
% 23.62/3.49  --pred_elim                             true
% 23.62/3.49  --res_sim_input                         true
% 23.62/3.49  --eq_ax_congr_red                       true
% 23.62/3.49  --pure_diseq_elim                       true
% 23.62/3.49  --brand_transform                       false
% 23.62/3.49  --non_eq_to_eq                          false
% 23.62/3.49  --prep_def_merge                        true
% 23.62/3.49  --prep_def_merge_prop_impl              false
% 23.62/3.49  --prep_def_merge_mbd                    true
% 23.62/3.49  --prep_def_merge_tr_red                 false
% 23.62/3.49  --prep_def_merge_tr_cl                  false
% 23.62/3.49  --smt_preprocessing                     true
% 23.62/3.49  --smt_ac_axioms                         fast
% 23.62/3.49  --preprocessed_out                      false
% 23.62/3.49  --preprocessed_stats                    false
% 23.62/3.49  
% 23.62/3.49  ------ Abstraction refinement Options
% 23.62/3.49  
% 23.62/3.49  --abstr_ref                             []
% 23.62/3.49  --abstr_ref_prep                        false
% 23.62/3.49  --abstr_ref_until_sat                   false
% 23.62/3.49  --abstr_ref_sig_restrict                funpre
% 23.62/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.62/3.49  --abstr_ref_under                       []
% 23.62/3.49  
% 23.62/3.49  ------ SAT Options
% 23.62/3.49  
% 23.62/3.49  --sat_mode                              false
% 23.62/3.49  --sat_fm_restart_options                ""
% 23.62/3.49  --sat_gr_def                            false
% 23.62/3.49  --sat_epr_types                         true
% 23.62/3.49  --sat_non_cyclic_types                  false
% 23.62/3.49  --sat_finite_models                     false
% 23.62/3.49  --sat_fm_lemmas                         false
% 23.62/3.49  --sat_fm_prep                           false
% 23.62/3.49  --sat_fm_uc_incr                        true
% 23.62/3.49  --sat_out_model                         small
% 23.62/3.49  --sat_out_clauses                       false
% 23.62/3.49  
% 23.62/3.49  ------ QBF Options
% 23.62/3.49  
% 23.62/3.49  --qbf_mode                              false
% 23.62/3.49  --qbf_elim_univ                         false
% 23.62/3.49  --qbf_dom_inst                          none
% 23.62/3.49  --qbf_dom_pre_inst                      false
% 23.62/3.49  --qbf_sk_in                             false
% 23.62/3.49  --qbf_pred_elim                         true
% 23.62/3.49  --qbf_split                             512
% 23.62/3.49  
% 23.62/3.49  ------ BMC1 Options
% 23.62/3.49  
% 23.62/3.49  --bmc1_incremental                      false
% 23.62/3.49  --bmc1_axioms                           reachable_all
% 23.62/3.49  --bmc1_min_bound                        0
% 23.62/3.49  --bmc1_max_bound                        -1
% 23.62/3.49  --bmc1_max_bound_default                -1
% 23.62/3.49  --bmc1_symbol_reachability              true
% 23.62/3.49  --bmc1_property_lemmas                  false
% 23.62/3.49  --bmc1_k_induction                      false
% 23.62/3.49  --bmc1_non_equiv_states                 false
% 23.62/3.49  --bmc1_deadlock                         false
% 23.62/3.49  --bmc1_ucm                              false
% 23.62/3.49  --bmc1_add_unsat_core                   none
% 23.62/3.49  --bmc1_unsat_core_children              false
% 23.62/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.62/3.49  --bmc1_out_stat                         full
% 23.62/3.49  --bmc1_ground_init                      false
% 23.62/3.49  --bmc1_pre_inst_next_state              false
% 23.62/3.49  --bmc1_pre_inst_state                   false
% 23.62/3.49  --bmc1_pre_inst_reach_state             false
% 23.62/3.49  --bmc1_out_unsat_core                   false
% 23.62/3.49  --bmc1_aig_witness_out                  false
% 23.62/3.49  --bmc1_verbose                          false
% 23.62/3.49  --bmc1_dump_clauses_tptp                false
% 23.62/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.62/3.49  --bmc1_dump_file                        -
% 23.62/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.62/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.62/3.49  --bmc1_ucm_extend_mode                  1
% 23.62/3.49  --bmc1_ucm_init_mode                    2
% 23.62/3.49  --bmc1_ucm_cone_mode                    none
% 23.62/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.62/3.49  --bmc1_ucm_relax_model                  4
% 23.62/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.62/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.62/3.49  --bmc1_ucm_layered_model                none
% 23.62/3.49  --bmc1_ucm_max_lemma_size               10
% 23.62/3.49  
% 23.62/3.49  ------ AIG Options
% 23.62/3.49  
% 23.62/3.49  --aig_mode                              false
% 23.62/3.49  
% 23.62/3.49  ------ Instantiation Options
% 23.62/3.49  
% 23.62/3.49  --instantiation_flag                    true
% 23.62/3.49  --inst_sos_flag                         false
% 23.62/3.49  --inst_sos_phase                        true
% 23.62/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.62/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.62/3.49  --inst_lit_sel_side                     num_symb
% 23.62/3.49  --inst_solver_per_active                1400
% 23.62/3.49  --inst_solver_calls_frac                1.
% 23.62/3.49  --inst_passive_queue_type               priority_queues
% 23.62/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.62/3.49  --inst_passive_queues_freq              [25;2]
% 23.62/3.49  --inst_dismatching                      true
% 23.62/3.49  --inst_eager_unprocessed_to_passive     true
% 23.62/3.49  --inst_prop_sim_given                   true
% 23.62/3.49  --inst_prop_sim_new                     false
% 23.62/3.49  --inst_subs_new                         false
% 23.62/3.49  --inst_eq_res_simp                      false
% 23.62/3.49  --inst_subs_given                       false
% 23.62/3.49  --inst_orphan_elimination               true
% 23.62/3.49  --inst_learning_loop_flag               true
% 23.62/3.49  --inst_learning_start                   3000
% 23.62/3.49  --inst_learning_factor                  2
% 23.62/3.49  --inst_start_prop_sim_after_learn       3
% 23.62/3.49  --inst_sel_renew                        solver
% 23.62/3.49  --inst_lit_activity_flag                true
% 23.62/3.49  --inst_restr_to_given                   false
% 23.62/3.49  --inst_activity_threshold               500
% 23.62/3.49  --inst_out_proof                        true
% 23.62/3.49  
% 23.62/3.49  ------ Resolution Options
% 23.62/3.49  
% 23.62/3.49  --resolution_flag                       true
% 23.62/3.49  --res_lit_sel                           adaptive
% 23.62/3.49  --res_lit_sel_side                      none
% 23.62/3.49  --res_ordering                          kbo
% 23.62/3.49  --res_to_prop_solver                    active
% 23.62/3.49  --res_prop_simpl_new                    false
% 23.62/3.49  --res_prop_simpl_given                  true
% 23.62/3.49  --res_passive_queue_type                priority_queues
% 23.62/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.62/3.50  --res_passive_queues_freq               [15;5]
% 23.62/3.50  --res_forward_subs                      full
% 23.62/3.50  --res_backward_subs                     full
% 23.62/3.50  --res_forward_subs_resolution           true
% 23.62/3.50  --res_backward_subs_resolution          true
% 23.62/3.50  --res_orphan_elimination                true
% 23.62/3.50  --res_time_limit                        2.
% 23.62/3.50  --res_out_proof                         true
% 23.62/3.50  
% 23.62/3.50  ------ Superposition Options
% 23.62/3.50  
% 23.62/3.50  --superposition_flag                    true
% 23.62/3.50  --sup_passive_queue_type                priority_queues
% 23.62/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.62/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.62/3.50  --demod_completeness_check              fast
% 23.62/3.50  --demod_use_ground                      true
% 23.62/3.50  --sup_to_prop_solver                    passive
% 23.62/3.50  --sup_prop_simpl_new                    true
% 23.62/3.50  --sup_prop_simpl_given                  true
% 23.62/3.50  --sup_fun_splitting                     false
% 23.62/3.50  --sup_smt_interval                      50000
% 23.62/3.50  
% 23.62/3.50  ------ Superposition Simplification Setup
% 23.62/3.50  
% 23.62/3.50  --sup_indices_passive                   []
% 23.62/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.62/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.62/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.62/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.62/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.62/3.50  --sup_full_bw                           [BwDemod]
% 23.62/3.50  --sup_immed_triv                        [TrivRules]
% 23.62/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.62/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.62/3.50  --sup_immed_bw_main                     []
% 23.62/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.62/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.62/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.62/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.62/3.50  
% 23.62/3.50  ------ Combination Options
% 23.62/3.50  
% 23.62/3.50  --comb_res_mult                         3
% 23.62/3.50  --comb_sup_mult                         2
% 23.62/3.50  --comb_inst_mult                        10
% 23.62/3.50  
% 23.62/3.50  ------ Debug Options
% 23.62/3.50  
% 23.62/3.50  --dbg_backtrace                         false
% 23.62/3.50  --dbg_dump_prop_clauses                 false
% 23.62/3.50  --dbg_dump_prop_clauses_file            -
% 23.62/3.50  --dbg_out_stat                          false
% 23.62/3.50  ------ Parsing...
% 23.62/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.62/3.50  
% 23.62/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 23.62/3.50  
% 23.62/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.62/3.50  
% 23.62/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.62/3.50  ------ Proving...
% 23.62/3.50  ------ Problem Properties 
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  clauses                                 12
% 23.62/3.50  conjectures                             2
% 23.62/3.50  EPR                                     0
% 23.62/3.50  Horn                                    12
% 23.62/3.50  unary                                   5
% 23.62/3.50  binary                                  6
% 23.62/3.50  lits                                    20
% 23.62/3.50  lits eq                                 5
% 23.62/3.50  fd_pure                                 0
% 23.62/3.50  fd_pseudo                               0
% 23.62/3.50  fd_cond                                 0
% 23.62/3.50  fd_pseudo_cond                          0
% 23.62/3.50  AC symbols                              0
% 23.62/3.50  
% 23.62/3.50  ------ Schedule dynamic 5 is on 
% 23.62/3.50  
% 23.62/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  ------ 
% 23.62/3.50  Current options:
% 23.62/3.50  ------ 
% 23.62/3.50  
% 23.62/3.50  ------ Input Options
% 23.62/3.50  
% 23.62/3.50  --out_options                           all
% 23.62/3.50  --tptp_safe_out                         true
% 23.62/3.50  --problem_path                          ""
% 23.62/3.50  --include_path                          ""
% 23.62/3.50  --clausifier                            res/vclausify_rel
% 23.62/3.50  --clausifier_options                    --mode clausify
% 23.62/3.50  --stdin                                 false
% 23.62/3.50  --stats_out                             all
% 23.62/3.50  
% 23.62/3.50  ------ General Options
% 23.62/3.50  
% 23.62/3.50  --fof                                   false
% 23.62/3.50  --time_out_real                         305.
% 23.62/3.50  --time_out_virtual                      -1.
% 23.62/3.50  --symbol_type_check                     false
% 23.62/3.50  --clausify_out                          false
% 23.62/3.50  --sig_cnt_out                           false
% 23.62/3.50  --trig_cnt_out                          false
% 23.62/3.50  --trig_cnt_out_tolerance                1.
% 23.62/3.50  --trig_cnt_out_sk_spl                   false
% 23.62/3.50  --abstr_cl_out                          false
% 23.62/3.50  
% 23.62/3.50  ------ Global Options
% 23.62/3.50  
% 23.62/3.50  --schedule                              default
% 23.62/3.50  --add_important_lit                     false
% 23.62/3.50  --prop_solver_per_cl                    1000
% 23.62/3.50  --min_unsat_core                        false
% 23.62/3.50  --soft_assumptions                      false
% 23.62/3.50  --soft_lemma_size                       3
% 23.62/3.50  --prop_impl_unit_size                   0
% 23.62/3.50  --prop_impl_unit                        []
% 23.62/3.50  --share_sel_clauses                     true
% 23.62/3.50  --reset_solvers                         false
% 23.62/3.50  --bc_imp_inh                            [conj_cone]
% 23.62/3.50  --conj_cone_tolerance                   3.
% 23.62/3.50  --extra_neg_conj                        none
% 23.62/3.50  --large_theory_mode                     true
% 23.62/3.50  --prolific_symb_bound                   200
% 23.62/3.50  --lt_threshold                          2000
% 23.62/3.50  --clause_weak_htbl                      true
% 23.62/3.50  --gc_record_bc_elim                     false
% 23.62/3.50  
% 23.62/3.50  ------ Preprocessing Options
% 23.62/3.50  
% 23.62/3.50  --preprocessing_flag                    true
% 23.62/3.50  --time_out_prep_mult                    0.1
% 23.62/3.50  --splitting_mode                        input
% 23.62/3.50  --splitting_grd                         true
% 23.62/3.50  --splitting_cvd                         false
% 23.62/3.50  --splitting_cvd_svl                     false
% 23.62/3.50  --splitting_nvd                         32
% 23.62/3.50  --sub_typing                            true
% 23.62/3.50  --prep_gs_sim                           true
% 23.62/3.50  --prep_unflatten                        true
% 23.62/3.50  --prep_res_sim                          true
% 23.62/3.50  --prep_upred                            true
% 23.62/3.50  --prep_sem_filter                       exhaustive
% 23.62/3.50  --prep_sem_filter_out                   false
% 23.62/3.50  --pred_elim                             true
% 23.62/3.50  --res_sim_input                         true
% 23.62/3.50  --eq_ax_congr_red                       true
% 23.62/3.50  --pure_diseq_elim                       true
% 23.62/3.50  --brand_transform                       false
% 23.62/3.50  --non_eq_to_eq                          false
% 23.62/3.50  --prep_def_merge                        true
% 23.62/3.50  --prep_def_merge_prop_impl              false
% 23.62/3.50  --prep_def_merge_mbd                    true
% 23.62/3.50  --prep_def_merge_tr_red                 false
% 23.62/3.50  --prep_def_merge_tr_cl                  false
% 23.62/3.50  --smt_preprocessing                     true
% 23.62/3.50  --smt_ac_axioms                         fast
% 23.62/3.50  --preprocessed_out                      false
% 23.62/3.50  --preprocessed_stats                    false
% 23.62/3.50  
% 23.62/3.50  ------ Abstraction refinement Options
% 23.62/3.50  
% 23.62/3.50  --abstr_ref                             []
% 23.62/3.50  --abstr_ref_prep                        false
% 23.62/3.50  --abstr_ref_until_sat                   false
% 23.62/3.50  --abstr_ref_sig_restrict                funpre
% 23.62/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.62/3.50  --abstr_ref_under                       []
% 23.62/3.50  
% 23.62/3.50  ------ SAT Options
% 23.62/3.50  
% 23.62/3.50  --sat_mode                              false
% 23.62/3.50  --sat_fm_restart_options                ""
% 23.62/3.50  --sat_gr_def                            false
% 23.62/3.50  --sat_epr_types                         true
% 23.62/3.50  --sat_non_cyclic_types                  false
% 23.62/3.50  --sat_finite_models                     false
% 23.62/3.50  --sat_fm_lemmas                         false
% 23.62/3.50  --sat_fm_prep                           false
% 23.62/3.50  --sat_fm_uc_incr                        true
% 23.62/3.50  --sat_out_model                         small
% 23.62/3.50  --sat_out_clauses                       false
% 23.62/3.50  
% 23.62/3.50  ------ QBF Options
% 23.62/3.50  
% 23.62/3.50  --qbf_mode                              false
% 23.62/3.50  --qbf_elim_univ                         false
% 23.62/3.50  --qbf_dom_inst                          none
% 23.62/3.50  --qbf_dom_pre_inst                      false
% 23.62/3.50  --qbf_sk_in                             false
% 23.62/3.50  --qbf_pred_elim                         true
% 23.62/3.50  --qbf_split                             512
% 23.62/3.50  
% 23.62/3.50  ------ BMC1 Options
% 23.62/3.50  
% 23.62/3.50  --bmc1_incremental                      false
% 23.62/3.50  --bmc1_axioms                           reachable_all
% 23.62/3.50  --bmc1_min_bound                        0
% 23.62/3.50  --bmc1_max_bound                        -1
% 23.62/3.50  --bmc1_max_bound_default                -1
% 23.62/3.50  --bmc1_symbol_reachability              true
% 23.62/3.50  --bmc1_property_lemmas                  false
% 23.62/3.50  --bmc1_k_induction                      false
% 23.62/3.50  --bmc1_non_equiv_states                 false
% 23.62/3.50  --bmc1_deadlock                         false
% 23.62/3.50  --bmc1_ucm                              false
% 23.62/3.50  --bmc1_add_unsat_core                   none
% 23.62/3.50  --bmc1_unsat_core_children              false
% 23.62/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.62/3.50  --bmc1_out_stat                         full
% 23.62/3.50  --bmc1_ground_init                      false
% 23.62/3.50  --bmc1_pre_inst_next_state              false
% 23.62/3.50  --bmc1_pre_inst_state                   false
% 23.62/3.50  --bmc1_pre_inst_reach_state             false
% 23.62/3.50  --bmc1_out_unsat_core                   false
% 23.62/3.50  --bmc1_aig_witness_out                  false
% 23.62/3.50  --bmc1_verbose                          false
% 23.62/3.50  --bmc1_dump_clauses_tptp                false
% 23.62/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.62/3.50  --bmc1_dump_file                        -
% 23.62/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.62/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.62/3.50  --bmc1_ucm_extend_mode                  1
% 23.62/3.50  --bmc1_ucm_init_mode                    2
% 23.62/3.50  --bmc1_ucm_cone_mode                    none
% 23.62/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.62/3.50  --bmc1_ucm_relax_model                  4
% 23.62/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.62/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.62/3.50  --bmc1_ucm_layered_model                none
% 23.62/3.50  --bmc1_ucm_max_lemma_size               10
% 23.62/3.50  
% 23.62/3.50  ------ AIG Options
% 23.62/3.50  
% 23.62/3.50  --aig_mode                              false
% 23.62/3.50  
% 23.62/3.50  ------ Instantiation Options
% 23.62/3.50  
% 23.62/3.50  --instantiation_flag                    true
% 23.62/3.50  --inst_sos_flag                         false
% 23.62/3.50  --inst_sos_phase                        true
% 23.62/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.62/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.62/3.50  --inst_lit_sel_side                     none
% 23.62/3.50  --inst_solver_per_active                1400
% 23.62/3.50  --inst_solver_calls_frac                1.
% 23.62/3.50  --inst_passive_queue_type               priority_queues
% 23.62/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.62/3.50  --inst_passive_queues_freq              [25;2]
% 23.62/3.50  --inst_dismatching                      true
% 23.62/3.50  --inst_eager_unprocessed_to_passive     true
% 23.62/3.50  --inst_prop_sim_given                   true
% 23.62/3.50  --inst_prop_sim_new                     false
% 23.62/3.50  --inst_subs_new                         false
% 23.62/3.50  --inst_eq_res_simp                      false
% 23.62/3.50  --inst_subs_given                       false
% 23.62/3.50  --inst_orphan_elimination               true
% 23.62/3.50  --inst_learning_loop_flag               true
% 23.62/3.50  --inst_learning_start                   3000
% 23.62/3.50  --inst_learning_factor                  2
% 23.62/3.50  --inst_start_prop_sim_after_learn       3
% 23.62/3.50  --inst_sel_renew                        solver
% 23.62/3.50  --inst_lit_activity_flag                true
% 23.62/3.50  --inst_restr_to_given                   false
% 23.62/3.50  --inst_activity_threshold               500
% 23.62/3.50  --inst_out_proof                        true
% 23.62/3.50  
% 23.62/3.50  ------ Resolution Options
% 23.62/3.50  
% 23.62/3.50  --resolution_flag                       false
% 23.62/3.50  --res_lit_sel                           adaptive
% 23.62/3.50  --res_lit_sel_side                      none
% 23.62/3.50  --res_ordering                          kbo
% 23.62/3.50  --res_to_prop_solver                    active
% 23.62/3.50  --res_prop_simpl_new                    false
% 23.62/3.50  --res_prop_simpl_given                  true
% 23.62/3.50  --res_passive_queue_type                priority_queues
% 23.62/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.62/3.50  --res_passive_queues_freq               [15;5]
% 23.62/3.50  --res_forward_subs                      full
% 23.62/3.50  --res_backward_subs                     full
% 23.62/3.50  --res_forward_subs_resolution           true
% 23.62/3.50  --res_backward_subs_resolution          true
% 23.62/3.50  --res_orphan_elimination                true
% 23.62/3.50  --res_time_limit                        2.
% 23.62/3.50  --res_out_proof                         true
% 23.62/3.50  
% 23.62/3.50  ------ Superposition Options
% 23.62/3.50  
% 23.62/3.50  --superposition_flag                    true
% 23.62/3.50  --sup_passive_queue_type                priority_queues
% 23.62/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.62/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.62/3.50  --demod_completeness_check              fast
% 23.62/3.50  --demod_use_ground                      true
% 23.62/3.50  --sup_to_prop_solver                    passive
% 23.62/3.50  --sup_prop_simpl_new                    true
% 23.62/3.50  --sup_prop_simpl_given                  true
% 23.62/3.50  --sup_fun_splitting                     false
% 23.62/3.50  --sup_smt_interval                      50000
% 23.62/3.50  
% 23.62/3.50  ------ Superposition Simplification Setup
% 23.62/3.50  
% 23.62/3.50  --sup_indices_passive                   []
% 23.62/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.62/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.62/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.62/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.62/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.62/3.50  --sup_full_bw                           [BwDemod]
% 23.62/3.50  --sup_immed_triv                        [TrivRules]
% 23.62/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.62/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.62/3.50  --sup_immed_bw_main                     []
% 23.62/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.62/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.62/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.62/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.62/3.50  
% 23.62/3.50  ------ Combination Options
% 23.62/3.50  
% 23.62/3.50  --comb_res_mult                         3
% 23.62/3.50  --comb_sup_mult                         2
% 23.62/3.50  --comb_inst_mult                        10
% 23.62/3.50  
% 23.62/3.50  ------ Debug Options
% 23.62/3.50  
% 23.62/3.50  --dbg_backtrace                         false
% 23.62/3.50  --dbg_dump_prop_clauses                 false
% 23.62/3.50  --dbg_dump_prop_clauses_file            -
% 23.62/3.50  --dbg_out_stat                          false
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  ------ Proving...
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  % SZS status Theorem for theBenchmark.p
% 23.62/3.50  
% 23.62/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.62/3.50  
% 23.62/3.50  fof(f11,conjecture,(
% 23.62/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 23.62/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f12,negated_conjecture,(
% 23.62/3.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 23.62/3.50    inference(negated_conjecture,[],[f11])).
% 23.62/3.50  
% 23.62/3.50  fof(f24,plain,(
% 23.62/3.50    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 23.62/3.50    inference(ennf_transformation,[],[f12])).
% 23.62/3.50  
% 23.62/3.50  fof(f25,plain,(
% 23.62/3.50    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 23.62/3.50    inference(flattening,[],[f24])).
% 23.62/3.50  
% 23.62/3.50  fof(f28,plain,(
% 23.62/3.50    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1))) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 23.62/3.50    introduced(choice_axiom,[])).
% 23.62/3.50  
% 23.62/3.50  fof(f27,plain,(
% 23.62/3.50    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 23.62/3.50    introduced(choice_axiom,[])).
% 23.62/3.50  
% 23.62/3.50  fof(f29,plain,(
% 23.62/3.50    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 23.62/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28,f27])).
% 23.62/3.50  
% 23.62/3.50  fof(f42,plain,(
% 23.62/3.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 23.62/3.50    inference(cnf_transformation,[],[f29])).
% 23.62/3.50  
% 23.62/3.50  fof(f7,axiom,(
% 23.62/3.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 23.62/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f18,plain,(
% 23.62/3.50    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 23.62/3.50    inference(ennf_transformation,[],[f7])).
% 23.62/3.50  
% 23.62/3.50  fof(f19,plain,(
% 23.62/3.50    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 23.62/3.50    inference(flattening,[],[f18])).
% 23.62/3.50  
% 23.62/3.50  fof(f37,plain,(
% 23.62/3.50    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f19])).
% 23.62/3.50  
% 23.62/3.50  fof(f41,plain,(
% 23.62/3.50    l1_pre_topc(sK0)),
% 23.62/3.50    inference(cnf_transformation,[],[f29])).
% 23.62/3.50  
% 23.62/3.50  fof(f8,axiom,(
% 23.62/3.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 23.62/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f20,plain,(
% 23.62/3.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 23.62/3.50    inference(ennf_transformation,[],[f8])).
% 23.62/3.50  
% 23.62/3.50  fof(f21,plain,(
% 23.62/3.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 23.62/3.50    inference(flattening,[],[f20])).
% 23.62/3.50  
% 23.62/3.50  fof(f38,plain,(
% 23.62/3.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f21])).
% 23.62/3.50  
% 23.62/3.50  fof(f5,axiom,(
% 23.62/3.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 23.62/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f15,plain,(
% 23.62/3.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 23.62/3.50    inference(ennf_transformation,[],[f5])).
% 23.62/3.50  
% 23.62/3.50  fof(f16,plain,(
% 23.62/3.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.62/3.50    inference(flattening,[],[f15])).
% 23.62/3.50  
% 23.62/3.50  fof(f34,plain,(
% 23.62/3.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.62/3.50    inference(cnf_transformation,[],[f16])).
% 23.62/3.50  
% 23.62/3.50  fof(f9,axiom,(
% 23.62/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 23.62/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f22,plain,(
% 23.62/3.50    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.62/3.50    inference(ennf_transformation,[],[f9])).
% 23.62/3.50  
% 23.62/3.50  fof(f39,plain,(
% 23.62/3.50    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f22])).
% 23.62/3.50  
% 23.62/3.50  fof(f6,axiom,(
% 23.62/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 23.62/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f17,plain,(
% 23.62/3.50    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.62/3.50    inference(ennf_transformation,[],[f6])).
% 23.62/3.50  
% 23.62/3.50  fof(f26,plain,(
% 23.62/3.50    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.62/3.50    inference(nnf_transformation,[],[f17])).
% 23.62/3.50  
% 23.62/3.50  fof(f35,plain,(
% 23.62/3.50    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f26])).
% 23.62/3.50  
% 23.62/3.50  fof(f43,plain,(
% 23.62/3.50    v5_tops_1(sK1,sK0)),
% 23.62/3.50    inference(cnf_transformation,[],[f29])).
% 23.62/3.50  
% 23.62/3.50  fof(f10,axiom,(
% 23.62/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 23.62/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f23,plain,(
% 23.62/3.50    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.62/3.50    inference(ennf_transformation,[],[f10])).
% 23.62/3.50  
% 23.62/3.50  fof(f40,plain,(
% 23.62/3.50    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f23])).
% 23.62/3.50  
% 23.62/3.50  fof(f3,axiom,(
% 23.62/3.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 23.62/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f14,plain,(
% 23.62/3.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 23.62/3.50    inference(ennf_transformation,[],[f3])).
% 23.62/3.50  
% 23.62/3.50  fof(f32,plain,(
% 23.62/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f14])).
% 23.62/3.50  
% 23.62/3.50  fof(f1,axiom,(
% 23.62/3.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 23.62/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f30,plain,(
% 23.62/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f1])).
% 23.62/3.50  
% 23.62/3.50  fof(f4,axiom,(
% 23.62/3.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 23.62/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f33,plain,(
% 23.62/3.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 23.62/3.50    inference(cnf_transformation,[],[f4])).
% 23.62/3.50  
% 23.62/3.50  fof(f2,axiom,(
% 23.62/3.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 23.62/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.62/3.50  
% 23.62/3.50  fof(f13,plain,(
% 23.62/3.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 23.62/3.50    inference(ennf_transformation,[],[f2])).
% 23.62/3.50  
% 23.62/3.50  fof(f31,plain,(
% 23.62/3.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 23.62/3.50    inference(cnf_transformation,[],[f13])).
% 23.62/3.50  
% 23.62/3.50  fof(f44,plain,(
% 23.62/3.50    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 23.62/3.50    inference(cnf_transformation,[],[f29])).
% 23.62/3.50  
% 23.62/3.50  cnf(c_13,negated_conjecture,
% 23.62/3.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 23.62/3.50      inference(cnf_transformation,[],[f42]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_513,plain,
% 23.62/3.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_7,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | ~ l1_pre_topc(X1) ),
% 23.62/3.50      inference(cnf_transformation,[],[f37]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_14,negated_conjecture,
% 23.62/3.50      ( l1_pre_topc(sK0) ),
% 23.62/3.50      inference(cnf_transformation,[],[f41]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_209,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | sK0 != X1 ),
% 23.62/3.50      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_210,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.62/3.50      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 23.62/3.50      inference(unflattening,[status(thm)],[c_209]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_509,plain,
% 23.62/3.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.62/3.50      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_8,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | ~ l1_pre_topc(X1) ),
% 23.62/3.50      inference(cnf_transformation,[],[f38]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_197,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | sK0 != X1 ),
% 23.62/3.50      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_198,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.62/3.50      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 23.62/3.50      inference(unflattening,[status(thm)],[c_197]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_510,plain,
% 23.62/3.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.62/3.50      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_198]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_4,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.62/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.62/3.50      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 23.62/3.50      inference(cnf_transformation,[],[f34]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_515,plain,
% 23.62/3.50      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 23.62/3.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 23.62/3.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_2250,plain,
% 23.62/3.50      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k2_xboole_0(X0,k2_tops_1(sK0,X1))
% 23.62/3.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.62/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_510,c_515]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_8142,plain,
% 23.62/3.50      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k2_tops_1(sK0,X1)) = k2_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X1))
% 23.62/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.62/3.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_509,c_2250]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_81726,plain,
% 23.62/3.50      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0)) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0))
% 23.62/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_513,c_8142]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_81759,plain,
% 23.62/3.50      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0)))
% 23.62/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_509,c_81726]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_88230,plain,
% 23.62/3.50      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_513,c_81759]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_9,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | ~ l1_pre_topc(X1)
% 23.62/3.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 23.62/3.50      inference(cnf_transformation,[],[f39]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_185,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 23.62/3.50      | sK0 != X1 ),
% 23.62/3.50      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_186,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.62/3.50      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 23.62/3.50      inference(unflattening,[status(thm)],[c_185]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_511,plain,
% 23.62/3.50      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 23.62/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_718,plain,
% 23.62/3.50      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
% 23.62/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_509,c_511]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_3173,plain,
% 23.62/3.50      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_513,c_718]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_6,plain,
% 23.62/3.50      ( ~ v5_tops_1(X0,X1)
% 23.62/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | ~ l1_pre_topc(X1)
% 23.62/3.50      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 23.62/3.50      inference(cnf_transformation,[],[f35]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_12,negated_conjecture,
% 23.62/3.50      ( v5_tops_1(sK1,sK0) ),
% 23.62/3.50      inference(cnf_transformation,[],[f43]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_164,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | ~ l1_pre_topc(X1)
% 23.62/3.50      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
% 23.62/3.50      | sK1 != X0
% 23.62/3.50      | sK0 != X1 ),
% 23.62/3.50      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_165,plain,
% 23.62/3.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.62/3.50      | ~ l1_pre_topc(sK0)
% 23.62/3.50      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 23.62/3.50      inference(unflattening,[status(thm)],[c_164]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_167,plain,
% 23.62/3.50      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 23.62/3.50      inference(global_propositional_subsumption,
% 23.62/3.50                [status(thm)],
% 23.62/3.50                [c_165,c_14,c_13]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_3185,plain,
% 23.62/3.50      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1 ),
% 23.62/3.50      inference(light_normalisation,[status(thm)],[c_3173,c_167]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_88242,plain,
% 23.62/3.50      ( k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1 ),
% 23.62/3.50      inference(light_normalisation,[status(thm)],[c_88230,c_3185]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_10,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
% 23.62/3.50      | ~ l1_pre_topc(X1) ),
% 23.62/3.50      inference(cnf_transformation,[],[f40]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_173,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.62/3.50      | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
% 23.62/3.50      | sK0 != X1 ),
% 23.62/3.50      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_174,plain,
% 23.62/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.62/3.50      | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k2_tops_1(sK0,X0)) ),
% 23.62/3.50      inference(unflattening,[status(thm)],[c_173]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_512,plain,
% 23.62/3.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.62/3.50      | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k2_tops_1(sK0,X0)) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_174]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_868,plain,
% 23.62/3.50      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 23.62/3.50      | r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_167,c_512]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_16,plain,
% 23.62/3.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_585,plain,
% 23.62/3.50      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 23.62/3.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 23.62/3.50      inference(instantiation,[status(thm)],[c_210]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_586,plain,
% 23.62/3.50      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 23.62/3.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_1374,plain,
% 23.62/3.50      ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 23.62/3.50      inference(global_propositional_subsumption,
% 23.62/3.50                [status(thm)],
% 23.62/3.50                [c_868,c_16,c_586]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_2,plain,
% 23.62/3.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 23.62/3.50      inference(cnf_transformation,[],[f32]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_517,plain,
% 23.62/3.50      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_1379,plain,
% 23.62/3.50      ( k2_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_1374,c_517]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_0,plain,
% 23.62/3.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 23.62/3.50      inference(cnf_transformation,[],[f30]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_3,plain,
% 23.62/3.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 23.62/3.50      inference(cnf_transformation,[],[f33]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_516,plain,
% 23.62/3.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_967,plain,
% 23.62/3.50      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_0,c_516]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_1,plain,
% 23.62/3.50      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 23.62/3.50      inference(cnf_transformation,[],[f31]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_518,plain,
% 23.62/3.50      ( r1_tarski(X0,X1) = iProver_top
% 23.62/3.50      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_1355,plain,
% 23.62/3.50      ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_967,c_518]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_3641,plain,
% 23.62/3.50      ( r1_tarski(k2_tops_1(sK0,sK1),k2_xboole_0(X0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_1379,c_1355]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_88379,plain,
% 23.62/3.50      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 23.62/3.50      inference(superposition,[status(thm)],[c_88242,c_3641]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_11,negated_conjecture,
% 23.62/3.50      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 23.62/3.50      inference(cnf_transformation,[],[f44]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_514,plain,
% 23.62/3.50      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 23.62/3.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(c_527,plain,
% 23.62/3.50      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 23.62/3.50      inference(light_normalisation,[status(thm)],[c_514,c_167]) ).
% 23.62/3.50  
% 23.62/3.50  cnf(contradiction,plain,
% 23.62/3.50      ( $false ),
% 23.62/3.50      inference(minisat,[status(thm)],[c_88379,c_527]) ).
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.62/3.50  
% 23.62/3.50  ------                               Statistics
% 23.62/3.50  
% 23.62/3.50  ------ General
% 23.62/3.50  
% 23.62/3.50  abstr_ref_over_cycles:                  0
% 23.62/3.50  abstr_ref_under_cycles:                 0
% 23.62/3.50  gc_basic_clause_elim:                   0
% 23.62/3.50  forced_gc_time:                         0
% 23.62/3.50  parsing_time:                           0.009
% 23.62/3.50  unif_index_cands_time:                  0.
% 23.62/3.50  unif_index_add_time:                    0.
% 23.62/3.50  orderings_time:                         0.
% 23.62/3.50  out_proof_time:                         0.013
% 23.62/3.50  total_time:                             2.805
% 23.62/3.50  num_of_symbols:                         44
% 23.62/3.50  num_of_terms:                           89079
% 23.62/3.50  
% 23.62/3.50  ------ Preprocessing
% 23.62/3.50  
% 23.62/3.50  num_of_splits:                          0
% 23.62/3.50  num_of_split_atoms:                     0
% 23.62/3.50  num_of_reused_defs:                     0
% 23.62/3.50  num_eq_ax_congr_red:                    9
% 23.62/3.50  num_of_sem_filtered_clauses:            1
% 23.62/3.50  num_of_subtypes:                        0
% 23.62/3.50  monotx_restored_types:                  0
% 23.62/3.50  sat_num_of_epr_types:                   0
% 23.62/3.50  sat_num_of_non_cyclic_types:            0
% 23.62/3.50  sat_guarded_non_collapsed_types:        0
% 23.62/3.50  num_pure_diseq_elim:                    0
% 23.62/3.50  simp_replaced_by:                       0
% 23.62/3.50  res_preprocessed:                       72
% 23.62/3.50  prep_upred:                             0
% 23.62/3.50  prep_unflattend:                        6
% 23.62/3.50  smt_new_axioms:                         0
% 23.62/3.50  pred_elim_cands:                        2
% 23.62/3.50  pred_elim:                              2
% 23.62/3.50  pred_elim_cl:                           3
% 23.62/3.50  pred_elim_cycles:                       4
% 23.62/3.50  merged_defs:                            0
% 23.62/3.50  merged_defs_ncl:                        0
% 23.62/3.50  bin_hyper_res:                          0
% 23.62/3.50  prep_cycles:                            4
% 23.62/3.50  pred_elim_time:                         0.001
% 23.62/3.50  splitting_time:                         0.
% 23.62/3.50  sem_filter_time:                        0.
% 23.62/3.50  monotx_time:                            0.001
% 23.62/3.50  subtype_inf_time:                       0.
% 23.62/3.50  
% 23.62/3.50  ------ Problem properties
% 23.62/3.50  
% 23.62/3.50  clauses:                                12
% 23.62/3.50  conjectures:                            2
% 23.62/3.50  epr:                                    0
% 23.62/3.50  horn:                                   12
% 23.62/3.50  ground:                                 3
% 23.62/3.50  unary:                                  5
% 23.62/3.50  binary:                                 6
% 23.62/3.50  lits:                                   20
% 23.62/3.50  lits_eq:                                5
% 23.62/3.50  fd_pure:                                0
% 23.62/3.50  fd_pseudo:                              0
% 23.62/3.50  fd_cond:                                0
% 23.62/3.50  fd_pseudo_cond:                         0
% 23.62/3.50  ac_symbols:                             0
% 23.62/3.50  
% 23.62/3.50  ------ Propositional Solver
% 23.62/3.50  
% 23.62/3.50  prop_solver_calls:                      35
% 23.62/3.50  prop_fast_solver_calls:                 830
% 23.62/3.50  smt_solver_calls:                       0
% 23.62/3.50  smt_fast_solver_calls:                  0
% 23.62/3.50  prop_num_of_clauses:                    32960
% 23.62/3.50  prop_preprocess_simplified:             52377
% 23.62/3.50  prop_fo_subsumed:                       3
% 23.62/3.50  prop_solver_time:                       0.
% 23.62/3.50  smt_solver_time:                        0.
% 23.62/3.50  smt_fast_solver_time:                   0.
% 23.62/3.50  prop_fast_solver_time:                  0.
% 23.62/3.50  prop_unsat_core_time:                   0.003
% 23.62/3.50  
% 23.62/3.50  ------ QBF
% 23.62/3.50  
% 23.62/3.50  qbf_q_res:                              0
% 23.62/3.50  qbf_num_tautologies:                    0
% 23.62/3.50  qbf_prep_cycles:                        0
% 23.62/3.50  
% 23.62/3.50  ------ BMC1
% 23.62/3.50  
% 23.62/3.50  bmc1_current_bound:                     -1
% 23.62/3.50  bmc1_last_solved_bound:                 -1
% 23.62/3.50  bmc1_unsat_core_size:                   -1
% 23.62/3.50  bmc1_unsat_core_parents_size:           -1
% 23.62/3.50  bmc1_merge_next_fun:                    0
% 23.62/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.62/3.50  
% 23.62/3.50  ------ Instantiation
% 23.62/3.50  
% 23.62/3.50  inst_num_of_clauses:                    8102
% 23.62/3.50  inst_num_in_passive:                    5058
% 23.62/3.50  inst_num_in_active:                     1548
% 23.62/3.50  inst_num_in_unprocessed:                1532
% 23.62/3.50  inst_num_of_loops:                      1860
% 23.62/3.50  inst_num_of_learning_restarts:          0
% 23.62/3.50  inst_num_moves_active_passive:          311
% 23.62/3.50  inst_lit_activity:                      0
% 23.62/3.50  inst_lit_activity_moves:                4
% 23.62/3.50  inst_num_tautologies:                   0
% 23.62/3.50  inst_num_prop_implied:                  0
% 23.62/3.50  inst_num_existing_simplified:           0
% 23.62/3.50  inst_num_eq_res_simplified:             0
% 23.62/3.50  inst_num_child_elim:                    0
% 23.62/3.50  inst_num_of_dismatching_blockings:      5498
% 23.62/3.50  inst_num_of_non_proper_insts:           6201
% 23.62/3.50  inst_num_of_duplicates:                 0
% 23.62/3.50  inst_inst_num_from_inst_to_res:         0
% 23.62/3.50  inst_dismatching_checking_time:         0.
% 23.62/3.50  
% 23.62/3.50  ------ Resolution
% 23.62/3.50  
% 23.62/3.50  res_num_of_clauses:                     0
% 23.62/3.50  res_num_in_passive:                     0
% 23.62/3.50  res_num_in_active:                      0
% 23.62/3.50  res_num_of_loops:                       76
% 23.62/3.50  res_forward_subset_subsumed:            3408
% 23.62/3.50  res_backward_subset_subsumed:           72
% 23.62/3.50  res_forward_subsumed:                   0
% 23.62/3.50  res_backward_subsumed:                  0
% 23.62/3.50  res_forward_subsumption_resolution:     0
% 23.62/3.50  res_backward_subsumption_resolution:    0
% 23.62/3.50  res_clause_to_clause_subsumption:       147506
% 23.62/3.50  res_orphan_elimination:                 0
% 23.62/3.50  res_tautology_del:                      258
% 23.62/3.50  res_num_eq_res_simplified:              0
% 23.62/3.50  res_num_sel_changes:                    0
% 23.62/3.50  res_moves_from_active_to_pass:          0
% 23.62/3.50  
% 23.62/3.50  ------ Superposition
% 23.62/3.50  
% 23.62/3.50  sup_time_total:                         0.
% 23.62/3.50  sup_time_generating:                    0.
% 23.62/3.50  sup_time_sim_full:                      0.
% 23.62/3.50  sup_time_sim_immed:                     0.
% 23.62/3.50  
% 23.62/3.50  sup_num_of_clauses:                     3192
% 23.62/3.50  sup_num_in_active:                      365
% 23.62/3.50  sup_num_in_passive:                     2827
% 23.62/3.50  sup_num_of_loops:                       370
% 23.62/3.50  sup_fw_superposition:                   9279
% 23.62/3.50  sup_bw_superposition:                   7326
% 23.62/3.50  sup_immediate_simplified:               5930
% 23.62/3.50  sup_given_eliminated:                   1
% 23.62/3.50  comparisons_done:                       0
% 23.62/3.50  comparisons_avoided:                    0
% 23.62/3.50  
% 23.62/3.50  ------ Simplifications
% 23.62/3.50  
% 23.62/3.50  
% 23.62/3.50  sim_fw_subset_subsumed:                 0
% 23.62/3.50  sim_bw_subset_subsumed:                 0
% 23.62/3.50  sim_fw_subsumed:                        2086
% 23.62/3.50  sim_bw_subsumed:                        5
% 23.62/3.50  sim_fw_subsumption_res:                 0
% 23.62/3.50  sim_bw_subsumption_res:                 0
% 23.62/3.50  sim_tautology_del:                      81
% 23.62/3.50  sim_eq_tautology_del:                   273
% 23.62/3.50  sim_eq_res_simp:                        0
% 23.62/3.50  sim_fw_demodulated:                     1503
% 23.62/3.50  sim_bw_demodulated:                     243
% 23.62/3.50  sim_light_normalised:                   2801
% 23.62/3.50  sim_joinable_taut:                      0
% 23.62/3.50  sim_joinable_simp:                      0
% 23.62/3.50  sim_ac_normalised:                      0
% 23.62/3.50  sim_smt_subsumption:                    0
% 23.62/3.50  
%------------------------------------------------------------------------------
