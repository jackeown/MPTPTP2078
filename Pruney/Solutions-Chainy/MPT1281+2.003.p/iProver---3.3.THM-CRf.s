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
% DateTime   : Thu Dec  3 12:15:39 EST 2020

% Result     : Theorem 11.34s
% Output     : CNFRefutation 11.34s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 334 expanded)
%              Number of clauses        :   65 ( 110 expanded)
%              Number of leaves         :   13 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          :  264 (1118 expanded)
%              Number of equality atoms :   82 ( 117 expanded)
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

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f34,f33])).

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

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f44,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_294,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_494,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_195,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_195])).

cnf(c_289,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_196])).

cnf(c_498,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_183,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_184,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_183])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_184])).

cnf(c_497,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X0_44))
    | ~ m1_subset_1(X1_42,k1_zfmisc_1(X0_44))
    | k4_subset_1(X0_44,X1_42,X0_42) = k3_tarski(k2_tarski(X1_42,X0_42)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_492,plain,
    ( k4_subset_1(X0_44,X0_42,X1_42) = k3_tarski(k2_tarski(X0_42,X1_42))
    | m1_subset_1(X0_42,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X1_42,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_981,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42)) = k3_tarski(k2_tarski(X0_42,k2_tops_1(sK0,X1_42)))
    | m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_497,c_492])).

cnf(c_3290,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_42),k2_tops_1(sK0,X1_42)) = k3_tarski(k2_tarski(k1_tops_1(sK0,X0_42),k2_tops_1(sK0,X1_42)))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_981])).

cnf(c_36465,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_42)) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_42)))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_3290])).

cnf(c_37119,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_42))) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_42))))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_36465])).

cnf(c_37313,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_494,c_37119])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_171,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_172,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_171])).

cnf(c_291,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X0_42)) = k2_pre_topc(sK0,X0_42) ),
    inference(subtyping,[status(esa)],[c_172])).

cnf(c_496,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X0_42)) = k2_pre_topc(sK0,X0_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_785,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_42),k2_tops_1(sK0,k1_tops_1(sK0,X0_42))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_498,c_496])).

cnf(c_1445,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_494,c_785])).

cnf(c_5,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_11,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_150,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_151,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_150])).

cnf(c_153,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_151,c_13,c_12])).

cnf(c_293,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_153])).

cnf(c_1448,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1445,c_293])).

cnf(c_37316,plain,
    ( k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_37313,c_1448])).

cnf(c_2,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_297,plain,
    ( k2_tarski(X0_42,X1_42) = k2_tarski(X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_298,plain,
    ( r1_tarski(X0_42,k3_tarski(k2_tarski(X0_42,X1_42))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_491,plain,
    ( r1_tarski(X0_42,k3_tarski(k2_tarski(X0_42,X1_42))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_921,plain,
    ( r1_tarski(X0_42,k3_tarski(k2_tarski(X1_42,X0_42))) = iProver_top ),
    inference(superposition,[status(thm)],[c_297,c_491])).

cnf(c_37576,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_37316,c_921])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_299,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(X2_42,X0_42)
    | r1_tarski(X2_42,X1_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_528,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),X0_42)
    | r1_tarski(k2_tops_1(sK0,sK1),X1_42) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_620,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,X0_42),X1_42)
    | r1_tarski(k2_tops_1(sK0,sK1),X1_42)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,X0_42)) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_3894,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),X0_42)
    | r1_tarski(k2_tops_1(sK0,sK1),X0_42)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_3898,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),X0_42) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),X0_42) = iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3894])).

cnf(c_3900,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK1) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3898])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_159,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_160,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_159])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0_42)),k2_tops_1(sK0,X0_42)) ),
    inference(subtyping,[status(esa)],[c_160])).

cnf(c_495,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0_42)),k2_tops_1(sK0,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_698,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_293,c_495])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_295,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_493,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_499,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_493,c_293])).

cnf(c_341,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_343,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37576,c_3900,c_698,c_499,c_343,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:29:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.34/2.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.34/2.06  
% 11.34/2.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.34/2.06  
% 11.34/2.06  ------  iProver source info
% 11.34/2.06  
% 11.34/2.06  git: date: 2020-06-30 10:37:57 +0100
% 11.34/2.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.34/2.06  git: non_committed_changes: false
% 11.34/2.06  git: last_make_outside_of_git: false
% 11.34/2.06  
% 11.34/2.06  ------ 
% 11.34/2.06  
% 11.34/2.06  ------ Input Options
% 11.34/2.06  
% 11.34/2.06  --out_options                           all
% 11.34/2.06  --tptp_safe_out                         true
% 11.34/2.06  --problem_path                          ""
% 11.34/2.06  --include_path                          ""
% 11.34/2.06  --clausifier                            res/vclausify_rel
% 11.34/2.06  --clausifier_options                    ""
% 11.34/2.06  --stdin                                 false
% 11.34/2.06  --stats_out                             all
% 11.34/2.06  
% 11.34/2.06  ------ General Options
% 11.34/2.06  
% 11.34/2.06  --fof                                   false
% 11.34/2.06  --time_out_real                         305.
% 11.34/2.06  --time_out_virtual                      -1.
% 11.34/2.06  --symbol_type_check                     false
% 11.34/2.06  --clausify_out                          false
% 11.34/2.06  --sig_cnt_out                           false
% 11.34/2.07  --trig_cnt_out                          false
% 11.34/2.07  --trig_cnt_out_tolerance                1.
% 11.34/2.07  --trig_cnt_out_sk_spl                   false
% 11.34/2.07  --abstr_cl_out                          false
% 11.34/2.07  
% 11.34/2.07  ------ Global Options
% 11.34/2.07  
% 11.34/2.07  --schedule                              default
% 11.34/2.07  --add_important_lit                     false
% 11.34/2.07  --prop_solver_per_cl                    1000
% 11.34/2.07  --min_unsat_core                        false
% 11.34/2.07  --soft_assumptions                      false
% 11.34/2.07  --soft_lemma_size                       3
% 11.34/2.07  --prop_impl_unit_size                   0
% 11.34/2.07  --prop_impl_unit                        []
% 11.34/2.07  --share_sel_clauses                     true
% 11.34/2.07  --reset_solvers                         false
% 11.34/2.07  --bc_imp_inh                            [conj_cone]
% 11.34/2.07  --conj_cone_tolerance                   3.
% 11.34/2.07  --extra_neg_conj                        none
% 11.34/2.07  --large_theory_mode                     true
% 11.34/2.07  --prolific_symb_bound                   200
% 11.34/2.07  --lt_threshold                          2000
% 11.34/2.07  --clause_weak_htbl                      true
% 11.34/2.07  --gc_record_bc_elim                     false
% 11.34/2.07  
% 11.34/2.07  ------ Preprocessing Options
% 11.34/2.07  
% 11.34/2.07  --preprocessing_flag                    true
% 11.34/2.07  --time_out_prep_mult                    0.1
% 11.34/2.07  --splitting_mode                        input
% 11.34/2.07  --splitting_grd                         true
% 11.34/2.07  --splitting_cvd                         false
% 11.34/2.07  --splitting_cvd_svl                     false
% 11.34/2.07  --splitting_nvd                         32
% 11.34/2.07  --sub_typing                            true
% 11.34/2.07  --prep_gs_sim                           true
% 11.34/2.07  --prep_unflatten                        true
% 11.34/2.07  --prep_res_sim                          true
% 11.34/2.07  --prep_upred                            true
% 11.34/2.07  --prep_sem_filter                       exhaustive
% 11.34/2.07  --prep_sem_filter_out                   false
% 11.34/2.07  --pred_elim                             true
% 11.34/2.07  --res_sim_input                         true
% 11.34/2.07  --eq_ax_congr_red                       true
% 11.34/2.07  --pure_diseq_elim                       true
% 11.34/2.07  --brand_transform                       false
% 11.34/2.07  --non_eq_to_eq                          false
% 11.34/2.07  --prep_def_merge                        true
% 11.34/2.07  --prep_def_merge_prop_impl              false
% 11.34/2.07  --prep_def_merge_mbd                    true
% 11.34/2.07  --prep_def_merge_tr_red                 false
% 11.34/2.07  --prep_def_merge_tr_cl                  false
% 11.34/2.07  --smt_preprocessing                     true
% 11.34/2.07  --smt_ac_axioms                         fast
% 11.34/2.07  --preprocessed_out                      false
% 11.34/2.07  --preprocessed_stats                    false
% 11.34/2.07  
% 11.34/2.07  ------ Abstraction refinement Options
% 11.34/2.07  
% 11.34/2.07  --abstr_ref                             []
% 11.34/2.07  --abstr_ref_prep                        false
% 11.34/2.07  --abstr_ref_until_sat                   false
% 11.34/2.07  --abstr_ref_sig_restrict                funpre
% 11.34/2.07  --abstr_ref_af_restrict_to_split_sk     false
% 11.34/2.07  --abstr_ref_under                       []
% 11.34/2.07  
% 11.34/2.07  ------ SAT Options
% 11.34/2.07  
% 11.34/2.07  --sat_mode                              false
% 11.34/2.07  --sat_fm_restart_options                ""
% 11.34/2.07  --sat_gr_def                            false
% 11.34/2.07  --sat_epr_types                         true
% 11.34/2.07  --sat_non_cyclic_types                  false
% 11.34/2.07  --sat_finite_models                     false
% 11.34/2.07  --sat_fm_lemmas                         false
% 11.34/2.07  --sat_fm_prep                           false
% 11.34/2.07  --sat_fm_uc_incr                        true
% 11.34/2.07  --sat_out_model                         small
% 11.34/2.07  --sat_out_clauses                       false
% 11.34/2.07  
% 11.34/2.07  ------ QBF Options
% 11.34/2.07  
% 11.34/2.07  --qbf_mode                              false
% 11.34/2.07  --qbf_elim_univ                         false
% 11.34/2.07  --qbf_dom_inst                          none
% 11.34/2.07  --qbf_dom_pre_inst                      false
% 11.34/2.07  --qbf_sk_in                             false
% 11.34/2.07  --qbf_pred_elim                         true
% 11.34/2.07  --qbf_split                             512
% 11.34/2.07  
% 11.34/2.07  ------ BMC1 Options
% 11.34/2.07  
% 11.34/2.07  --bmc1_incremental                      false
% 11.34/2.07  --bmc1_axioms                           reachable_all
% 11.34/2.07  --bmc1_min_bound                        0
% 11.34/2.07  --bmc1_max_bound                        -1
% 11.34/2.07  --bmc1_max_bound_default                -1
% 11.34/2.07  --bmc1_symbol_reachability              true
% 11.34/2.07  --bmc1_property_lemmas                  false
% 11.34/2.07  --bmc1_k_induction                      false
% 11.34/2.07  --bmc1_non_equiv_states                 false
% 11.34/2.07  --bmc1_deadlock                         false
% 11.34/2.07  --bmc1_ucm                              false
% 11.34/2.07  --bmc1_add_unsat_core                   none
% 11.34/2.07  --bmc1_unsat_core_children              false
% 11.34/2.07  --bmc1_unsat_core_extrapolate_axioms    false
% 11.34/2.07  --bmc1_out_stat                         full
% 11.34/2.07  --bmc1_ground_init                      false
% 11.34/2.07  --bmc1_pre_inst_next_state              false
% 11.34/2.07  --bmc1_pre_inst_state                   false
% 11.34/2.07  --bmc1_pre_inst_reach_state             false
% 11.34/2.07  --bmc1_out_unsat_core                   false
% 11.34/2.07  --bmc1_aig_witness_out                  false
% 11.34/2.07  --bmc1_verbose                          false
% 11.34/2.07  --bmc1_dump_clauses_tptp                false
% 11.34/2.07  --bmc1_dump_unsat_core_tptp             false
% 11.34/2.07  --bmc1_dump_file                        -
% 11.34/2.07  --bmc1_ucm_expand_uc_limit              128
% 11.34/2.07  --bmc1_ucm_n_expand_iterations          6
% 11.34/2.07  --bmc1_ucm_extend_mode                  1
% 11.34/2.07  --bmc1_ucm_init_mode                    2
% 11.34/2.07  --bmc1_ucm_cone_mode                    none
% 11.34/2.07  --bmc1_ucm_reduced_relation_type        0
% 11.34/2.07  --bmc1_ucm_relax_model                  4
% 11.34/2.07  --bmc1_ucm_full_tr_after_sat            true
% 11.34/2.07  --bmc1_ucm_expand_neg_assumptions       false
% 11.34/2.07  --bmc1_ucm_layered_model                none
% 11.34/2.07  --bmc1_ucm_max_lemma_size               10
% 11.34/2.07  
% 11.34/2.07  ------ AIG Options
% 11.34/2.07  
% 11.34/2.07  --aig_mode                              false
% 11.34/2.07  
% 11.34/2.07  ------ Instantiation Options
% 11.34/2.07  
% 11.34/2.07  --instantiation_flag                    true
% 11.34/2.07  --inst_sos_flag                         true
% 11.34/2.07  --inst_sos_phase                        true
% 11.34/2.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.34/2.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.34/2.07  --inst_lit_sel_side                     num_symb
% 11.34/2.07  --inst_solver_per_active                1400
% 11.34/2.07  --inst_solver_calls_frac                1.
% 11.34/2.07  --inst_passive_queue_type               priority_queues
% 11.34/2.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.34/2.07  --inst_passive_queues_freq              [25;2]
% 11.34/2.07  --inst_dismatching                      true
% 11.34/2.07  --inst_eager_unprocessed_to_passive     true
% 11.34/2.07  --inst_prop_sim_given                   true
% 11.34/2.07  --inst_prop_sim_new                     false
% 11.34/2.07  --inst_subs_new                         false
% 11.34/2.07  --inst_eq_res_simp                      false
% 11.34/2.07  --inst_subs_given                       false
% 11.34/2.07  --inst_orphan_elimination               true
% 11.34/2.07  --inst_learning_loop_flag               true
% 11.34/2.07  --inst_learning_start                   3000
% 11.34/2.07  --inst_learning_factor                  2
% 11.34/2.07  --inst_start_prop_sim_after_learn       3
% 11.34/2.07  --inst_sel_renew                        solver
% 11.34/2.07  --inst_lit_activity_flag                true
% 11.34/2.07  --inst_restr_to_given                   false
% 11.34/2.07  --inst_activity_threshold               500
% 11.34/2.07  --inst_out_proof                        true
% 11.34/2.07  
% 11.34/2.07  ------ Resolution Options
% 11.34/2.07  
% 11.34/2.07  --resolution_flag                       true
% 11.34/2.07  --res_lit_sel                           adaptive
% 11.34/2.07  --res_lit_sel_side                      none
% 11.34/2.07  --res_ordering                          kbo
% 11.34/2.07  --res_to_prop_solver                    active
% 11.34/2.07  --res_prop_simpl_new                    false
% 11.34/2.07  --res_prop_simpl_given                  true
% 11.34/2.07  --res_passive_queue_type                priority_queues
% 11.34/2.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.34/2.07  --res_passive_queues_freq               [15;5]
% 11.34/2.07  --res_forward_subs                      full
% 11.34/2.07  --res_backward_subs                     full
% 11.34/2.07  --res_forward_subs_resolution           true
% 11.34/2.07  --res_backward_subs_resolution          true
% 11.34/2.07  --res_orphan_elimination                true
% 11.34/2.07  --res_time_limit                        2.
% 11.34/2.07  --res_out_proof                         true
% 11.34/2.07  
% 11.34/2.07  ------ Superposition Options
% 11.34/2.07  
% 11.34/2.07  --superposition_flag                    true
% 11.34/2.07  --sup_passive_queue_type                priority_queues
% 11.34/2.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.34/2.07  --sup_passive_queues_freq               [8;1;4]
% 11.34/2.07  --demod_completeness_check              fast
% 11.34/2.07  --demod_use_ground                      true
% 11.34/2.07  --sup_to_prop_solver                    passive
% 11.34/2.07  --sup_prop_simpl_new                    true
% 11.34/2.07  --sup_prop_simpl_given                  true
% 11.34/2.07  --sup_fun_splitting                     true
% 11.34/2.07  --sup_smt_interval                      50000
% 11.34/2.07  
% 11.34/2.07  ------ Superposition Simplification Setup
% 11.34/2.07  
% 11.34/2.07  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.34/2.07  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.34/2.07  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.34/2.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.34/2.07  --sup_full_triv                         [TrivRules;PropSubs]
% 11.34/2.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.34/2.07  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.34/2.07  --sup_immed_triv                        [TrivRules]
% 11.34/2.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.34/2.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.34/2.07  --sup_immed_bw_main                     []
% 11.34/2.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.34/2.07  --sup_input_triv                        [Unflattening;TrivRules]
% 11.34/2.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.34/2.07  --sup_input_bw                          []
% 11.34/2.07  
% 11.34/2.07  ------ Combination Options
% 11.34/2.07  
% 11.34/2.07  --comb_res_mult                         3
% 11.34/2.07  --comb_sup_mult                         2
% 11.34/2.07  --comb_inst_mult                        10
% 11.34/2.07  
% 11.34/2.07  ------ Debug Options
% 11.34/2.07  
% 11.34/2.07  --dbg_backtrace                         false
% 11.34/2.07  --dbg_dump_prop_clauses                 false
% 11.34/2.07  --dbg_dump_prop_clauses_file            -
% 11.34/2.07  --dbg_out_stat                          false
% 11.34/2.07  ------ Parsing...
% 11.34/2.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.34/2.07  
% 11.34/2.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.34/2.07  
% 11.34/2.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.34/2.07  
% 11.34/2.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.34/2.07  ------ Proving...
% 11.34/2.07  ------ Problem Properties 
% 11.34/2.07  
% 11.34/2.07  
% 11.34/2.07  clauses                                 11
% 11.34/2.07  conjectures                             2
% 11.34/2.07  EPR                                     1
% 11.34/2.07  Horn                                    11
% 11.34/2.07  unary                                   5
% 11.34/2.07  binary                                  4
% 11.34/2.07  lits                                    19
% 11.34/2.07  lits eq                                 4
% 11.34/2.07  fd_pure                                 0
% 11.34/2.07  fd_pseudo                               0
% 11.34/2.07  fd_cond                                 0
% 11.34/2.07  fd_pseudo_cond                          0
% 11.34/2.07  AC symbols                              0
% 11.34/2.07  
% 11.34/2.07  ------ Schedule dynamic 5 is on 
% 11.34/2.07  
% 11.34/2.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.34/2.07  
% 11.34/2.07  
% 11.34/2.07  ------ 
% 11.34/2.07  Current options:
% 11.34/2.07  ------ 
% 11.34/2.07  
% 11.34/2.07  ------ Input Options
% 11.34/2.07  
% 11.34/2.07  --out_options                           all
% 11.34/2.07  --tptp_safe_out                         true
% 11.34/2.07  --problem_path                          ""
% 11.34/2.07  --include_path                          ""
% 11.34/2.07  --clausifier                            res/vclausify_rel
% 11.34/2.07  --clausifier_options                    ""
% 11.34/2.07  --stdin                                 false
% 11.34/2.07  --stats_out                             all
% 11.34/2.07  
% 11.34/2.07  ------ General Options
% 11.34/2.07  
% 11.34/2.07  --fof                                   false
% 11.34/2.07  --time_out_real                         305.
% 11.34/2.07  --time_out_virtual                      -1.
% 11.34/2.07  --symbol_type_check                     false
% 11.34/2.07  --clausify_out                          false
% 11.34/2.07  --sig_cnt_out                           false
% 11.34/2.07  --trig_cnt_out                          false
% 11.34/2.07  --trig_cnt_out_tolerance                1.
% 11.34/2.07  --trig_cnt_out_sk_spl                   false
% 11.34/2.07  --abstr_cl_out                          false
% 11.34/2.07  
% 11.34/2.07  ------ Global Options
% 11.34/2.07  
% 11.34/2.07  --schedule                              default
% 11.34/2.07  --add_important_lit                     false
% 11.34/2.07  --prop_solver_per_cl                    1000
% 11.34/2.07  --min_unsat_core                        false
% 11.34/2.07  --soft_assumptions                      false
% 11.34/2.07  --soft_lemma_size                       3
% 11.34/2.07  --prop_impl_unit_size                   0
% 11.34/2.07  --prop_impl_unit                        []
% 11.34/2.07  --share_sel_clauses                     true
% 11.34/2.07  --reset_solvers                         false
% 11.34/2.07  --bc_imp_inh                            [conj_cone]
% 11.34/2.07  --conj_cone_tolerance                   3.
% 11.34/2.07  --extra_neg_conj                        none
% 11.34/2.07  --large_theory_mode                     true
% 11.34/2.07  --prolific_symb_bound                   200
% 11.34/2.07  --lt_threshold                          2000
% 11.34/2.07  --clause_weak_htbl                      true
% 11.34/2.07  --gc_record_bc_elim                     false
% 11.34/2.07  
% 11.34/2.07  ------ Preprocessing Options
% 11.34/2.07  
% 11.34/2.07  --preprocessing_flag                    true
% 11.34/2.07  --time_out_prep_mult                    0.1
% 11.34/2.07  --splitting_mode                        input
% 11.34/2.07  --splitting_grd                         true
% 11.34/2.07  --splitting_cvd                         false
% 11.34/2.07  --splitting_cvd_svl                     false
% 11.34/2.07  --splitting_nvd                         32
% 11.34/2.07  --sub_typing                            true
% 11.34/2.07  --prep_gs_sim                           true
% 11.34/2.07  --prep_unflatten                        true
% 11.34/2.07  --prep_res_sim                          true
% 11.34/2.07  --prep_upred                            true
% 11.34/2.07  --prep_sem_filter                       exhaustive
% 11.34/2.07  --prep_sem_filter_out                   false
% 11.34/2.07  --pred_elim                             true
% 11.34/2.07  --res_sim_input                         true
% 11.34/2.07  --eq_ax_congr_red                       true
% 11.34/2.07  --pure_diseq_elim                       true
% 11.34/2.07  --brand_transform                       false
% 11.34/2.07  --non_eq_to_eq                          false
% 11.34/2.07  --prep_def_merge                        true
% 11.34/2.07  --prep_def_merge_prop_impl              false
% 11.34/2.07  --prep_def_merge_mbd                    true
% 11.34/2.07  --prep_def_merge_tr_red                 false
% 11.34/2.07  --prep_def_merge_tr_cl                  false
% 11.34/2.07  --smt_preprocessing                     true
% 11.34/2.07  --smt_ac_axioms                         fast
% 11.34/2.07  --preprocessed_out                      false
% 11.34/2.07  --preprocessed_stats                    false
% 11.34/2.07  
% 11.34/2.07  ------ Abstraction refinement Options
% 11.34/2.07  
% 11.34/2.07  --abstr_ref                             []
% 11.34/2.07  --abstr_ref_prep                        false
% 11.34/2.07  --abstr_ref_until_sat                   false
% 11.34/2.07  --abstr_ref_sig_restrict                funpre
% 11.34/2.07  --abstr_ref_af_restrict_to_split_sk     false
% 11.34/2.07  --abstr_ref_under                       []
% 11.34/2.07  
% 11.34/2.07  ------ SAT Options
% 11.34/2.07  
% 11.34/2.07  --sat_mode                              false
% 11.34/2.07  --sat_fm_restart_options                ""
% 11.34/2.07  --sat_gr_def                            false
% 11.34/2.07  --sat_epr_types                         true
% 11.34/2.07  --sat_non_cyclic_types                  false
% 11.34/2.07  --sat_finite_models                     false
% 11.34/2.07  --sat_fm_lemmas                         false
% 11.34/2.07  --sat_fm_prep                           false
% 11.34/2.07  --sat_fm_uc_incr                        true
% 11.34/2.07  --sat_out_model                         small
% 11.34/2.07  --sat_out_clauses                       false
% 11.34/2.07  
% 11.34/2.07  ------ QBF Options
% 11.34/2.07  
% 11.34/2.07  --qbf_mode                              false
% 11.34/2.07  --qbf_elim_univ                         false
% 11.34/2.07  --qbf_dom_inst                          none
% 11.34/2.07  --qbf_dom_pre_inst                      false
% 11.34/2.07  --qbf_sk_in                             false
% 11.34/2.07  --qbf_pred_elim                         true
% 11.34/2.07  --qbf_split                             512
% 11.34/2.07  
% 11.34/2.07  ------ BMC1 Options
% 11.34/2.07  
% 11.34/2.07  --bmc1_incremental                      false
% 11.34/2.07  --bmc1_axioms                           reachable_all
% 11.34/2.07  --bmc1_min_bound                        0
% 11.34/2.07  --bmc1_max_bound                        -1
% 11.34/2.07  --bmc1_max_bound_default                -1
% 11.34/2.07  --bmc1_symbol_reachability              true
% 11.34/2.07  --bmc1_property_lemmas                  false
% 11.34/2.07  --bmc1_k_induction                      false
% 11.34/2.07  --bmc1_non_equiv_states                 false
% 11.34/2.07  --bmc1_deadlock                         false
% 11.34/2.07  --bmc1_ucm                              false
% 11.34/2.07  --bmc1_add_unsat_core                   none
% 11.34/2.07  --bmc1_unsat_core_children              false
% 11.34/2.07  --bmc1_unsat_core_extrapolate_axioms    false
% 11.34/2.07  --bmc1_out_stat                         full
% 11.34/2.07  --bmc1_ground_init                      false
% 11.34/2.07  --bmc1_pre_inst_next_state              false
% 11.34/2.07  --bmc1_pre_inst_state                   false
% 11.34/2.07  --bmc1_pre_inst_reach_state             false
% 11.34/2.07  --bmc1_out_unsat_core                   false
% 11.34/2.07  --bmc1_aig_witness_out                  false
% 11.34/2.07  --bmc1_verbose                          false
% 11.34/2.07  --bmc1_dump_clauses_tptp                false
% 11.34/2.07  --bmc1_dump_unsat_core_tptp             false
% 11.34/2.07  --bmc1_dump_file                        -
% 11.34/2.07  --bmc1_ucm_expand_uc_limit              128
% 11.34/2.07  --bmc1_ucm_n_expand_iterations          6
% 11.34/2.07  --bmc1_ucm_extend_mode                  1
% 11.34/2.07  --bmc1_ucm_init_mode                    2
% 11.34/2.07  --bmc1_ucm_cone_mode                    none
% 11.34/2.07  --bmc1_ucm_reduced_relation_type        0
% 11.34/2.07  --bmc1_ucm_relax_model                  4
% 11.34/2.07  --bmc1_ucm_full_tr_after_sat            true
% 11.34/2.07  --bmc1_ucm_expand_neg_assumptions       false
% 11.34/2.07  --bmc1_ucm_layered_model                none
% 11.34/2.07  --bmc1_ucm_max_lemma_size               10
% 11.34/2.07  
% 11.34/2.07  ------ AIG Options
% 11.34/2.07  
% 11.34/2.07  --aig_mode                              false
% 11.34/2.07  
% 11.34/2.07  ------ Instantiation Options
% 11.34/2.07  
% 11.34/2.07  --instantiation_flag                    true
% 11.34/2.07  --inst_sos_flag                         true
% 11.34/2.07  --inst_sos_phase                        true
% 11.34/2.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.34/2.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.34/2.07  --inst_lit_sel_side                     none
% 11.34/2.07  --inst_solver_per_active                1400
% 11.34/2.07  --inst_solver_calls_frac                1.
% 11.34/2.07  --inst_passive_queue_type               priority_queues
% 11.34/2.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.34/2.07  --inst_passive_queues_freq              [25;2]
% 11.34/2.07  --inst_dismatching                      true
% 11.34/2.07  --inst_eager_unprocessed_to_passive     true
% 11.34/2.07  --inst_prop_sim_given                   true
% 11.34/2.07  --inst_prop_sim_new                     false
% 11.34/2.07  --inst_subs_new                         false
% 11.34/2.07  --inst_eq_res_simp                      false
% 11.34/2.07  --inst_subs_given                       false
% 11.34/2.07  --inst_orphan_elimination               true
% 11.34/2.07  --inst_learning_loop_flag               true
% 11.34/2.07  --inst_learning_start                   3000
% 11.34/2.07  --inst_learning_factor                  2
% 11.34/2.07  --inst_start_prop_sim_after_learn       3
% 11.34/2.07  --inst_sel_renew                        solver
% 11.34/2.07  --inst_lit_activity_flag                true
% 11.34/2.07  --inst_restr_to_given                   false
% 11.34/2.07  --inst_activity_threshold               500
% 11.34/2.07  --inst_out_proof                        true
% 11.34/2.07  
% 11.34/2.07  ------ Resolution Options
% 11.34/2.07  
% 11.34/2.07  --resolution_flag                       false
% 11.34/2.07  --res_lit_sel                           adaptive
% 11.34/2.07  --res_lit_sel_side                      none
% 11.34/2.07  --res_ordering                          kbo
% 11.34/2.07  --res_to_prop_solver                    active
% 11.34/2.07  --res_prop_simpl_new                    false
% 11.34/2.07  --res_prop_simpl_given                  true
% 11.34/2.07  --res_passive_queue_type                priority_queues
% 11.34/2.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.34/2.07  --res_passive_queues_freq               [15;5]
% 11.34/2.07  --res_forward_subs                      full
% 11.34/2.07  --res_backward_subs                     full
% 11.34/2.07  --res_forward_subs_resolution           true
% 11.34/2.07  --res_backward_subs_resolution          true
% 11.34/2.07  --res_orphan_elimination                true
% 11.34/2.07  --res_time_limit                        2.
% 11.34/2.07  --res_out_proof                         true
% 11.34/2.07  
% 11.34/2.07  ------ Superposition Options
% 11.34/2.07  
% 11.34/2.07  --superposition_flag                    true
% 11.34/2.07  --sup_passive_queue_type                priority_queues
% 11.34/2.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.34/2.07  --sup_passive_queues_freq               [8;1;4]
% 11.34/2.07  --demod_completeness_check              fast
% 11.34/2.07  --demod_use_ground                      true
% 11.34/2.07  --sup_to_prop_solver                    passive
% 11.34/2.07  --sup_prop_simpl_new                    true
% 11.34/2.07  --sup_prop_simpl_given                  true
% 11.34/2.07  --sup_fun_splitting                     true
% 11.34/2.07  --sup_smt_interval                      50000
% 11.34/2.07  
% 11.34/2.07  ------ Superposition Simplification Setup
% 11.34/2.07  
% 11.34/2.07  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.34/2.07  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.34/2.07  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.34/2.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.34/2.07  --sup_full_triv                         [TrivRules;PropSubs]
% 11.34/2.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.34/2.07  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.34/2.07  --sup_immed_triv                        [TrivRules]
% 11.34/2.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.34/2.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.34/2.07  --sup_immed_bw_main                     []
% 11.34/2.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.34/2.07  --sup_input_triv                        [Unflattening;TrivRules]
% 11.34/2.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.34/2.07  --sup_input_bw                          []
% 11.34/2.07  
% 11.34/2.07  ------ Combination Options
% 11.34/2.07  
% 11.34/2.07  --comb_res_mult                         3
% 11.34/2.07  --comb_sup_mult                         2
% 11.34/2.07  --comb_inst_mult                        10
% 11.34/2.07  
% 11.34/2.07  ------ Debug Options
% 11.34/2.07  
% 11.34/2.07  --dbg_backtrace                         false
% 11.34/2.07  --dbg_dump_prop_clauses                 false
% 11.34/2.07  --dbg_dump_prop_clauses_file            -
% 11.34/2.07  --dbg_out_stat                          false
% 11.34/2.07  
% 11.34/2.07  
% 11.34/2.07  
% 11.34/2.07  
% 11.34/2.07  ------ Proving...
% 11.34/2.07  
% 11.34/2.07  
% 11.34/2.07  % SZS status Theorem for theBenchmark.p
% 11.34/2.07  
% 11.34/2.07  % SZS output start CNFRefutation for theBenchmark.p
% 11.34/2.07  
% 11.34/2.07  fof(f11,conjecture,(
% 11.34/2.07    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 11.34/2.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.34/2.07  
% 11.34/2.07  fof(f12,negated_conjecture,(
% 11.34/2.07    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 11.34/2.07    inference(negated_conjecture,[],[f11])).
% 11.34/2.07  
% 11.34/2.07  fof(f24,plain,(
% 11.34/2.07    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.34/2.07    inference(ennf_transformation,[],[f12])).
% 11.34/2.07  
% 11.34/2.07  fof(f25,plain,(
% 11.34/2.07    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.34/2.07    inference(flattening,[],[f24])).
% 11.34/2.07  
% 11.34/2.07  fof(f28,plain,(
% 11.34/2.07    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1))) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.34/2.07    introduced(choice_axiom,[])).
% 11.34/2.07  
% 11.34/2.07  fof(f27,plain,(
% 11.34/2.07    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 11.34/2.07    introduced(choice_axiom,[])).
% 11.34/2.07  
% 11.34/2.07  fof(f29,plain,(
% 11.34/2.07    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 11.34/2.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28,f27])).
% 11.34/2.07  
% 11.34/2.07  fof(f42,plain,(
% 11.34/2.07    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.34/2.07    inference(cnf_transformation,[],[f29])).
% 11.34/2.07  
% 11.34/2.07  fof(f7,axiom,(
% 11.34/2.07    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.34/2.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.34/2.07  
% 11.34/2.07  fof(f18,plain,(
% 11.34/2.07    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.34/2.07    inference(ennf_transformation,[],[f7])).
% 11.34/2.07  
% 11.34/2.07  fof(f19,plain,(
% 11.34/2.07    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.34/2.07    inference(flattening,[],[f18])).
% 11.34/2.07  
% 11.34/2.07  fof(f37,plain,(
% 11.34/2.07    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.34/2.07    inference(cnf_transformation,[],[f19])).
% 11.34/2.07  
% 11.34/2.07  fof(f41,plain,(
% 11.34/2.07    l1_pre_topc(sK0)),
% 11.34/2.07    inference(cnf_transformation,[],[f29])).
% 11.34/2.07  
% 11.34/2.07  fof(f8,axiom,(
% 11.34/2.07    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.34/2.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.34/2.07  
% 11.34/2.07  fof(f20,plain,(
% 11.34/2.07    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.34/2.07    inference(ennf_transformation,[],[f8])).
% 11.34/2.07  
% 11.34/2.07  fof(f21,plain,(
% 11.34/2.07    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.34/2.07    inference(flattening,[],[f20])).
% 11.34/2.07  
% 11.34/2.07  fof(f38,plain,(
% 11.34/2.07    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.34/2.07    inference(cnf_transformation,[],[f21])).
% 11.34/2.07  
% 11.34/2.07  fof(f5,axiom,(
% 11.34/2.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.34/2.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.34/2.07  
% 11.34/2.07  fof(f15,plain,(
% 11.34/2.07    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.34/2.07    inference(ennf_transformation,[],[f5])).
% 11.34/2.07  
% 11.34/2.07  fof(f16,plain,(
% 11.34/2.07    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.34/2.07    inference(flattening,[],[f15])).
% 11.34/2.07  
% 11.34/2.07  fof(f34,plain,(
% 11.34/2.07    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.34/2.07    inference(cnf_transformation,[],[f16])).
% 11.34/2.07  
% 11.34/2.07  fof(f4,axiom,(
% 11.34/2.07    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.34/2.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.34/2.07  
% 11.34/2.07  fof(f33,plain,(
% 11.34/2.07    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.34/2.07    inference(cnf_transformation,[],[f4])).
% 11.34/2.07  
% 11.34/2.07  fof(f46,plain,(
% 11.34/2.07    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.34/2.07    inference(definition_unfolding,[],[f34,f33])).
% 11.34/2.07  
% 11.34/2.07  fof(f9,axiom,(
% 11.34/2.07    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 11.34/2.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.34/2.07  
% 11.34/2.07  fof(f22,plain,(
% 11.34/2.07    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.34/2.07    inference(ennf_transformation,[],[f9])).
% 11.34/2.07  
% 11.34/2.07  fof(f39,plain,(
% 11.34/2.07    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.34/2.07    inference(cnf_transformation,[],[f22])).
% 11.34/2.07  
% 11.34/2.07  fof(f6,axiom,(
% 11.34/2.07    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 11.34/2.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.34/2.07  
% 11.34/2.07  fof(f17,plain,(
% 11.34/2.07    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.34/2.07    inference(ennf_transformation,[],[f6])).
% 11.34/2.07  
% 11.34/2.07  fof(f26,plain,(
% 11.34/2.07    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.34/2.07    inference(nnf_transformation,[],[f17])).
% 11.34/2.07  
% 11.34/2.07  fof(f35,plain,(
% 11.34/2.07    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.34/2.07    inference(cnf_transformation,[],[f26])).
% 11.34/2.07  
% 11.34/2.07  fof(f43,plain,(
% 11.34/2.07    v5_tops_1(sK1,sK0)),
% 11.34/2.07    inference(cnf_transformation,[],[f29])).
% 11.34/2.07  
% 11.34/2.07  fof(f3,axiom,(
% 11.34/2.07    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 11.34/2.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.34/2.07  
% 11.34/2.07  fof(f32,plain,(
% 11.34/2.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 11.34/2.07    inference(cnf_transformation,[],[f3])).
% 11.34/2.07  
% 11.34/2.07  fof(f2,axiom,(
% 11.34/2.07    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.34/2.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.34/2.07  
% 11.34/2.07  fof(f31,plain,(
% 11.34/2.07    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.34/2.07    inference(cnf_transformation,[],[f2])).
% 11.34/2.07  
% 11.34/2.07  fof(f45,plain,(
% 11.34/2.07    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 11.34/2.07    inference(definition_unfolding,[],[f31,f33])).
% 11.34/2.07  
% 11.34/2.07  fof(f1,axiom,(
% 11.34/2.07    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.34/2.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.34/2.07  
% 11.34/2.07  fof(f13,plain,(
% 11.34/2.07    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.34/2.07    inference(ennf_transformation,[],[f1])).
% 11.34/2.07  
% 11.34/2.07  fof(f14,plain,(
% 11.34/2.07    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.34/2.07    inference(flattening,[],[f13])).
% 11.34/2.07  
% 11.34/2.07  fof(f30,plain,(
% 11.34/2.07    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.34/2.07    inference(cnf_transformation,[],[f14])).
% 11.34/2.07  
% 11.34/2.07  fof(f10,axiom,(
% 11.34/2.07    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 11.34/2.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.34/2.07  
% 11.34/2.07  fof(f23,plain,(
% 11.34/2.07    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.34/2.07    inference(ennf_transformation,[],[f10])).
% 11.34/2.07  
% 11.34/2.07  fof(f40,plain,(
% 11.34/2.07    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.34/2.07    inference(cnf_transformation,[],[f23])).
% 11.34/2.07  
% 11.34/2.07  fof(f44,plain,(
% 11.34/2.07    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 11.34/2.07    inference(cnf_transformation,[],[f29])).
% 11.34/2.07  
% 11.34/2.07  cnf(c_12,negated_conjecture,
% 11.34/2.07      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.34/2.07      inference(cnf_transformation,[],[f42]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_294,negated_conjecture,
% 11.34/2.07      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.34/2.07      inference(subtyping,[status(esa)],[c_12]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_494,plain,
% 11.34/2.07      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.34/2.07      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_6,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | ~ l1_pre_topc(X1) ),
% 11.34/2.07      inference(cnf_transformation,[],[f37]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_13,negated_conjecture,
% 11.34/2.07      ( l1_pre_topc(sK0) ),
% 11.34/2.07      inference(cnf_transformation,[],[f41]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_195,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | sK0 != X1 ),
% 11.34/2.07      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_196,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.34/2.07      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.34/2.07      inference(unflattening,[status(thm)],[c_195]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_289,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.34/2.07      | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.34/2.07      inference(subtyping,[status(esa)],[c_196]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_498,plain,
% 11.34/2.07      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.34/2.07      | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.34/2.07      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_7,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | ~ l1_pre_topc(X1) ),
% 11.34/2.07      inference(cnf_transformation,[],[f38]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_183,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | sK0 != X1 ),
% 11.34/2.07      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_184,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.34/2.07      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.34/2.07      inference(unflattening,[status(thm)],[c_183]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_290,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.34/2.07      | m1_subset_1(k2_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.34/2.07      inference(subtyping,[status(esa)],[c_184]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_497,plain,
% 11.34/2.07      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.34/2.07      | m1_subset_1(k2_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.34/2.07      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_3,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.34/2.07      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.34/2.07      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 11.34/2.07      inference(cnf_transformation,[],[f46]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_296,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X0_44))
% 11.34/2.07      | ~ m1_subset_1(X1_42,k1_zfmisc_1(X0_44))
% 11.34/2.07      | k4_subset_1(X0_44,X1_42,X0_42) = k3_tarski(k2_tarski(X1_42,X0_42)) ),
% 11.34/2.07      inference(subtyping,[status(esa)],[c_3]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_492,plain,
% 11.34/2.07      ( k4_subset_1(X0_44,X0_42,X1_42) = k3_tarski(k2_tarski(X0_42,X1_42))
% 11.34/2.07      | m1_subset_1(X0_42,k1_zfmisc_1(X0_44)) != iProver_top
% 11.34/2.07      | m1_subset_1(X1_42,k1_zfmisc_1(X0_44)) != iProver_top ),
% 11.34/2.07      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_981,plain,
% 11.34/2.07      ( k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42)) = k3_tarski(k2_tarski(X0_42,k2_tops_1(sK0,X1_42)))
% 11.34/2.07      | m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.34/2.07      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.34/2.07      inference(superposition,[status(thm)],[c_497,c_492]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_3290,plain,
% 11.34/2.07      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_42),k2_tops_1(sK0,X1_42)) = k3_tarski(k2_tarski(k1_tops_1(sK0,X0_42),k2_tops_1(sK0,X1_42)))
% 11.34/2.07      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.34/2.07      | m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.34/2.07      inference(superposition,[status(thm)],[c_498,c_981]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_36465,plain,
% 11.34/2.07      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_42)) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_42)))
% 11.34/2.07      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.34/2.07      inference(superposition,[status(thm)],[c_494,c_3290]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_37119,plain,
% 11.34/2.07      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_42))) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_42))))
% 11.34/2.07      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.34/2.07      inference(superposition,[status(thm)],[c_498,c_36465]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_37313,plain,
% 11.34/2.07      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) ),
% 11.34/2.07      inference(superposition,[status(thm)],[c_494,c_37119]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_8,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | ~ l1_pre_topc(X1)
% 11.34/2.07      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.34/2.07      inference(cnf_transformation,[],[f39]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_171,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 11.34/2.07      | sK0 != X1 ),
% 11.34/2.07      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_172,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.34/2.07      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 11.34/2.07      inference(unflattening,[status(thm)],[c_171]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_291,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.34/2.07      | k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X0_42)) = k2_pre_topc(sK0,X0_42) ),
% 11.34/2.07      inference(subtyping,[status(esa)],[c_172]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_496,plain,
% 11.34/2.07      ( k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X0_42)) = k2_pre_topc(sK0,X0_42)
% 11.34/2.07      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.34/2.07      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_785,plain,
% 11.34/2.07      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_42),k2_tops_1(sK0,k1_tops_1(sK0,X0_42))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))
% 11.34/2.07      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.34/2.07      inference(superposition,[status(thm)],[c_498,c_496]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_1445,plain,
% 11.34/2.07      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 11.34/2.07      inference(superposition,[status(thm)],[c_494,c_785]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_5,plain,
% 11.34/2.07      ( ~ v5_tops_1(X0,X1)
% 11.34/2.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | ~ l1_pre_topc(X1)
% 11.34/2.07      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 11.34/2.07      inference(cnf_transformation,[],[f35]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_11,negated_conjecture,
% 11.34/2.07      ( v5_tops_1(sK1,sK0) ),
% 11.34/2.07      inference(cnf_transformation,[],[f43]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_150,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | ~ l1_pre_topc(X1)
% 11.34/2.07      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
% 11.34/2.07      | sK1 != X0
% 11.34/2.07      | sK0 != X1 ),
% 11.34/2.07      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_151,plain,
% 11.34/2.07      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.34/2.07      | ~ l1_pre_topc(sK0)
% 11.34/2.07      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 11.34/2.07      inference(unflattening,[status(thm)],[c_150]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_153,plain,
% 11.34/2.07      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 11.34/2.07      inference(global_propositional_subsumption,
% 11.34/2.07                [status(thm)],
% 11.34/2.07                [c_151,c_13,c_12]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_293,plain,
% 11.34/2.07      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 11.34/2.07      inference(subtyping,[status(esa)],[c_153]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_1448,plain,
% 11.34/2.07      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1 ),
% 11.34/2.07      inference(light_normalisation,[status(thm)],[c_1445,c_293]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_37316,plain,
% 11.34/2.07      ( k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = sK1 ),
% 11.34/2.07      inference(light_normalisation,[status(thm)],[c_37313,c_1448]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_2,plain,
% 11.34/2.07      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 11.34/2.07      inference(cnf_transformation,[],[f32]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_297,plain,
% 11.34/2.07      ( k2_tarski(X0_42,X1_42) = k2_tarski(X1_42,X0_42) ),
% 11.34/2.07      inference(subtyping,[status(esa)],[c_2]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_1,plain,
% 11.34/2.07      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 11.34/2.07      inference(cnf_transformation,[],[f45]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_298,plain,
% 11.34/2.07      ( r1_tarski(X0_42,k3_tarski(k2_tarski(X0_42,X1_42))) ),
% 11.34/2.07      inference(subtyping,[status(esa)],[c_1]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_491,plain,
% 11.34/2.07      ( r1_tarski(X0_42,k3_tarski(k2_tarski(X0_42,X1_42))) = iProver_top ),
% 11.34/2.07      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_921,plain,
% 11.34/2.07      ( r1_tarski(X0_42,k3_tarski(k2_tarski(X1_42,X0_42))) = iProver_top ),
% 11.34/2.07      inference(superposition,[status(thm)],[c_297,c_491]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_37576,plain,
% 11.34/2.07      ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK1) = iProver_top ),
% 11.34/2.07      inference(superposition,[status(thm)],[c_37316,c_921]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_0,plain,
% 11.34/2.07      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 11.34/2.07      inference(cnf_transformation,[],[f30]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_299,plain,
% 11.34/2.07      ( ~ r1_tarski(X0_42,X1_42)
% 11.34/2.07      | ~ r1_tarski(X2_42,X0_42)
% 11.34/2.07      | r1_tarski(X2_42,X1_42) ),
% 11.34/2.07      inference(subtyping,[status(esa)],[c_0]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_528,plain,
% 11.34/2.07      ( ~ r1_tarski(X0_42,X1_42)
% 11.34/2.07      | ~ r1_tarski(k2_tops_1(sK0,sK1),X0_42)
% 11.34/2.07      | r1_tarski(k2_tops_1(sK0,sK1),X1_42) ),
% 11.34/2.07      inference(instantiation,[status(thm)],[c_299]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_620,plain,
% 11.34/2.07      ( ~ r1_tarski(k2_tops_1(sK0,X0_42),X1_42)
% 11.34/2.07      | r1_tarski(k2_tops_1(sK0,sK1),X1_42)
% 11.34/2.07      | ~ r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,X0_42)) ),
% 11.34/2.07      inference(instantiation,[status(thm)],[c_528]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_3894,plain,
% 11.34/2.07      ( ~ r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),X0_42)
% 11.34/2.07      | r1_tarski(k2_tops_1(sK0,sK1),X0_42)
% 11.34/2.07      | ~ r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
% 11.34/2.07      inference(instantiation,[status(thm)],[c_620]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_3898,plain,
% 11.34/2.07      ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),X0_42) != iProver_top
% 11.34/2.07      | r1_tarski(k2_tops_1(sK0,sK1),X0_42) = iProver_top
% 11.34/2.07      | r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 11.34/2.07      inference(predicate_to_equality,[status(thm)],[c_3894]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_3900,plain,
% 11.34/2.07      ( r1_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK1) != iProver_top
% 11.34/2.07      | r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 11.34/2.07      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 11.34/2.07      inference(instantiation,[status(thm)],[c_3898]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_9,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
% 11.34/2.07      | ~ l1_pre_topc(X1) ),
% 11.34/2.07      inference(cnf_transformation,[],[f40]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_159,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.34/2.07      | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
% 11.34/2.07      | sK0 != X1 ),
% 11.34/2.07      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_160,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.34/2.07      | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k2_tops_1(sK0,X0)) ),
% 11.34/2.07      inference(unflattening,[status(thm)],[c_159]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_292,plain,
% 11.34/2.07      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.34/2.07      | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0_42)),k2_tops_1(sK0,X0_42)) ),
% 11.34/2.07      inference(subtyping,[status(esa)],[c_160]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_495,plain,
% 11.34/2.07      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.34/2.07      | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0_42)),k2_tops_1(sK0,X0_42)) = iProver_top ),
% 11.34/2.07      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_698,plain,
% 11.34/2.07      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.34/2.07      | r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 11.34/2.07      inference(superposition,[status(thm)],[c_293,c_495]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_10,negated_conjecture,
% 11.34/2.07      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 11.34/2.07      inference(cnf_transformation,[],[f44]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_295,negated_conjecture,
% 11.34/2.07      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 11.34/2.07      inference(subtyping,[status(esa)],[c_10]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_493,plain,
% 11.34/2.07      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 11.34/2.07      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_499,plain,
% 11.34/2.07      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 11.34/2.07      inference(light_normalisation,[status(thm)],[c_493,c_293]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_341,plain,
% 11.34/2.07      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.34/2.07      | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.34/2.07      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_343,plain,
% 11.34/2.07      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.34/2.07      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.34/2.07      inference(instantiation,[status(thm)],[c_341]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(c_15,plain,
% 11.34/2.07      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.34/2.07      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.34/2.07  
% 11.34/2.07  cnf(contradiction,plain,
% 11.34/2.07      ( $false ),
% 11.34/2.07      inference(minisat,
% 11.34/2.07                [status(thm)],
% 11.34/2.07                [c_37576,c_3900,c_698,c_499,c_343,c_15]) ).
% 11.34/2.07  
% 11.34/2.07  
% 11.34/2.07  % SZS output end CNFRefutation for theBenchmark.p
% 11.34/2.07  
% 11.34/2.07  ------                               Statistics
% 11.34/2.07  
% 11.34/2.07  ------ General
% 11.34/2.07  
% 11.34/2.07  abstr_ref_over_cycles:                  0
% 11.34/2.07  abstr_ref_under_cycles:                 0
% 11.34/2.07  gc_basic_clause_elim:                   0
% 11.34/2.07  forced_gc_time:                         0
% 11.34/2.07  parsing_time:                           0.008
% 11.34/2.07  unif_index_cands_time:                  0.
% 11.34/2.07  unif_index_add_time:                    0.
% 11.34/2.07  orderings_time:                         0.
% 11.34/2.07  out_proof_time:                         0.01
% 11.34/2.07  total_time:                             1.198
% 11.34/2.07  num_of_symbols:                         47
% 11.34/2.07  num_of_terms:                           35085
% 11.34/2.07  
% 11.34/2.07  ------ Preprocessing
% 11.34/2.07  
% 11.34/2.07  num_of_splits:                          0
% 11.34/2.07  num_of_split_atoms:                     0
% 11.34/2.07  num_of_reused_defs:                     0
% 11.34/2.07  num_eq_ax_congr_red:                    16
% 11.34/2.07  num_of_sem_filtered_clauses:            1
% 11.34/2.07  num_of_subtypes:                        5
% 11.34/2.07  monotx_restored_types:                  0
% 11.34/2.07  sat_num_of_epr_types:                   0
% 11.34/2.07  sat_num_of_non_cyclic_types:            0
% 11.34/2.07  sat_guarded_non_collapsed_types:        0
% 11.34/2.07  num_pure_diseq_elim:                    0
% 11.34/2.07  simp_replaced_by:                       0
% 11.34/2.07  res_preprocessed:                       70
% 11.34/2.07  prep_upred:                             0
% 11.34/2.07  prep_unflattend:                        6
% 11.34/2.07  smt_new_axioms:                         0
% 11.34/2.07  pred_elim_cands:                        2
% 11.34/2.07  pred_elim:                              2
% 11.34/2.07  pred_elim_cl:                           3
% 11.34/2.07  pred_elim_cycles:                       4
% 11.34/2.07  merged_defs:                            0
% 11.34/2.07  merged_defs_ncl:                        0
% 11.34/2.07  bin_hyper_res:                          0
% 11.34/2.07  prep_cycles:                            4
% 11.34/2.07  pred_elim_time:                         0.002
% 11.34/2.07  splitting_time:                         0.
% 11.34/2.07  sem_filter_time:                        0.
% 11.34/2.07  monotx_time:                            0.
% 11.34/2.07  subtype_inf_time:                       0.
% 11.34/2.07  
% 11.34/2.07  ------ Problem properties
% 11.34/2.07  
% 11.34/2.07  clauses:                                11
% 11.34/2.07  conjectures:                            2
% 11.34/2.07  epr:                                    1
% 11.34/2.07  horn:                                   11
% 11.34/2.07  ground:                                 3
% 11.34/2.07  unary:                                  5
% 11.34/2.07  binary:                                 4
% 11.34/2.07  lits:                                   19
% 11.34/2.07  lits_eq:                                4
% 11.34/2.07  fd_pure:                                0
% 11.34/2.07  fd_pseudo:                              0
% 11.34/2.07  fd_cond:                                0
% 11.34/2.07  fd_pseudo_cond:                         0
% 11.34/2.07  ac_symbols:                             0
% 11.34/2.07  
% 11.34/2.07  ------ Propositional Solver
% 11.34/2.07  
% 11.34/2.07  prop_solver_calls:                      32
% 11.34/2.07  prop_fast_solver_calls:                 805
% 11.34/2.07  smt_solver_calls:                       0
% 11.34/2.07  smt_fast_solver_calls:                  0
% 11.34/2.07  prop_num_of_clauses:                    12545
% 11.34/2.07  prop_preprocess_simplified:             28290
% 11.34/2.07  prop_fo_subsumed:                       8
% 11.34/2.07  prop_solver_time:                       0.
% 11.34/2.07  smt_solver_time:                        0.
% 11.34/2.07  smt_fast_solver_time:                   0.
% 11.34/2.07  prop_fast_solver_time:                  0.
% 11.34/2.07  prop_unsat_core_time:                   0.001
% 11.34/2.07  
% 11.34/2.07  ------ QBF
% 11.34/2.07  
% 11.34/2.07  qbf_q_res:                              0
% 11.34/2.07  qbf_num_tautologies:                    0
% 11.34/2.07  qbf_prep_cycles:                        0
% 11.34/2.07  
% 11.34/2.07  ------ BMC1
% 11.34/2.07  
% 11.34/2.07  bmc1_current_bound:                     -1
% 11.34/2.07  bmc1_last_solved_bound:                 -1
% 11.34/2.07  bmc1_unsat_core_size:                   -1
% 11.34/2.07  bmc1_unsat_core_parents_size:           -1
% 11.34/2.07  bmc1_merge_next_fun:                    0
% 11.34/2.07  bmc1_unsat_core_clauses_time:           0.
% 11.34/2.07  
% 11.34/2.07  ------ Instantiation
% 11.34/2.07  
% 11.34/2.07  inst_num_of_clauses:                    3744
% 11.34/2.07  inst_num_in_passive:                    1206
% 11.34/2.07  inst_num_in_active:                     1342
% 11.34/2.07  inst_num_in_unprocessed:                1197
% 11.34/2.07  inst_num_of_loops:                      1390
% 11.34/2.07  inst_num_of_learning_restarts:          0
% 11.34/2.07  inst_num_moves_active_passive:          43
% 11.34/2.07  inst_lit_activity:                      0
% 11.34/2.07  inst_lit_activity_moves:                0
% 11.34/2.07  inst_num_tautologies:                   0
% 11.34/2.07  inst_num_prop_implied:                  0
% 11.34/2.07  inst_num_existing_simplified:           0
% 11.34/2.07  inst_num_eq_res_simplified:             0
% 11.34/2.07  inst_num_child_elim:                    0
% 11.34/2.07  inst_num_of_dismatching_blockings:      7008
% 11.34/2.07  inst_num_of_non_proper_insts:           6456
% 11.34/2.07  inst_num_of_duplicates:                 0
% 11.34/2.07  inst_inst_num_from_inst_to_res:         0
% 11.34/2.07  inst_dismatching_checking_time:         0.
% 11.34/2.07  
% 11.34/2.07  ------ Resolution
% 11.34/2.07  
% 11.34/2.07  res_num_of_clauses:                     0
% 11.34/2.07  res_num_in_passive:                     0
% 11.34/2.07  res_num_in_active:                      0
% 11.34/2.07  res_num_of_loops:                       74
% 11.34/2.07  res_forward_subset_subsumed:            233
% 11.34/2.07  res_backward_subset_subsumed:           6
% 11.34/2.07  res_forward_subsumed:                   0
% 11.34/2.07  res_backward_subsumed:                  0
% 11.34/2.07  res_forward_subsumption_resolution:     0
% 11.34/2.07  res_backward_subsumption_resolution:    0
% 11.34/2.07  res_clause_to_clause_subsumption:       25278
% 11.34/2.07  res_orphan_elimination:                 0
% 11.34/2.07  res_tautology_del:                      780
% 11.34/2.07  res_num_eq_res_simplified:              0
% 11.34/2.07  res_num_sel_changes:                    0
% 11.34/2.07  res_moves_from_active_to_pass:          0
% 11.34/2.07  
% 11.34/2.07  ------ Superposition
% 11.34/2.07  
% 11.34/2.07  sup_time_total:                         0.
% 11.34/2.07  sup_time_generating:                    0.
% 11.34/2.07  sup_time_sim_full:                      0.
% 11.34/2.07  sup_time_sim_immed:                     0.
% 11.34/2.07  
% 11.34/2.07  sup_num_of_clauses:                     1028
% 11.34/2.07  sup_num_in_active:                      277
% 11.34/2.07  sup_num_in_passive:                     751
% 11.34/2.07  sup_num_of_loops:                       276
% 11.34/2.07  sup_fw_superposition:                   1188
% 11.34/2.07  sup_bw_superposition:                   693
% 11.34/2.07  sup_immediate_simplified:               43
% 11.34/2.07  sup_given_eliminated:                   0
% 11.34/2.07  comparisons_done:                       0
% 11.34/2.07  comparisons_avoided:                    0
% 11.34/2.07  
% 11.34/2.07  ------ Simplifications
% 11.34/2.07  
% 11.34/2.07  
% 11.34/2.07  sim_fw_subset_subsumed:                 39
% 11.34/2.07  sim_bw_subset_subsumed:                 0
% 11.34/2.07  sim_fw_subsumed:                        0
% 11.34/2.07  sim_bw_subsumed:                        3
% 11.34/2.07  sim_fw_subsumption_res:                 0
% 11.34/2.07  sim_bw_subsumption_res:                 0
% 11.34/2.07  sim_tautology_del:                      0
% 11.34/2.07  sim_eq_tautology_del:                   0
% 11.34/2.07  sim_eq_res_simp:                        0
% 11.34/2.07  sim_fw_demodulated:                     0
% 11.34/2.07  sim_bw_demodulated:                     0
% 11.34/2.07  sim_light_normalised:                   8
% 11.34/2.07  sim_joinable_taut:                      0
% 11.34/2.07  sim_joinable_simp:                      0
% 11.34/2.07  sim_ac_normalised:                      0
% 11.34/2.07  sim_smt_subsumption:                    0
% 11.34/2.07  
%------------------------------------------------------------------------------
