%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:43 EST 2020

% Result     : Theorem 7.83s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 453 expanded)
%              Number of clauses        :   76 ( 155 expanded)
%              Number of leaves         :   13 ( 103 expanded)
%              Depth                    :   22
%              Number of atoms          :  316 (1546 expanded)
%              Number of equality atoms :  139 ( 223 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1)))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
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

fof(f31,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f30,f29])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_131,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_413,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_131])).

cnf(c_5,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_138,plain,
    ( ~ v5_tops_1(X0_43,X0_42)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42)
    | k2_pre_topc(X0_42,k1_tops_1(X0_42,X0_43)) = X0_43 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_406,plain,
    ( k2_pre_topc(X0_42,k1_tops_1(X0_42,X0_43)) = X0_43
    | v5_tops_1(X0_43,X0_42) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_138])).

cnf(c_2336,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
    | v5_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_406])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_11,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_179,plain,
    ( ~ v5_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_2529,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2336,c_13,c_12,c_11,c_179])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_134,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | r1_tarski(k2_tops_1(X0_42,k2_pre_topc(X0_42,X0_43)),k2_tops_1(X0_42,X0_43))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_410,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | r1_tarski(k2_tops_1(X0_42,k2_pre_topc(X0_42,X0_43)),k2_tops_1(X0_42,X0_43)) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_134])).

cnf(c_2534,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2529,c_410])).

cnf(c_14,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_137,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | m1_subset_1(k1_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_181,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(k1_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137])).

cnf(c_183,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_2734,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2534,c_14,c_15,c_183])).

cnf(c_407,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(k1_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_136,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_408,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_136])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_141,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
    | k4_subset_1(X0_45,X0_43,X1_43) = k4_subset_1(X0_45,X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_403,plain,
    ( k4_subset_1(X0_45,X0_43,X1_43) = k4_subset_1(X0_45,X1_43,X0_43)
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_141])).

cnf(c_944,plain,
    ( k4_subset_1(u1_struct_0(X0_42),X0_43,k1_tops_1(X0_42,X1_43)) = k4_subset_1(u1_struct_0(X0_42),k1_tops_1(X0_42,X1_43),X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_407,c_403])).

cnf(c_5057,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0_43) = k4_subset_1(u1_struct_0(sK0),X0_43,k1_tops_1(sK0,sK1))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_944])).

cnf(c_5849,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0_43) = k4_subset_1(u1_struct_0(sK0),X0_43,k1_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5057,c_14])).

cnf(c_5850,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0_43) = k4_subset_1(u1_struct_0(sK0),X0_43,k1_tops_1(sK0,sK1))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5849])).

cnf(c_5858,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_43))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_408,c_5850])).

cnf(c_5879,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5858,c_14])).

cnf(c_5880,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_43))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5879])).

cnf(c_5889,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_43))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_407,c_5880])).

cnf(c_23090,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_43))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5889,c_14])).

cnf(c_23091,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_43))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_23090])).

cnf(c_23098,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_413,c_23091])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_135,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42)
    | k4_subset_1(u1_struct_0(X0_42),X0_43,k2_tops_1(X0_42,X0_43)) = k2_pre_topc(X0_42,X0_43) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_409,plain,
    ( k4_subset_1(u1_struct_0(X0_42),X0_43,k2_tops_1(X0_42,X0_43)) = k2_pre_topc(X0_42,X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_135])).

cnf(c_1188,plain,
    ( k4_subset_1(u1_struct_0(X0_42),k1_tops_1(X0_42,X0_43),k2_tops_1(X0_42,k1_tops_1(X0_42,X0_43))) = k2_pre_topc(X0_42,k1_tops_1(X0_42,X0_43))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_407,c_409])).

cnf(c_7515,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_1188])).

cnf(c_7532,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7515,c_2529])).

cnf(c_7543,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7532,c_14])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_140,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
    | k4_subset_1(X0_45,X1_43,X0_43) = k3_tarski(k2_tarski(X1_43,X0_43)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_404,plain,
    ( k4_subset_1(X0_45,X0_43,X1_43) = k3_tarski(k2_tarski(X0_43,X1_43))
    | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_1047,plain,
    ( k4_subset_1(u1_struct_0(X0_42),X0_43,k1_tops_1(X0_42,X1_43)) = k3_tarski(k2_tarski(X0_43,k1_tops_1(X0_42,X1_43)))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_407,c_404])).

cnf(c_10854,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_43,k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0_43,k1_tops_1(sK0,sK1)))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_1047])).

cnf(c_11642,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),X0_43,k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0_43,k1_tops_1(sK0,sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10854,c_14])).

cnf(c_11643,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_43,k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0_43,k1_tops_1(sK0,sK1)))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11642])).

cnf(c_11651,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_408,c_11643])).

cnf(c_12086,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11651,c_14])).

cnf(c_12087,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12086])).

cnf(c_12096,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1)))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_407,c_12087])).

cnf(c_19649,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12096,c_14])).

cnf(c_19650,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1)))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_19649])).

cnf(c_19657,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_413,c_19650])).

cnf(c_23114,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_23098,c_7543,c_19657])).

cnf(c_1,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_142,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_tarski(X0_43,X1_43))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_402,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_tarski(X0_43,X1_43))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_143,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,X0_43)
    | r1_tarski(X2_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_401,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(X2_43,X0_43) != iProver_top
    | r1_tarski(X2_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_654,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(X0_43,k3_tarski(k2_tarski(X1_43,X2_43))) = iProver_top ),
    inference(superposition,[status(thm)],[c_402,c_401])).

cnf(c_23254,plain,
    ( r1_tarski(X0_43,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(X0_43,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_23114,c_654])).

cnf(c_23882,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2734,c_23254])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_133,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_411,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_133])).

cnf(c_2532,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2529,c_411])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23882,c_2532])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.83/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/1.48  
% 7.83/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.83/1.48  
% 7.83/1.48  ------  iProver source info
% 7.83/1.48  
% 7.83/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.83/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.83/1.48  git: non_committed_changes: false
% 7.83/1.48  git: last_make_outside_of_git: false
% 7.83/1.48  
% 7.83/1.48  ------ 
% 7.83/1.48  ------ Parsing...
% 7.83/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.83/1.48  
% 7.83/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.83/1.48  
% 7.83/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.83/1.48  
% 7.83/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.48  ------ Proving...
% 7.83/1.48  ------ Problem Properties 
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  clauses                                 14
% 7.83/1.48  conjectures                             4
% 7.83/1.48  EPR                                     3
% 7.83/1.48  Horn                                    14
% 7.83/1.48  unary                                   5
% 7.83/1.48  binary                                  0
% 7.83/1.48  lits                                    34
% 7.83/1.48  lits eq                                 5
% 7.83/1.48  fd_pure                                 0
% 7.83/1.48  fd_pseudo                               0
% 7.83/1.48  fd_cond                                 0
% 7.83/1.48  fd_pseudo_cond                          0
% 7.83/1.48  AC symbols                              0
% 7.83/1.48  
% 7.83/1.48  ------ Input Options Time Limit: Unbounded
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  ------ 
% 7.83/1.48  Current options:
% 7.83/1.48  ------ 
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  ------ Proving...
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  % SZS status Theorem for theBenchmark.p
% 7.83/1.48  
% 7.83/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.83/1.48  
% 7.83/1.48  fof(f11,conjecture,(
% 7.83/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f12,negated_conjecture,(
% 7.83/1.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 7.83/1.48    inference(negated_conjecture,[],[f11])).
% 7.83/1.48  
% 7.83/1.48  fof(f26,plain,(
% 7.83/1.48    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.83/1.48    inference(ennf_transformation,[],[f12])).
% 7.83/1.48  
% 7.83/1.48  fof(f27,plain,(
% 7.83/1.48    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.83/1.48    inference(flattening,[],[f26])).
% 7.83/1.48  
% 7.83/1.48  fof(f30,plain,(
% 7.83/1.48    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1))) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f29,plain,(
% 7.83/1.48    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 7.83/1.48    introduced(choice_axiom,[])).
% 7.83/1.48  
% 7.83/1.48  fof(f31,plain,(
% 7.83/1.48    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 7.83/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f30,f29])).
% 7.83/1.48  
% 7.83/1.48  fof(f44,plain,(
% 7.83/1.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.83/1.48    inference(cnf_transformation,[],[f31])).
% 7.83/1.48  
% 7.83/1.48  fof(f6,axiom,(
% 7.83/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f19,plain,(
% 7.83/1.48    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.83/1.48    inference(ennf_transformation,[],[f6])).
% 7.83/1.48  
% 7.83/1.48  fof(f28,plain,(
% 7.83/1.48    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.83/1.48    inference(nnf_transformation,[],[f19])).
% 7.83/1.48  
% 7.83/1.48  fof(f37,plain,(
% 7.83/1.48    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.83/1.48    inference(cnf_transformation,[],[f28])).
% 7.83/1.48  
% 7.83/1.48  fof(f43,plain,(
% 7.83/1.48    l1_pre_topc(sK0)),
% 7.83/1.48    inference(cnf_transformation,[],[f31])).
% 7.83/1.48  
% 7.83/1.48  fof(f45,plain,(
% 7.83/1.48    v5_tops_1(sK1,sK0)),
% 7.83/1.48    inference(cnf_transformation,[],[f31])).
% 7.83/1.48  
% 7.83/1.48  fof(f10,axiom,(
% 7.83/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f25,plain,(
% 7.83/1.48    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.83/1.48    inference(ennf_transformation,[],[f10])).
% 7.83/1.48  
% 7.83/1.48  fof(f42,plain,(
% 7.83/1.48    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.83/1.48    inference(cnf_transformation,[],[f25])).
% 7.83/1.48  
% 7.83/1.48  fof(f7,axiom,(
% 7.83/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f20,plain,(
% 7.83/1.48    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.83/1.48    inference(ennf_transformation,[],[f7])).
% 7.83/1.48  
% 7.83/1.48  fof(f21,plain,(
% 7.83/1.48    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.83/1.48    inference(flattening,[],[f20])).
% 7.83/1.48  
% 7.83/1.48  fof(f39,plain,(
% 7.83/1.48    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.83/1.48    inference(cnf_transformation,[],[f21])).
% 7.83/1.48  
% 7.83/1.48  fof(f8,axiom,(
% 7.83/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f22,plain,(
% 7.83/1.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.83/1.48    inference(ennf_transformation,[],[f8])).
% 7.83/1.48  
% 7.83/1.48  fof(f23,plain,(
% 7.83/1.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.83/1.48    inference(flattening,[],[f22])).
% 7.83/1.48  
% 7.83/1.48  fof(f40,plain,(
% 7.83/1.48    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.83/1.48    inference(cnf_transformation,[],[f23])).
% 7.83/1.48  
% 7.83/1.48  fof(f4,axiom,(
% 7.83/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f15,plain,(
% 7.83/1.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.83/1.48    inference(ennf_transformation,[],[f4])).
% 7.83/1.48  
% 7.83/1.48  fof(f16,plain,(
% 7.83/1.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.83/1.48    inference(flattening,[],[f15])).
% 7.83/1.48  
% 7.83/1.48  fof(f35,plain,(
% 7.83/1.48    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.83/1.48    inference(cnf_transformation,[],[f16])).
% 7.83/1.48  
% 7.83/1.48  fof(f9,axiom,(
% 7.83/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f24,plain,(
% 7.83/1.48    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.83/1.48    inference(ennf_transformation,[],[f9])).
% 7.83/1.48  
% 7.83/1.48  fof(f41,plain,(
% 7.83/1.48    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.83/1.48    inference(cnf_transformation,[],[f24])).
% 7.83/1.48  
% 7.83/1.48  fof(f5,axiom,(
% 7.83/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f17,plain,(
% 7.83/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.83/1.48    inference(ennf_transformation,[],[f5])).
% 7.83/1.48  
% 7.83/1.48  fof(f18,plain,(
% 7.83/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.83/1.48    inference(flattening,[],[f17])).
% 7.83/1.48  
% 7.83/1.48  fof(f36,plain,(
% 7.83/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.83/1.48    inference(cnf_transformation,[],[f18])).
% 7.83/1.48  
% 7.83/1.48  fof(f3,axiom,(
% 7.83/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f34,plain,(
% 7.83/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.83/1.48    inference(cnf_transformation,[],[f3])).
% 7.83/1.48  
% 7.83/1.48  fof(f48,plain,(
% 7.83/1.48    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.83/1.48    inference(definition_unfolding,[],[f36,f34])).
% 7.83/1.48  
% 7.83/1.48  fof(f2,axiom,(
% 7.83/1.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f33,plain,(
% 7.83/1.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.83/1.48    inference(cnf_transformation,[],[f2])).
% 7.83/1.48  
% 7.83/1.48  fof(f47,plain,(
% 7.83/1.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 7.83/1.48    inference(definition_unfolding,[],[f33,f34])).
% 7.83/1.48  
% 7.83/1.48  fof(f1,axiom,(
% 7.83/1.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.83/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.48  
% 7.83/1.48  fof(f13,plain,(
% 7.83/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.83/1.48    inference(ennf_transformation,[],[f1])).
% 7.83/1.48  
% 7.83/1.48  fof(f14,plain,(
% 7.83/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.83/1.48    inference(flattening,[],[f13])).
% 7.83/1.48  
% 7.83/1.48  fof(f32,plain,(
% 7.83/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.83/1.48    inference(cnf_transformation,[],[f14])).
% 7.83/1.48  
% 7.83/1.48  fof(f46,plain,(
% 7.83/1.48    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 7.83/1.48    inference(cnf_transformation,[],[f31])).
% 7.83/1.48  
% 7.83/1.48  cnf(c_12,negated_conjecture,
% 7.83/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.83/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_131,negated_conjecture,
% 7.83/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.83/1.48      inference(subtyping,[status(esa)],[c_12]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_413,plain,
% 7.83/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_131]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_5,plain,
% 7.83/1.48      ( ~ v5_tops_1(X0,X1)
% 7.83/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.83/1.48      | ~ l1_pre_topc(X1)
% 7.83/1.48      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 7.83/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_138,plain,
% 7.83/1.48      ( ~ v5_tops_1(X0_43,X0_42)
% 7.83/1.48      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.83/1.48      | ~ l1_pre_topc(X0_42)
% 7.83/1.48      | k2_pre_topc(X0_42,k1_tops_1(X0_42,X0_43)) = X0_43 ),
% 7.83/1.48      inference(subtyping,[status(esa)],[c_5]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_406,plain,
% 7.83/1.48      ( k2_pre_topc(X0_42,k1_tops_1(X0_42,X0_43)) = X0_43
% 7.83/1.48      | v5_tops_1(X0_43,X0_42) != iProver_top
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.83/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_138]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_2336,plain,
% 7.83/1.48      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
% 7.83/1.48      | v5_tops_1(sK1,sK0) != iProver_top
% 7.83/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_413,c_406]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_13,negated_conjecture,
% 7.83/1.48      ( l1_pre_topc(sK0) ),
% 7.83/1.48      inference(cnf_transformation,[],[f43]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_11,negated_conjecture,
% 7.83/1.48      ( v5_tops_1(sK1,sK0) ),
% 7.83/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_179,plain,
% 7.83/1.48      ( ~ v5_tops_1(sK1,sK0)
% 7.83/1.48      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.83/1.48      | ~ l1_pre_topc(sK0)
% 7.83/1.48      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 7.83/1.48      inference(instantiation,[status(thm)],[c_138]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_2529,plain,
% 7.83/1.48      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 7.83/1.48      inference(global_propositional_subsumption,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_2336,c_13,c_12,c_11,c_179]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_9,plain,
% 7.83/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.83/1.48      | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
% 7.83/1.48      | ~ l1_pre_topc(X1) ),
% 7.83/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_134,plain,
% 7.83/1.48      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.83/1.48      | r1_tarski(k2_tops_1(X0_42,k2_pre_topc(X0_42,X0_43)),k2_tops_1(X0_42,X0_43))
% 7.83/1.48      | ~ l1_pre_topc(X0_42) ),
% 7.83/1.48      inference(subtyping,[status(esa)],[c_9]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_410,plain,
% 7.83/1.48      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.83/1.48      | r1_tarski(k2_tops_1(X0_42,k2_pre_topc(X0_42,X0_43)),k2_tops_1(X0_42,X0_43)) = iProver_top
% 7.83/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_134]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_2534,plain,
% 7.83/1.48      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top
% 7.83/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_2529,c_410]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_14,plain,
% 7.83/1.48      ( l1_pre_topc(sK0) = iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_15,plain,
% 7.83/1.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_6,plain,
% 7.83/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.83/1.48      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.83/1.48      | ~ l1_pre_topc(X1) ),
% 7.83/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_137,plain,
% 7.83/1.48      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.83/1.48      | m1_subset_1(k1_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.83/1.48      | ~ l1_pre_topc(X0_42) ),
% 7.83/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_181,plain,
% 7.83/1.48      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.83/1.48      | m1_subset_1(k1_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
% 7.83/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_137]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_183,plain,
% 7.83/1.48      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.83/1.48      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.83/1.48      inference(instantiation,[status(thm)],[c_181]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_2734,plain,
% 7.83/1.48      ( r1_tarski(k2_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 7.83/1.48      inference(global_propositional_subsumption,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_2534,c_14,c_15,c_183]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_407,plain,
% 7.83/1.48      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.83/1.48      | m1_subset_1(k1_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
% 7.83/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_137]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_7,plain,
% 7.83/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.83/1.48      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.83/1.48      | ~ l1_pre_topc(X1) ),
% 7.83/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_136,plain,
% 7.83/1.48      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.83/1.48      | m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.83/1.48      | ~ l1_pre_topc(X0_42) ),
% 7.83/1.48      inference(subtyping,[status(esa)],[c_7]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_408,plain,
% 7.83/1.48      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.83/1.48      | m1_subset_1(k2_tops_1(X0_42,X0_43),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
% 7.83/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_136]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_2,plain,
% 7.83/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.83/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.83/1.48      | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
% 7.83/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_141,plain,
% 7.83/1.48      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
% 7.83/1.48      | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
% 7.83/1.48      | k4_subset_1(X0_45,X0_43,X1_43) = k4_subset_1(X0_45,X1_43,X0_43) ),
% 7.83/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_403,plain,
% 7.83/1.48      ( k4_subset_1(X0_45,X0_43,X1_43) = k4_subset_1(X0_45,X1_43,X0_43)
% 7.83/1.48      | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_141]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_944,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(X0_42),X0_43,k1_tops_1(X0_42,X1_43)) = k4_subset_1(u1_struct_0(X0_42),k1_tops_1(X0_42,X1_43),X0_43)
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.83/1.48      | m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.83/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_407,c_403]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_5057,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0_43) = k4_subset_1(u1_struct_0(sK0),X0_43,k1_tops_1(sK0,sK1))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_413,c_944]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_5849,plain,
% 7.83/1.48      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0_43) = k4_subset_1(u1_struct_0(sK0),X0_43,k1_tops_1(sK0,sK1)) ),
% 7.83/1.48      inference(global_propositional_subsumption,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_5057,c_14]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_5850,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0_43) = k4_subset_1(u1_struct_0(sK0),X0_43,k1_tops_1(sK0,sK1))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.83/1.48      inference(renaming,[status(thm)],[c_5849]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_5858,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_43))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_408,c_5850]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_5879,plain,
% 7.83/1.48      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_43)) ),
% 7.83/1.48      inference(global_propositional_subsumption,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_5858,c_14]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_5880,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_43))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.83/1.48      inference(renaming,[status(thm)],[c_5879]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_5889,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_43))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_407,c_5880]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_23090,plain,
% 7.83/1.48      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_43))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1)) ),
% 7.83/1.48      inference(global_propositional_subsumption,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_5889,c_14]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_23091,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_43))) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.83/1.48      inference(renaming,[status(thm)],[c_23090]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_23098,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_413,c_23091]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_8,plain,
% 7.83/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.83/1.48      | ~ l1_pre_topc(X1)
% 7.83/1.48      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.83/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_135,plain,
% 7.83/1.48      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.83/1.48      | ~ l1_pre_topc(X0_42)
% 7.83/1.48      | k4_subset_1(u1_struct_0(X0_42),X0_43,k2_tops_1(X0_42,X0_43)) = k2_pre_topc(X0_42,X0_43) ),
% 7.83/1.48      inference(subtyping,[status(esa)],[c_8]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_409,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(X0_42),X0_43,k2_tops_1(X0_42,X0_43)) = k2_pre_topc(X0_42,X0_43)
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.83/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_135]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_1188,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(X0_42),k1_tops_1(X0_42,X0_43),k2_tops_1(X0_42,k1_tops_1(X0_42,X0_43))) = k2_pre_topc(X0_42,k1_tops_1(X0_42,X0_43))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.83/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_407,c_409]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_7515,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 7.83/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_413,c_1188]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_7532,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1
% 7.83/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.83/1.48      inference(light_normalisation,[status(thm)],[c_7515,c_2529]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_7543,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1 ),
% 7.83/1.48      inference(global_propositional_subsumption,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_7532,c_14]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_3,plain,
% 7.83/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.83/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.83/1.48      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 7.83/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_140,plain,
% 7.83/1.48      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
% 7.83/1.48      | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
% 7.83/1.48      | k4_subset_1(X0_45,X1_43,X0_43) = k3_tarski(k2_tarski(X1_43,X0_43)) ),
% 7.83/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_404,plain,
% 7.83/1.48      ( k4_subset_1(X0_45,X0_43,X1_43) = k3_tarski(k2_tarski(X0_43,X1_43))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top
% 7.83/1.48      | m1_subset_1(X1_43,k1_zfmisc_1(X0_45)) != iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_140]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_1047,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(X0_42),X0_43,k1_tops_1(X0_42,X1_43)) = k3_tarski(k2_tarski(X0_43,k1_tops_1(X0_42,X1_43)))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.83/1.48      | m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 7.83/1.48      | l1_pre_topc(X0_42) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_407,c_404]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_10854,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),X0_43,k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0_43,k1_tops_1(sK0,sK1)))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_413,c_1047]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_11642,plain,
% 7.83/1.48      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | k4_subset_1(u1_struct_0(sK0),X0_43,k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0_43,k1_tops_1(sK0,sK1))) ),
% 7.83/1.48      inference(global_propositional_subsumption,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_10854,c_14]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_11643,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),X0_43,k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0_43,k1_tops_1(sK0,sK1)))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.83/1.48      inference(renaming,[status(thm)],[c_11642]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_11651,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_408,c_11643]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_12086,plain,
% 7.83/1.48      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1))) ),
% 7.83/1.48      inference(global_propositional_subsumption,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_11651,c_14]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_12087,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,X0_43),k1_tops_1(sK0,sK1)))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.83/1.48      inference(renaming,[status(thm)],[c_12086]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_12096,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1)))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | l1_pre_topc(sK0) != iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_407,c_12087]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_19649,plain,
% 7.83/1.48      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.83/1.48      | k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1))) ),
% 7.83/1.48      inference(global_propositional_subsumption,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_12096,c_14]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_19650,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,k1_tops_1(sK0,X0_43)),k1_tops_1(sK0,sK1)))
% 7.83/1.48      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.83/1.48      inference(renaming,[status(thm)],[c_19649]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_19657,plain,
% 7.83/1.48      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))) ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_413,c_19650]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_23114,plain,
% 7.83/1.48      ( k3_tarski(k2_tarski(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))) = sK1 ),
% 7.83/1.48      inference(light_normalisation,
% 7.83/1.48                [status(thm)],
% 7.83/1.48                [c_23098,c_7543,c_19657]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_1,plain,
% 7.83/1.48      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 7.83/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_142,plain,
% 7.83/1.48      ( r1_tarski(X0_43,k3_tarski(k2_tarski(X0_43,X1_43))) ),
% 7.83/1.48      inference(subtyping,[status(esa)],[c_1]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_402,plain,
% 7.83/1.48      ( r1_tarski(X0_43,k3_tarski(k2_tarski(X0_43,X1_43))) = iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_142]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_0,plain,
% 7.83/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 7.83/1.48      inference(cnf_transformation,[],[f32]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_143,plain,
% 7.83/1.48      ( ~ r1_tarski(X0_43,X1_43)
% 7.83/1.48      | ~ r1_tarski(X2_43,X0_43)
% 7.83/1.48      | r1_tarski(X2_43,X1_43) ),
% 7.83/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_401,plain,
% 7.83/1.48      ( r1_tarski(X0_43,X1_43) != iProver_top
% 7.83/1.48      | r1_tarski(X2_43,X0_43) != iProver_top
% 7.83/1.48      | r1_tarski(X2_43,X1_43) = iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_143]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_654,plain,
% 7.83/1.48      ( r1_tarski(X0_43,X1_43) != iProver_top
% 7.83/1.48      | r1_tarski(X0_43,k3_tarski(k2_tarski(X1_43,X2_43))) = iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_402,c_401]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_23254,plain,
% 7.83/1.48      ( r1_tarski(X0_43,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 7.83/1.48      | r1_tarski(X0_43,sK1) = iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_23114,c_654]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_23882,plain,
% 7.83/1.48      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 7.83/1.48      inference(superposition,[status(thm)],[c_2734,c_23254]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_10,negated_conjecture,
% 7.83/1.48      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 7.83/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_133,negated_conjecture,
% 7.83/1.48      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 7.83/1.48      inference(subtyping,[status(esa)],[c_10]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_411,plain,
% 7.83/1.48      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 7.83/1.48      inference(predicate_to_equality,[status(thm)],[c_133]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(c_2532,plain,
% 7.83/1.48      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 7.83/1.48      inference(demodulation,[status(thm)],[c_2529,c_411]) ).
% 7.83/1.48  
% 7.83/1.48  cnf(contradiction,plain,
% 7.83/1.48      ( $false ),
% 7.83/1.48      inference(minisat,[status(thm)],[c_23882,c_2532]) ).
% 7.83/1.48  
% 7.83/1.48  
% 7.83/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.83/1.48  
% 7.83/1.48  ------                               Statistics
% 7.83/1.48  
% 7.83/1.48  ------ Selected
% 7.83/1.48  
% 7.83/1.48  total_time:                             0.719
% 7.83/1.48  
%------------------------------------------------------------------------------
