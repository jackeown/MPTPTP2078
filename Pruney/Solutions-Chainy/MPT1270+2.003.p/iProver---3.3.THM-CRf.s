%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:15 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  124 (1678 expanded)
%              Number of clauses        :   81 ( 530 expanded)
%              Number of leaves         :   17 ( 402 expanded)
%              Depth                    :   22
%              Number of atoms          :  276 (6155 expanded)
%              Number of equality atoms :  142 (1031 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(sK1,k2_tops_1(X0,sK1))
          | ~ v2_tops_1(sK1,X0) )
        & ( r1_tarski(sK1,k2_tops_1(X0,sK1))
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f42,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_13,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_97,plain,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_173,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_174,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_173])).

cnf(c_250,plain,
    ( ~ v2_tops_1(X0,sK0)
    | k1_tops_1(sK0,X0) = k1_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_174])).

cnf(c_251,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_279,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_251])).

cnf(c_366,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_279])).

cnf(c_656,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_660,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_683,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_660,c_8])).

cnf(c_3873,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_656,c_683])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_204,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_235,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_204])).

cnf(c_236,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_226,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_227,plain,
    ( k7_subset_1(X0,sK1,X1) = k4_xboole_0(sK1,X1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_725,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(equality_resolution,[status(thm)],[c_227])).

cnf(c_738,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_236,c_725])).

cnf(c_986,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_738,c_8])).

cnf(c_3900,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3873,c_986])).

cnf(c_987,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8,c_8])).

cnf(c_12954,plain,
    ( k1_setfam_1(k2_tarski(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_986,c_987])).

cnf(c_6,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_659,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_828,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_659])).

cnf(c_3875,plain,
    ( k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_828,c_683])).

cnf(c_4420,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6,c_3875])).

cnf(c_13112,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_12954,c_738,c_4420])).

cnf(c_13578,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,sK1)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3900,c_13112])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_932,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_738,c_2])).

cnf(c_14375,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_13578,c_932])).

cnf(c_280,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_464,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_473,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_462,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_483,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_940,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_945,plain,
    ( k1_xboole_0 = k4_xboole_0(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_947,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | r1_tarski(k4_xboole_0(sK1,sK1),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_945])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_985,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_8])).

cnf(c_1662,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_6,c_985])).

cnf(c_988,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_659])).

cnf(c_1838,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_988])).

cnf(c_1875,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK1),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1838])).

cnf(c_463,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_905,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X3) != X1
    | k4_xboole_0(X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_1373,plain,
    ( X0 != k4_xboole_0(X1,X2)
    | k4_xboole_0(X3,X4) = X0
    | k4_xboole_0(X3,X4) != k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_5460,plain,
    ( k4_xboole_0(X0,X1) != k4_xboole_0(X2,X3)
    | k4_xboole_0(X0,X1) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(X2,X3) ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_5461,plain,
    ( k4_xboole_0(sK1,sK1) != k4_xboole_0(sK1,sK1)
    | k4_xboole_0(sK1,sK1) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5460])).

cnf(c_10,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_188,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_189,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_240,plain,
    ( v2_tops_1(X0,sK0)
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_189])).

cnf(c_241,plain,
    ( v2_tops_1(sK1,sK0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_12,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_95,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_270,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_241,c_95])).

cnf(c_364,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_270])).

cnf(c_657,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_14369,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k4_xboole_0(sK1,sK1) != k1_xboole_0
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13578,c_657])).

cnf(c_14684,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14375,c_280,c_473,c_483,c_947,c_1875,c_5461,c_14369])).

cnf(c_1710,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_988])).

cnf(c_1887,plain,
    ( r1_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_1710])).

cnf(c_14739,plain,
    ( r1_tarski(k4_xboole_0(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14684,c_1887])).

cnf(c_14780,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14739,c_3])).

cnf(c_14740,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14684,c_657])).

cnf(c_14776,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14740])).

cnf(c_14782,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_14780,c_14776])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.12/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.00  
% 4.12/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.12/1.00  
% 4.12/1.00  ------  iProver source info
% 4.12/1.00  
% 4.12/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.12/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.12/1.00  git: non_committed_changes: false
% 4.12/1.00  git: last_make_outside_of_git: false
% 4.12/1.00  
% 4.12/1.00  ------ 
% 4.12/1.00  
% 4.12/1.00  ------ Input Options
% 4.12/1.00  
% 4.12/1.00  --out_options                           all
% 4.12/1.00  --tptp_safe_out                         true
% 4.12/1.00  --problem_path                          ""
% 4.12/1.00  --include_path                          ""
% 4.12/1.00  --clausifier                            res/vclausify_rel
% 4.12/1.00  --clausifier_options                    --mode clausify
% 4.12/1.00  --stdin                                 false
% 4.12/1.00  --stats_out                             all
% 4.12/1.00  
% 4.12/1.00  ------ General Options
% 4.12/1.00  
% 4.12/1.00  --fof                                   false
% 4.12/1.00  --time_out_real                         305.
% 4.12/1.00  --time_out_virtual                      -1.
% 4.12/1.00  --symbol_type_check                     false
% 4.12/1.00  --clausify_out                          false
% 4.12/1.00  --sig_cnt_out                           false
% 4.12/1.00  --trig_cnt_out                          false
% 4.12/1.00  --trig_cnt_out_tolerance                1.
% 4.12/1.00  --trig_cnt_out_sk_spl                   false
% 4.12/1.00  --abstr_cl_out                          false
% 4.12/1.00  
% 4.12/1.00  ------ Global Options
% 4.12/1.00  
% 4.12/1.00  --schedule                              default
% 4.12/1.00  --add_important_lit                     false
% 4.12/1.00  --prop_solver_per_cl                    1000
% 4.12/1.00  --min_unsat_core                        false
% 4.12/1.00  --soft_assumptions                      false
% 4.12/1.00  --soft_lemma_size                       3
% 4.12/1.00  --prop_impl_unit_size                   0
% 4.12/1.00  --prop_impl_unit                        []
% 4.12/1.00  --share_sel_clauses                     true
% 4.12/1.00  --reset_solvers                         false
% 4.12/1.00  --bc_imp_inh                            [conj_cone]
% 4.12/1.00  --conj_cone_tolerance                   3.
% 4.12/1.00  --extra_neg_conj                        none
% 4.12/1.00  --large_theory_mode                     true
% 4.12/1.00  --prolific_symb_bound                   200
% 4.12/1.00  --lt_threshold                          2000
% 4.12/1.00  --clause_weak_htbl                      true
% 4.12/1.00  --gc_record_bc_elim                     false
% 4.12/1.00  
% 4.12/1.00  ------ Preprocessing Options
% 4.12/1.00  
% 4.12/1.00  --preprocessing_flag                    true
% 4.12/1.00  --time_out_prep_mult                    0.1
% 4.12/1.00  --splitting_mode                        input
% 4.12/1.00  --splitting_grd                         true
% 4.12/1.00  --splitting_cvd                         false
% 4.12/1.00  --splitting_cvd_svl                     false
% 4.12/1.00  --splitting_nvd                         32
% 4.12/1.00  --sub_typing                            true
% 4.12/1.00  --prep_gs_sim                           true
% 4.12/1.00  --prep_unflatten                        true
% 4.12/1.00  --prep_res_sim                          true
% 4.12/1.00  --prep_upred                            true
% 4.12/1.00  --prep_sem_filter                       exhaustive
% 4.12/1.00  --prep_sem_filter_out                   false
% 4.12/1.00  --pred_elim                             true
% 4.12/1.00  --res_sim_input                         true
% 4.12/1.00  --eq_ax_congr_red                       true
% 4.12/1.00  --pure_diseq_elim                       true
% 4.12/1.00  --brand_transform                       false
% 4.12/1.00  --non_eq_to_eq                          false
% 4.12/1.00  --prep_def_merge                        true
% 4.12/1.00  --prep_def_merge_prop_impl              false
% 4.12/1.00  --prep_def_merge_mbd                    true
% 4.12/1.00  --prep_def_merge_tr_red                 false
% 4.12/1.00  --prep_def_merge_tr_cl                  false
% 4.12/1.00  --smt_preprocessing                     true
% 4.12/1.00  --smt_ac_axioms                         fast
% 4.12/1.00  --preprocessed_out                      false
% 4.12/1.00  --preprocessed_stats                    false
% 4.12/1.00  
% 4.12/1.00  ------ Abstraction refinement Options
% 4.12/1.00  
% 4.12/1.00  --abstr_ref                             []
% 4.12/1.00  --abstr_ref_prep                        false
% 4.12/1.00  --abstr_ref_until_sat                   false
% 4.12/1.00  --abstr_ref_sig_restrict                funpre
% 4.12/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.12/1.00  --abstr_ref_under                       []
% 4.12/1.00  
% 4.12/1.00  ------ SAT Options
% 4.12/1.00  
% 4.12/1.00  --sat_mode                              false
% 4.12/1.00  --sat_fm_restart_options                ""
% 4.12/1.00  --sat_gr_def                            false
% 4.12/1.00  --sat_epr_types                         true
% 4.12/1.00  --sat_non_cyclic_types                  false
% 4.12/1.00  --sat_finite_models                     false
% 4.12/1.00  --sat_fm_lemmas                         false
% 4.12/1.00  --sat_fm_prep                           false
% 4.12/1.00  --sat_fm_uc_incr                        true
% 4.12/1.00  --sat_out_model                         small
% 4.12/1.00  --sat_out_clauses                       false
% 4.12/1.00  
% 4.12/1.00  ------ QBF Options
% 4.12/1.00  
% 4.12/1.00  --qbf_mode                              false
% 4.12/1.00  --qbf_elim_univ                         false
% 4.12/1.00  --qbf_dom_inst                          none
% 4.12/1.00  --qbf_dom_pre_inst                      false
% 4.12/1.00  --qbf_sk_in                             false
% 4.12/1.00  --qbf_pred_elim                         true
% 4.12/1.00  --qbf_split                             512
% 4.12/1.00  
% 4.12/1.00  ------ BMC1 Options
% 4.12/1.00  
% 4.12/1.00  --bmc1_incremental                      false
% 4.12/1.00  --bmc1_axioms                           reachable_all
% 4.12/1.00  --bmc1_min_bound                        0
% 4.12/1.00  --bmc1_max_bound                        -1
% 4.12/1.00  --bmc1_max_bound_default                -1
% 4.12/1.00  --bmc1_symbol_reachability              true
% 4.12/1.00  --bmc1_property_lemmas                  false
% 4.12/1.00  --bmc1_k_induction                      false
% 4.12/1.00  --bmc1_non_equiv_states                 false
% 4.12/1.00  --bmc1_deadlock                         false
% 4.12/1.00  --bmc1_ucm                              false
% 4.12/1.00  --bmc1_add_unsat_core                   none
% 4.12/1.00  --bmc1_unsat_core_children              false
% 4.12/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.12/1.00  --bmc1_out_stat                         full
% 4.12/1.00  --bmc1_ground_init                      false
% 4.12/1.00  --bmc1_pre_inst_next_state              false
% 4.12/1.00  --bmc1_pre_inst_state                   false
% 4.12/1.00  --bmc1_pre_inst_reach_state             false
% 4.12/1.00  --bmc1_out_unsat_core                   false
% 4.12/1.00  --bmc1_aig_witness_out                  false
% 4.12/1.00  --bmc1_verbose                          false
% 4.12/1.00  --bmc1_dump_clauses_tptp                false
% 4.12/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.12/1.00  --bmc1_dump_file                        -
% 4.12/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.12/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.12/1.00  --bmc1_ucm_extend_mode                  1
% 4.12/1.00  --bmc1_ucm_init_mode                    2
% 4.12/1.00  --bmc1_ucm_cone_mode                    none
% 4.12/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.12/1.00  --bmc1_ucm_relax_model                  4
% 4.12/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.12/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.12/1.00  --bmc1_ucm_layered_model                none
% 4.12/1.00  --bmc1_ucm_max_lemma_size               10
% 4.12/1.00  
% 4.12/1.00  ------ AIG Options
% 4.12/1.00  
% 4.12/1.00  --aig_mode                              false
% 4.12/1.00  
% 4.12/1.00  ------ Instantiation Options
% 4.12/1.00  
% 4.12/1.00  --instantiation_flag                    true
% 4.12/1.00  --inst_sos_flag                         false
% 4.12/1.00  --inst_sos_phase                        true
% 4.12/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.12/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.12/1.00  --inst_lit_sel_side                     num_symb
% 4.12/1.00  --inst_solver_per_active                1400
% 4.12/1.00  --inst_solver_calls_frac                1.
% 4.12/1.00  --inst_passive_queue_type               priority_queues
% 4.12/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.12/1.00  --inst_passive_queues_freq              [25;2]
% 4.12/1.00  --inst_dismatching                      true
% 4.12/1.00  --inst_eager_unprocessed_to_passive     true
% 4.12/1.00  --inst_prop_sim_given                   true
% 4.12/1.00  --inst_prop_sim_new                     false
% 4.12/1.00  --inst_subs_new                         false
% 4.12/1.00  --inst_eq_res_simp                      false
% 4.12/1.00  --inst_subs_given                       false
% 4.12/1.00  --inst_orphan_elimination               true
% 4.12/1.00  --inst_learning_loop_flag               true
% 4.12/1.00  --inst_learning_start                   3000
% 4.12/1.00  --inst_learning_factor                  2
% 4.12/1.00  --inst_start_prop_sim_after_learn       3
% 4.12/1.00  --inst_sel_renew                        solver
% 4.12/1.00  --inst_lit_activity_flag                true
% 4.12/1.00  --inst_restr_to_given                   false
% 4.12/1.00  --inst_activity_threshold               500
% 4.12/1.00  --inst_out_proof                        true
% 4.12/1.00  
% 4.12/1.00  ------ Resolution Options
% 4.12/1.00  
% 4.12/1.00  --resolution_flag                       true
% 4.12/1.00  --res_lit_sel                           adaptive
% 4.12/1.00  --res_lit_sel_side                      none
% 4.12/1.00  --res_ordering                          kbo
% 4.12/1.00  --res_to_prop_solver                    active
% 4.12/1.00  --res_prop_simpl_new                    false
% 4.12/1.00  --res_prop_simpl_given                  true
% 4.12/1.00  --res_passive_queue_type                priority_queues
% 4.12/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.12/1.00  --res_passive_queues_freq               [15;5]
% 4.12/1.00  --res_forward_subs                      full
% 4.12/1.00  --res_backward_subs                     full
% 4.12/1.00  --res_forward_subs_resolution           true
% 4.12/1.00  --res_backward_subs_resolution          true
% 4.12/1.00  --res_orphan_elimination                true
% 4.12/1.00  --res_time_limit                        2.
% 4.12/1.00  --res_out_proof                         true
% 4.12/1.00  
% 4.12/1.00  ------ Superposition Options
% 4.12/1.00  
% 4.12/1.00  --superposition_flag                    true
% 4.12/1.00  --sup_passive_queue_type                priority_queues
% 4.12/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.12/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.12/1.00  --demod_completeness_check              fast
% 4.12/1.00  --demod_use_ground                      true
% 4.12/1.00  --sup_to_prop_solver                    passive
% 4.12/1.00  --sup_prop_simpl_new                    true
% 4.12/1.00  --sup_prop_simpl_given                  true
% 4.12/1.00  --sup_fun_splitting                     false
% 4.12/1.00  --sup_smt_interval                      50000
% 4.12/1.00  
% 4.12/1.00  ------ Superposition Simplification Setup
% 4.12/1.00  
% 4.12/1.00  --sup_indices_passive                   []
% 4.12/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.12/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.12/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.12/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.12/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.12/1.00  --sup_full_bw                           [BwDemod]
% 4.12/1.00  --sup_immed_triv                        [TrivRules]
% 4.12/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.12/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.12/1.00  --sup_immed_bw_main                     []
% 4.12/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.12/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.12/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.12/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.12/1.00  
% 4.12/1.00  ------ Combination Options
% 4.12/1.00  
% 4.12/1.00  --comb_res_mult                         3
% 4.12/1.00  --comb_sup_mult                         2
% 4.12/1.00  --comb_inst_mult                        10
% 4.12/1.00  
% 4.12/1.00  ------ Debug Options
% 4.12/1.00  
% 4.12/1.00  --dbg_backtrace                         false
% 4.12/1.00  --dbg_dump_prop_clauses                 false
% 4.12/1.00  --dbg_dump_prop_clauses_file            -
% 4.12/1.00  --dbg_out_stat                          false
% 4.12/1.00  ------ Parsing...
% 4.12/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.12/1.00  
% 4.12/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.12/1.00  
% 4.12/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.12/1.00  
% 4.12/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/1.00  ------ Proving...
% 4.12/1.00  ------ Problem Properties 
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  clauses                                 12
% 4.12/1.00  conjectures                             0
% 4.12/1.00  EPR                                     1
% 4.12/1.00  Horn                                    11
% 4.12/1.00  unary                                   7
% 4.12/1.00  binary                                  5
% 4.12/1.00  lits                                    17
% 4.12/1.00  lits eq                                 12
% 4.12/1.00  fd_pure                                 0
% 4.12/1.00  fd_pseudo                               0
% 4.12/1.00  fd_cond                                 1
% 4.12/1.00  fd_pseudo_cond                          0
% 4.12/1.00  AC symbols                              0
% 4.12/1.00  
% 4.12/1.00  ------ Schedule dynamic 5 is on 
% 4.12/1.00  
% 4.12/1.00  ------ no conjectures: strip conj schedule 
% 4.12/1.00  
% 4.12/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  ------ 
% 4.12/1.00  Current options:
% 4.12/1.00  ------ 
% 4.12/1.00  
% 4.12/1.00  ------ Input Options
% 4.12/1.00  
% 4.12/1.00  --out_options                           all
% 4.12/1.00  --tptp_safe_out                         true
% 4.12/1.00  --problem_path                          ""
% 4.12/1.00  --include_path                          ""
% 4.12/1.00  --clausifier                            res/vclausify_rel
% 4.12/1.00  --clausifier_options                    --mode clausify
% 4.12/1.00  --stdin                                 false
% 4.12/1.00  --stats_out                             all
% 4.12/1.00  
% 4.12/1.00  ------ General Options
% 4.12/1.00  
% 4.12/1.00  --fof                                   false
% 4.12/1.00  --time_out_real                         305.
% 4.12/1.00  --time_out_virtual                      -1.
% 4.12/1.00  --symbol_type_check                     false
% 4.12/1.00  --clausify_out                          false
% 4.12/1.00  --sig_cnt_out                           false
% 4.12/1.00  --trig_cnt_out                          false
% 4.12/1.00  --trig_cnt_out_tolerance                1.
% 4.12/1.00  --trig_cnt_out_sk_spl                   false
% 4.12/1.00  --abstr_cl_out                          false
% 4.12/1.00  
% 4.12/1.00  ------ Global Options
% 4.12/1.00  
% 4.12/1.00  --schedule                              default
% 4.12/1.00  --add_important_lit                     false
% 4.12/1.00  --prop_solver_per_cl                    1000
% 4.12/1.00  --min_unsat_core                        false
% 4.12/1.00  --soft_assumptions                      false
% 4.12/1.00  --soft_lemma_size                       3
% 4.12/1.00  --prop_impl_unit_size                   0
% 4.12/1.00  --prop_impl_unit                        []
% 4.12/1.00  --share_sel_clauses                     true
% 4.12/1.00  --reset_solvers                         false
% 4.12/1.00  --bc_imp_inh                            [conj_cone]
% 4.12/1.00  --conj_cone_tolerance                   3.
% 4.12/1.00  --extra_neg_conj                        none
% 4.12/1.00  --large_theory_mode                     true
% 4.12/1.00  --prolific_symb_bound                   200
% 4.12/1.00  --lt_threshold                          2000
% 4.12/1.00  --clause_weak_htbl                      true
% 4.12/1.00  --gc_record_bc_elim                     false
% 4.12/1.00  
% 4.12/1.00  ------ Preprocessing Options
% 4.12/1.00  
% 4.12/1.00  --preprocessing_flag                    true
% 4.12/1.00  --time_out_prep_mult                    0.1
% 4.12/1.00  --splitting_mode                        input
% 4.12/1.00  --splitting_grd                         true
% 4.12/1.00  --splitting_cvd                         false
% 4.12/1.00  --splitting_cvd_svl                     false
% 4.12/1.00  --splitting_nvd                         32
% 4.12/1.00  --sub_typing                            true
% 4.12/1.00  --prep_gs_sim                           true
% 4.12/1.00  --prep_unflatten                        true
% 4.12/1.00  --prep_res_sim                          true
% 4.12/1.00  --prep_upred                            true
% 4.12/1.00  --prep_sem_filter                       exhaustive
% 4.12/1.00  --prep_sem_filter_out                   false
% 4.12/1.00  --pred_elim                             true
% 4.12/1.00  --res_sim_input                         true
% 4.12/1.00  --eq_ax_congr_red                       true
% 4.12/1.00  --pure_diseq_elim                       true
% 4.12/1.00  --brand_transform                       false
% 4.12/1.00  --non_eq_to_eq                          false
% 4.12/1.00  --prep_def_merge                        true
% 4.12/1.00  --prep_def_merge_prop_impl              false
% 4.12/1.00  --prep_def_merge_mbd                    true
% 4.12/1.00  --prep_def_merge_tr_red                 false
% 4.12/1.00  --prep_def_merge_tr_cl                  false
% 4.12/1.00  --smt_preprocessing                     true
% 4.12/1.00  --smt_ac_axioms                         fast
% 4.12/1.00  --preprocessed_out                      false
% 4.12/1.00  --preprocessed_stats                    false
% 4.12/1.00  
% 4.12/1.00  ------ Abstraction refinement Options
% 4.12/1.00  
% 4.12/1.00  --abstr_ref                             []
% 4.12/1.00  --abstr_ref_prep                        false
% 4.12/1.00  --abstr_ref_until_sat                   false
% 4.12/1.00  --abstr_ref_sig_restrict                funpre
% 4.12/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.12/1.00  --abstr_ref_under                       []
% 4.12/1.00  
% 4.12/1.00  ------ SAT Options
% 4.12/1.00  
% 4.12/1.00  --sat_mode                              false
% 4.12/1.00  --sat_fm_restart_options                ""
% 4.12/1.00  --sat_gr_def                            false
% 4.12/1.00  --sat_epr_types                         true
% 4.12/1.00  --sat_non_cyclic_types                  false
% 4.12/1.00  --sat_finite_models                     false
% 4.12/1.00  --sat_fm_lemmas                         false
% 4.12/1.00  --sat_fm_prep                           false
% 4.12/1.00  --sat_fm_uc_incr                        true
% 4.12/1.00  --sat_out_model                         small
% 4.12/1.00  --sat_out_clauses                       false
% 4.12/1.00  
% 4.12/1.00  ------ QBF Options
% 4.12/1.00  
% 4.12/1.00  --qbf_mode                              false
% 4.12/1.00  --qbf_elim_univ                         false
% 4.12/1.00  --qbf_dom_inst                          none
% 4.12/1.00  --qbf_dom_pre_inst                      false
% 4.12/1.00  --qbf_sk_in                             false
% 4.12/1.00  --qbf_pred_elim                         true
% 4.12/1.00  --qbf_split                             512
% 4.12/1.00  
% 4.12/1.00  ------ BMC1 Options
% 4.12/1.00  
% 4.12/1.00  --bmc1_incremental                      false
% 4.12/1.00  --bmc1_axioms                           reachable_all
% 4.12/1.00  --bmc1_min_bound                        0
% 4.12/1.00  --bmc1_max_bound                        -1
% 4.12/1.00  --bmc1_max_bound_default                -1
% 4.12/1.00  --bmc1_symbol_reachability              true
% 4.12/1.00  --bmc1_property_lemmas                  false
% 4.12/1.00  --bmc1_k_induction                      false
% 4.12/1.00  --bmc1_non_equiv_states                 false
% 4.12/1.00  --bmc1_deadlock                         false
% 4.12/1.00  --bmc1_ucm                              false
% 4.12/1.00  --bmc1_add_unsat_core                   none
% 4.12/1.00  --bmc1_unsat_core_children              false
% 4.12/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.12/1.00  --bmc1_out_stat                         full
% 4.12/1.00  --bmc1_ground_init                      false
% 4.12/1.00  --bmc1_pre_inst_next_state              false
% 4.12/1.00  --bmc1_pre_inst_state                   false
% 4.12/1.00  --bmc1_pre_inst_reach_state             false
% 4.12/1.00  --bmc1_out_unsat_core                   false
% 4.12/1.00  --bmc1_aig_witness_out                  false
% 4.12/1.00  --bmc1_verbose                          false
% 4.12/1.00  --bmc1_dump_clauses_tptp                false
% 4.12/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.12/1.00  --bmc1_dump_file                        -
% 4.12/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.12/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.12/1.00  --bmc1_ucm_extend_mode                  1
% 4.12/1.00  --bmc1_ucm_init_mode                    2
% 4.12/1.00  --bmc1_ucm_cone_mode                    none
% 4.12/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.12/1.00  --bmc1_ucm_relax_model                  4
% 4.12/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.12/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.12/1.00  --bmc1_ucm_layered_model                none
% 4.12/1.00  --bmc1_ucm_max_lemma_size               10
% 4.12/1.00  
% 4.12/1.00  ------ AIG Options
% 4.12/1.00  
% 4.12/1.00  --aig_mode                              false
% 4.12/1.00  
% 4.12/1.00  ------ Instantiation Options
% 4.12/1.00  
% 4.12/1.00  --instantiation_flag                    true
% 4.12/1.00  --inst_sos_flag                         false
% 4.12/1.00  --inst_sos_phase                        true
% 4.12/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.12/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.12/1.00  --inst_lit_sel_side                     none
% 4.12/1.00  --inst_solver_per_active                1400
% 4.12/1.00  --inst_solver_calls_frac                1.
% 4.12/1.00  --inst_passive_queue_type               priority_queues
% 4.12/1.00  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 4.12/1.00  --inst_passive_queues_freq              [25;2]
% 4.12/1.00  --inst_dismatching                      true
% 4.12/1.00  --inst_eager_unprocessed_to_passive     true
% 4.12/1.00  --inst_prop_sim_given                   true
% 4.12/1.00  --inst_prop_sim_new                     false
% 4.12/1.00  --inst_subs_new                         false
% 4.12/1.00  --inst_eq_res_simp                      false
% 4.12/1.00  --inst_subs_given                       false
% 4.12/1.00  --inst_orphan_elimination               true
% 4.12/1.00  --inst_learning_loop_flag               true
% 4.12/1.00  --inst_learning_start                   3000
% 4.12/1.00  --inst_learning_factor                  2
% 4.12/1.00  --inst_start_prop_sim_after_learn       3
% 4.12/1.00  --inst_sel_renew                        solver
% 4.12/1.00  --inst_lit_activity_flag                true
% 4.12/1.00  --inst_restr_to_given                   false
% 4.12/1.00  --inst_activity_threshold               500
% 4.12/1.00  --inst_out_proof                        true
% 4.12/1.00  
% 4.12/1.00  ------ Resolution Options
% 4.12/1.00  
% 4.12/1.00  --resolution_flag                       false
% 4.12/1.00  --res_lit_sel                           adaptive
% 4.12/1.00  --res_lit_sel_side                      none
% 4.12/1.00  --res_ordering                          kbo
% 4.12/1.00  --res_to_prop_solver                    active
% 4.12/1.00  --res_prop_simpl_new                    false
% 4.12/1.00  --res_prop_simpl_given                  true
% 4.12/1.00  --res_passive_queue_type                priority_queues
% 4.12/1.00  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 4.12/1.00  --res_passive_queues_freq               [15;5]
% 4.12/1.00  --res_forward_subs                      full
% 4.12/1.00  --res_backward_subs                     full
% 4.12/1.00  --res_forward_subs_resolution           true
% 4.12/1.00  --res_backward_subs_resolution          true
% 4.12/1.00  --res_orphan_elimination                true
% 4.12/1.00  --res_time_limit                        2.
% 4.12/1.00  --res_out_proof                         true
% 4.12/1.00  
% 4.12/1.00  ------ Superposition Options
% 4.12/1.00  
% 4.12/1.00  --superposition_flag                    true
% 4.12/1.00  --sup_passive_queue_type                priority_queues
% 4.12/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.12/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.12/1.00  --demod_completeness_check              fast
% 4.12/1.00  --demod_use_ground                      true
% 4.12/1.00  --sup_to_prop_solver                    passive
% 4.12/1.00  --sup_prop_simpl_new                    true
% 4.12/1.00  --sup_prop_simpl_given                  true
% 4.12/1.00  --sup_fun_splitting                     false
% 4.12/1.00  --sup_smt_interval                      50000
% 4.12/1.00  
% 4.12/1.00  ------ Superposition Simplification Setup
% 4.12/1.00  
% 4.12/1.00  --sup_indices_passive                   []
% 4.12/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.12/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.12/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.12/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.12/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.12/1.00  --sup_full_bw                           [BwDemod]
% 4.12/1.00  --sup_immed_triv                        [TrivRules]
% 4.12/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.12/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.12/1.00  --sup_immed_bw_main                     []
% 4.12/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.12/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.12/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.12/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.12/1.00  
% 4.12/1.00  ------ Combination Options
% 4.12/1.00  
% 4.12/1.00  --comb_res_mult                         3
% 4.12/1.00  --comb_sup_mult                         2
% 4.12/1.00  --comb_inst_mult                        10
% 4.12/1.00  
% 4.12/1.00  ------ Debug Options
% 4.12/1.00  
% 4.12/1.00  --dbg_backtrace                         false
% 4.12/1.00  --dbg_dump_prop_clauses                 false
% 4.12/1.00  --dbg_dump_prop_clauses_file            -
% 4.12/1.00  --dbg_out_stat                          false
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  ------ Proving...
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  % SZS status Theorem for theBenchmark.p
% 4.12/1.00  
% 4.12/1.00   Resolution empty clause
% 4.12/1.00  
% 4.12/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.12/1.00  
% 4.12/1.00  fof(f13,conjecture,(
% 4.12/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f14,negated_conjecture,(
% 4.12/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 4.12/1.00    inference(negated_conjecture,[],[f13])).
% 4.12/1.00  
% 4.12/1.00  fof(f20,plain,(
% 4.12/1.00    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.12/1.00    inference(ennf_transformation,[],[f14])).
% 4.12/1.00  
% 4.12/1.00  fof(f22,plain,(
% 4.12/1.00    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.12/1.00    inference(nnf_transformation,[],[f20])).
% 4.12/1.00  
% 4.12/1.00  fof(f23,plain,(
% 4.12/1.00    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.12/1.00    inference(flattening,[],[f22])).
% 4.12/1.00  
% 4.12/1.00  fof(f25,plain,(
% 4.12/1.00    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~r1_tarski(sK1,k2_tops_1(X0,sK1)) | ~v2_tops_1(sK1,X0)) & (r1_tarski(sK1,k2_tops_1(X0,sK1)) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.12/1.00    introduced(choice_axiom,[])).
% 4.12/1.00  
% 4.12/1.00  fof(f24,plain,(
% 4.12/1.00    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 4.12/1.00    introduced(choice_axiom,[])).
% 4.12/1.00  
% 4.12/1.00  fof(f26,plain,(
% 4.12/1.00    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 4.12/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).
% 4.12/1.00  
% 4.12/1.00  fof(f42,plain,(
% 4.12/1.00    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 4.12/1.00    inference(cnf_transformation,[],[f26])).
% 4.12/1.00  
% 4.12/1.00  fof(f41,plain,(
% 4.12/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.12/1.00    inference(cnf_transformation,[],[f26])).
% 4.12/1.00  
% 4.12/1.00  fof(f12,axiom,(
% 4.12/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f19,plain,(
% 4.12/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/1.00    inference(ennf_transformation,[],[f12])).
% 4.12/1.00  
% 4.12/1.00  fof(f21,plain,(
% 4.12/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/1.00    inference(nnf_transformation,[],[f19])).
% 4.12/1.00  
% 4.12/1.00  fof(f38,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f21])).
% 4.12/1.00  
% 4.12/1.00  fof(f40,plain,(
% 4.12/1.00    l1_pre_topc(sK0)),
% 4.12/1.00    inference(cnf_transformation,[],[f26])).
% 4.12/1.00  
% 4.12/1.00  fof(f1,axiom,(
% 4.12/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f15,plain,(
% 4.12/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.12/1.00    inference(ennf_transformation,[],[f1])).
% 4.12/1.00  
% 4.12/1.00  fof(f27,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f15])).
% 4.12/1.00  
% 4.12/1.00  fof(f7,axiom,(
% 4.12/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f33,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.12/1.00    inference(cnf_transformation,[],[f7])).
% 4.12/1.00  
% 4.12/1.00  fof(f44,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 4.12/1.00    inference(definition_unfolding,[],[f27,f33])).
% 4.12/1.00  
% 4.12/1.00  fof(f10,axiom,(
% 4.12/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f36,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.12/1.00    inference(cnf_transformation,[],[f10])).
% 4.12/1.00  
% 4.12/1.00  fof(f45,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.12/1.00    inference(definition_unfolding,[],[f36,f33])).
% 4.12/1.00  
% 4.12/1.00  fof(f11,axiom,(
% 4.12/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f18,plain,(
% 4.12/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/1.00    inference(ennf_transformation,[],[f11])).
% 4.12/1.00  
% 4.12/1.00  fof(f37,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f18])).
% 4.12/1.00  
% 4.12/1.00  fof(f9,axiom,(
% 4.12/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f17,plain,(
% 4.12/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.12/1.00    inference(ennf_transformation,[],[f9])).
% 4.12/1.00  
% 4.12/1.00  fof(f35,plain,(
% 4.12/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.12/1.00    inference(cnf_transformation,[],[f17])).
% 4.12/1.00  
% 4.12/1.00  fof(f8,axiom,(
% 4.12/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f34,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f8])).
% 4.12/1.00  
% 4.12/1.00  fof(f2,axiom,(
% 4.12/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f28,plain,(
% 4.12/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f2])).
% 4.12/1.00  
% 4.12/1.00  fof(f3,axiom,(
% 4.12/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f29,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.12/1.00    inference(cnf_transformation,[],[f3])).
% 4.12/1.00  
% 4.12/1.00  fof(f5,axiom,(
% 4.12/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f16,plain,(
% 4.12/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 4.12/1.00    inference(ennf_transformation,[],[f5])).
% 4.12/1.00  
% 4.12/1.00  fof(f31,plain,(
% 4.12/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f16])).
% 4.12/1.00  
% 4.12/1.00  fof(f4,axiom,(
% 4.12/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f30,plain,(
% 4.12/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.12/1.00    inference(cnf_transformation,[],[f4])).
% 4.12/1.00  
% 4.12/1.00  fof(f39,plain,(
% 4.12/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f21])).
% 4.12/1.00  
% 4.12/1.00  fof(f43,plain,(
% 4.12/1.00    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 4.12/1.00    inference(cnf_transformation,[],[f26])).
% 4.12/1.00  
% 4.12/1.00  cnf(c_13,negated_conjecture,
% 4.12/1.00      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 4.12/1.00      inference(cnf_transformation,[],[f42]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_97,plain,
% 4.12/1.00      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 4.12/1.00      inference(prop_impl,[status(thm)],[c_13]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_14,negated_conjecture,
% 4.12/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.12/1.00      inference(cnf_transformation,[],[f41]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_11,plain,
% 4.12/1.00      ( ~ v2_tops_1(X0,X1)
% 4.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/1.00      | ~ l1_pre_topc(X1)
% 4.12/1.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 4.12/1.00      inference(cnf_transformation,[],[f38]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_15,negated_conjecture,
% 4.12/1.00      ( l1_pre_topc(sK0) ),
% 4.12/1.00      inference(cnf_transformation,[],[f40]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_173,plain,
% 4.12/1.00      ( ~ v2_tops_1(X0,X1)
% 4.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/1.00      | k1_tops_1(X1,X0) = k1_xboole_0
% 4.12/1.00      | sK0 != X1 ),
% 4.12/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_174,plain,
% 4.12/1.00      ( ~ v2_tops_1(X0,sK0)
% 4.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.12/1.00      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 4.12/1.00      inference(unflattening,[status(thm)],[c_173]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_250,plain,
% 4.12/1.00      ( ~ v2_tops_1(X0,sK0)
% 4.12/1.00      | k1_tops_1(sK0,X0) = k1_xboole_0
% 4.12/1.00      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 4.12/1.00      | sK1 != X0 ),
% 4.12/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_174]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_251,plain,
% 4.12/1.00      ( ~ v2_tops_1(sK1,sK0) | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 4.12/1.00      inference(unflattening,[status(thm)],[c_250]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_279,plain,
% 4.12/1.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 4.12/1.00      inference(resolution,[status(thm)],[c_97,c_251]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_366,plain,
% 4.12/1.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 4.12/1.00      inference(prop_impl,[status(thm)],[c_279]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_656,plain,
% 4.12/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 4.12/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_0,plain,
% 4.12/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 4.12/1.00      inference(cnf_transformation,[],[f44]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_660,plain,
% 4.12/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 4.12/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_8,plain,
% 4.12/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 4.12/1.00      inference(cnf_transformation,[],[f45]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_683,plain,
% 4.12/1.00      ( k1_setfam_1(k2_tarski(X0,X1)) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 4.12/1.00      inference(demodulation,[status(thm)],[c_660,c_8]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_3873,plain,
% 4.12/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 4.12/1.00      | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_656,c_683]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_9,plain,
% 4.12/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/1.00      | ~ l1_pre_topc(X1)
% 4.12/1.00      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 4.12/1.00      inference(cnf_transformation,[],[f37]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_203,plain,
% 4.12/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/1.00      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 4.12/1.00      | sK0 != X1 ),
% 4.12/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_204,plain,
% 4.12/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.12/1.00      | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 4.12/1.00      inference(unflattening,[status(thm)],[c_203]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_235,plain,
% 4.12/1.00      ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 4.12/1.00      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 4.12/1.00      | sK1 != X0 ),
% 4.12/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_204]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_236,plain,
% 4.12/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 4.12/1.00      inference(unflattening,[status(thm)],[c_235]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_7,plain,
% 4.12/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.12/1.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 4.12/1.00      inference(cnf_transformation,[],[f35]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_226,plain,
% 4.12/1.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 4.12/1.00      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0)
% 4.12/1.00      | sK1 != X1 ),
% 4.12/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_227,plain,
% 4.12/1.00      ( k7_subset_1(X0,sK1,X1) = k4_xboole_0(sK1,X1)
% 4.12/1.00      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
% 4.12/1.00      inference(unflattening,[status(thm)],[c_226]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_725,plain,
% 4.12/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 4.12/1.00      inference(equality_resolution,[status(thm)],[c_227]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_738,plain,
% 4.12/1.00      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_236,c_725]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_986,plain,
% 4.12/1.00      ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_738,c_8]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_3900,plain,
% 4.12/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 4.12/1.00      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1 ),
% 4.12/1.00      inference(demodulation,[status(thm)],[c_3873,c_986]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_987,plain,
% 4.12/1.00      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_8,c_8]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_12954,plain,
% 4.12/1.00      ( k1_setfam_1(k2_tarski(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_986,c_987]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_6,plain,
% 4.12/1.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 4.12/1.00      inference(cnf_transformation,[],[f34]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1,plain,
% 4.12/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 4.12/1.00      inference(cnf_transformation,[],[f28]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_659,plain,
% 4.12/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_828,plain,
% 4.12/1.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_738,c_659]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_3875,plain,
% 4.12/1.00      ( k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k1_tops_1(sK0,sK1) ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_828,c_683]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_4420,plain,
% 4.12/1.00      ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_6,c_3875]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_13112,plain,
% 4.12/1.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 4.12/1.00      inference(light_normalisation,[status(thm)],[c_12954,c_738,c_4420]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_13578,plain,
% 4.12/1.00      ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,sK1)
% 4.12/1.00      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_3900,c_13112]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_2,plain,
% 4.12/1.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 4.12/1.00      inference(cnf_transformation,[],[f29]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_932,plain,
% 4.12/1.00      ( k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_738,c_2]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_14375,plain,
% 4.12/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 4.12/1.00      | k2_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_13578,c_932]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_280,plain,
% 4.12/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 4.12/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_464,plain,
% 4.12/1.00      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 4.12/1.00      theory(equality) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_473,plain,
% 4.12/1.00      ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1) | sK1 != sK1 ),
% 4.12/1.00      inference(instantiation,[status(thm)],[c_464]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_462,plain,( X0 = X0 ),theory(equality) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_483,plain,
% 4.12/1.00      ( sK1 = sK1 ),
% 4.12/1.00      inference(instantiation,[status(thm)],[c_462]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_4,plain,
% 4.12/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 4.12/1.00      inference(cnf_transformation,[],[f31]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_940,plain,
% 4.12/1.00      ( ~ r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0)
% 4.12/1.00      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 4.12/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_945,plain,
% 4.12/1.00      ( k1_xboole_0 = k4_xboole_0(X0,X1)
% 4.12/1.00      | r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) != iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_947,plain,
% 4.12/1.00      ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
% 4.12/1.00      | r1_tarski(k4_xboole_0(sK1,sK1),k1_xboole_0) != iProver_top ),
% 4.12/1.00      inference(instantiation,[status(thm)],[c_945]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_3,plain,
% 4.12/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.12/1.00      inference(cnf_transformation,[],[f30]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_985,plain,
% 4.12/1.00      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_3,c_8]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1662,plain,
% 4.12/1.00      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_6,c_985]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_988,plain,
% 4.12/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_8,c_659]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1838,plain,
% 4.12/1.00      ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_1662,c_988]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1875,plain,
% 4.12/1.00      ( r1_tarski(k4_xboole_0(sK1,sK1),k1_xboole_0) = iProver_top ),
% 4.12/1.00      inference(instantiation,[status(thm)],[c_1838]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_463,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_905,plain,
% 4.12/1.00      ( X0 != X1 | k4_xboole_0(X2,X3) != X1 | k4_xboole_0(X2,X3) = X0 ),
% 4.12/1.00      inference(instantiation,[status(thm)],[c_463]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1373,plain,
% 4.12/1.00      ( X0 != k4_xboole_0(X1,X2)
% 4.12/1.00      | k4_xboole_0(X3,X4) = X0
% 4.12/1.00      | k4_xboole_0(X3,X4) != k4_xboole_0(X1,X2) ),
% 4.12/1.00      inference(instantiation,[status(thm)],[c_905]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_5460,plain,
% 4.12/1.00      ( k4_xboole_0(X0,X1) != k4_xboole_0(X2,X3)
% 4.12/1.00      | k4_xboole_0(X0,X1) = k1_xboole_0
% 4.12/1.00      | k1_xboole_0 != k4_xboole_0(X2,X3) ),
% 4.12/1.00      inference(instantiation,[status(thm)],[c_1373]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_5461,plain,
% 4.12/1.00      ( k4_xboole_0(sK1,sK1) != k4_xboole_0(sK1,sK1)
% 4.12/1.00      | k4_xboole_0(sK1,sK1) = k1_xboole_0
% 4.12/1.00      | k1_xboole_0 != k4_xboole_0(sK1,sK1) ),
% 4.12/1.00      inference(instantiation,[status(thm)],[c_5460]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_10,plain,
% 4.12/1.00      ( v2_tops_1(X0,X1)
% 4.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/1.00      | ~ l1_pre_topc(X1)
% 4.12/1.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 4.12/1.00      inference(cnf_transformation,[],[f39]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_188,plain,
% 4.12/1.00      ( v2_tops_1(X0,X1)
% 4.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/1.00      | k1_tops_1(X1,X0) != k1_xboole_0
% 4.12/1.00      | sK0 != X1 ),
% 4.12/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_189,plain,
% 4.12/1.00      ( v2_tops_1(X0,sK0)
% 4.12/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.12/1.00      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 4.12/1.00      inference(unflattening,[status(thm)],[c_188]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_240,plain,
% 4.12/1.00      ( v2_tops_1(X0,sK0)
% 4.12/1.00      | k1_tops_1(sK0,X0) != k1_xboole_0
% 4.12/1.00      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 4.12/1.00      | sK1 != X0 ),
% 4.12/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_189]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_241,plain,
% 4.12/1.00      ( v2_tops_1(sK1,sK0) | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 4.12/1.00      inference(unflattening,[status(thm)],[c_240]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_12,negated_conjecture,
% 4.12/1.00      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 4.12/1.00      inference(cnf_transformation,[],[f43]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_95,plain,
% 4.12/1.00      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 4.12/1.00      inference(prop_impl,[status(thm)],[c_12]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_270,plain,
% 4.12/1.00      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 4.12/1.00      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 4.12/1.00      inference(resolution,[status(thm)],[c_241,c_95]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_364,plain,
% 4.12/1.00      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 4.12/1.00      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 4.12/1.00      inference(prop_impl,[status(thm)],[c_270]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_657,plain,
% 4.12/1.00      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 4.12/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_14369,plain,
% 4.12/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 4.12/1.00      | k4_xboole_0(sK1,sK1) != k1_xboole_0
% 4.12/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_13578,c_657]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_14684,plain,
% 4.12/1.00      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 4.12/1.00      inference(global_propositional_subsumption,
% 4.12/1.00                [status(thm)],
% 4.12/1.00                [c_14375,c_280,c_473,c_483,c_947,c_1875,c_5461,c_14369]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1710,plain,
% 4.12/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_6,c_988]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1887,plain,
% 4.12/1.00      ( r1_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_986,c_1710]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_14739,plain,
% 4.12/1.00      ( r1_tarski(k4_xboole_0(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) = iProver_top ),
% 4.12/1.00      inference(demodulation,[status(thm)],[c_14684,c_1887]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_14780,plain,
% 4.12/1.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 4.12/1.00      inference(demodulation,[status(thm)],[c_14739,c_3]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_14740,plain,
% 4.12/1.00      ( k1_xboole_0 != k1_xboole_0
% 4.12/1.00      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 4.12/1.00      inference(demodulation,[status(thm)],[c_14684,c_657]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_14776,plain,
% 4.12/1.00      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 4.12/1.00      inference(equality_resolution_simp,[status(thm)],[c_14740]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_14782,plain,
% 4.12/1.00      ( $false ),
% 4.12/1.00      inference(backward_subsumption_resolution,
% 4.12/1.00                [status(thm)],
% 4.12/1.00                [c_14780,c_14776]) ).
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.12/1.00  
% 4.12/1.00  ------                               Statistics
% 4.12/1.00  
% 4.12/1.00  ------ General
% 4.12/1.00  
% 4.12/1.00  abstr_ref_over_cycles:                  0
% 4.12/1.00  abstr_ref_under_cycles:                 0
% 4.12/1.00  gc_basic_clause_elim:                   0
% 4.12/1.00  forced_gc_time:                         0
% 4.12/1.00  parsing_time:                           0.013
% 4.12/1.00  unif_index_cands_time:                  0.
% 4.12/1.00  unif_index_add_time:                    0.
% 4.12/1.00  orderings_time:                         0.
% 4.12/1.00  out_proof_time:                         0.008
% 4.12/1.00  total_time:                             0.419
% 4.12/1.00  num_of_symbols:                         47
% 4.12/1.00  num_of_terms:                           16216
% 4.12/1.00  
% 4.12/1.00  ------ Preprocessing
% 4.12/1.00  
% 4.12/1.00  num_of_splits:                          0
% 4.12/1.00  num_of_split_atoms:                     0
% 4.12/1.00  num_of_reused_defs:                     0
% 4.12/1.00  num_eq_ax_congr_red:                    12
% 4.12/1.00  num_of_sem_filtered_clauses:            1
% 4.12/1.00  num_of_subtypes:                        0
% 4.12/1.00  monotx_restored_types:                  0
% 4.12/1.00  sat_num_of_epr_types:                   0
% 4.12/1.00  sat_num_of_non_cyclic_types:            0
% 4.12/1.00  sat_guarded_non_collapsed_types:        0
% 4.12/1.00  num_pure_diseq_elim:                    0
% 4.12/1.00  simp_replaced_by:                       0
% 4.12/1.00  res_preprocessed:                       75
% 4.12/1.00  prep_upred:                             0
% 4.12/1.00  prep_unflattend:                        23
% 4.12/1.00  smt_new_axioms:                         0
% 4.12/1.00  pred_elim_cands:                        1
% 4.12/1.00  pred_elim:                              3
% 4.12/1.00  pred_elim_cl:                           4
% 4.12/1.00  pred_elim_cycles:                       5
% 4.12/1.00  merged_defs:                            8
% 4.12/1.00  merged_defs_ncl:                        0
% 4.12/1.00  bin_hyper_res:                          8
% 4.12/1.00  prep_cycles:                            4
% 4.12/1.00  pred_elim_time:                         0.004
% 4.12/1.00  splitting_time:                         0.
% 4.12/1.00  sem_filter_time:                        0.
% 4.12/1.00  monotx_time:                            0.
% 4.12/1.00  subtype_inf_time:                       0.
% 4.12/1.00  
% 4.12/1.00  ------ Problem properties
% 4.12/1.00  
% 4.12/1.00  clauses:                                12
% 4.12/1.00  conjectures:                            0
% 4.12/1.00  epr:                                    1
% 4.12/1.00  horn:                                   11
% 4.12/1.00  ground:                                 3
% 4.12/1.00  unary:                                  7
% 4.12/1.00  binary:                                 5
% 4.12/1.00  lits:                                   17
% 4.12/1.00  lits_eq:                                12
% 4.12/1.00  fd_pure:                                0
% 4.12/1.00  fd_pseudo:                              0
% 4.12/1.00  fd_cond:                                1
% 4.12/1.00  fd_pseudo_cond:                         0
% 4.12/1.00  ac_symbols:                             0
% 4.12/1.00  
% 4.12/1.00  ------ Propositional Solver
% 4.12/1.00  
% 4.12/1.00  prop_solver_calls:                      31
% 4.12/1.00  prop_fast_solver_calls:                 449
% 4.12/1.00  smt_solver_calls:                       0
% 4.12/1.00  smt_fast_solver_calls:                  0
% 4.12/1.00  prop_num_of_clauses:                    4698
% 4.12/1.00  prop_preprocess_simplified:             6777
% 4.12/1.00  prop_fo_subsumed:                       1
% 4.12/1.00  prop_solver_time:                       0.
% 4.12/1.00  smt_solver_time:                        0.
% 4.12/1.00  smt_fast_solver_time:                   0.
% 4.12/1.00  prop_fast_solver_time:                  0.
% 4.12/1.00  prop_unsat_core_time:                   0.
% 4.12/1.00  
% 4.12/1.00  ------ QBF
% 4.12/1.00  
% 4.12/1.00  qbf_q_res:                              0
% 4.12/1.00  qbf_num_tautologies:                    0
% 4.12/1.00  qbf_prep_cycles:                        0
% 4.12/1.00  
% 4.12/1.00  ------ BMC1
% 4.12/1.00  
% 4.12/1.00  bmc1_current_bound:                     -1
% 4.12/1.00  bmc1_last_solved_bound:                 -1
% 4.12/1.00  bmc1_unsat_core_size:                   -1
% 4.12/1.00  bmc1_unsat_core_parents_size:           -1
% 4.12/1.00  bmc1_merge_next_fun:                    0
% 4.12/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.12/1.00  
% 4.12/1.00  ------ Instantiation
% 4.12/1.00  
% 4.12/1.00  inst_num_of_clauses:                    1441
% 4.12/1.00  inst_num_in_passive:                    256
% 4.12/1.00  inst_num_in_active:                     562
% 4.12/1.00  inst_num_in_unprocessed:                625
% 4.12/1.00  inst_num_of_loops:                      590
% 4.12/1.00  inst_num_of_learning_restarts:          0
% 4.12/1.00  inst_num_moves_active_passive:          21
% 4.12/1.00  inst_lit_activity:                      0
% 4.12/1.00  inst_lit_activity_moves:                0
% 4.12/1.00  inst_num_tautologies:                   0
% 4.12/1.00  inst_num_prop_implied:                  0
% 4.12/1.00  inst_num_existing_simplified:           0
% 4.12/1.00  inst_num_eq_res_simplified:             0
% 4.12/1.00  inst_num_child_elim:                    0
% 4.12/1.00  inst_num_of_dismatching_blockings:      1656
% 4.12/1.00  inst_num_of_non_proper_insts:           1950
% 4.12/1.00  inst_num_of_duplicates:                 0
% 4.12/1.00  inst_inst_num_from_inst_to_res:         0
% 4.12/1.00  inst_dismatching_checking_time:         0.
% 4.12/1.00  
% 4.12/1.00  ------ Resolution
% 4.12/1.00  
% 4.12/1.00  res_num_of_clauses:                     0
% 4.12/1.00  res_num_in_passive:                     0
% 4.12/1.00  res_num_in_active:                      0
% 4.12/1.00  res_num_of_loops:                       79
% 4.12/1.00  res_forward_subset_subsumed:            346
% 4.12/1.00  res_backward_subset_subsumed:           14
% 4.12/1.00  res_forward_subsumed:                   0
% 4.12/1.00  res_backward_subsumed:                  0
% 4.12/1.00  res_forward_subsumption_resolution:     0
% 4.12/1.00  res_backward_subsumption_resolution:    0
% 4.12/1.00  res_clause_to_clause_subsumption:       3586
% 4.12/1.00  res_orphan_elimination:                 0
% 4.12/1.00  res_tautology_del:                      187
% 4.12/1.00  res_num_eq_res_simplified:              0
% 4.12/1.00  res_num_sel_changes:                    0
% 4.12/1.00  res_moves_from_active_to_pass:          0
% 4.12/1.00  
% 4.12/1.00  ------ Superposition
% 4.12/1.00  
% 4.12/1.00  sup_time_total:                         0.
% 4.12/1.00  sup_time_generating:                    0.
% 4.12/1.00  sup_time_sim_full:                      0.
% 4.12/1.00  sup_time_sim_immed:                     0.
% 4.12/1.00  
% 4.12/1.00  sup_num_of_clauses:                     617
% 4.12/1.00  sup_num_in_active:                      38
% 4.12/1.00  sup_num_in_passive:                     579
% 4.12/1.00  sup_num_of_loops:                       117
% 4.12/1.00  sup_fw_superposition:                   764
% 4.12/1.00  sup_bw_superposition:                   879
% 4.12/1.00  sup_immediate_simplified:               754
% 4.12/1.00  sup_given_eliminated:                   3
% 4.12/1.00  comparisons_done:                       0
% 4.12/1.00  comparisons_avoided:                    3
% 4.12/1.00  
% 4.12/1.00  ------ Simplifications
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  sim_fw_subset_subsumed:                 1
% 4.12/1.00  sim_bw_subset_subsumed:                 62
% 4.12/1.00  sim_fw_subsumed:                        200
% 4.12/1.00  sim_bw_subsumed:                        6
% 4.12/1.00  sim_fw_subsumption_res:                 0
% 4.12/1.00  sim_bw_subsumption_res:                 1
% 4.12/1.00  sim_tautology_del:                      0
% 4.12/1.00  sim_eq_tautology_del:                   83
% 4.12/1.00  sim_eq_res_simp:                        1
% 4.12/1.00  sim_fw_demodulated:                     326
% 4.12/1.00  sim_bw_demodulated:                     115
% 4.12/1.00  sim_light_normalised:                   339
% 4.12/1.00  sim_joinable_taut:                      0
% 4.12/1.00  sim_joinable_simp:                      0
% 4.12/1.00  sim_ac_normalised:                      0
% 4.12/1.00  sim_smt_subsumption:                    0
% 4.12/1.00  
%------------------------------------------------------------------------------
