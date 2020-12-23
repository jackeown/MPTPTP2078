%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:15 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 498 expanded)
%              Number of clauses        :   49 ( 159 expanded)
%              Number of leaves         :   12 ( 118 expanded)
%              Depth                    :   19
%              Number of atoms          :  209 (1764 expanded)
%              Number of equality atoms :   95 ( 307 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f30,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f36,f36])).

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

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_537,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_542,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4972,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_542])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_546,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1618,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_537,c_546])).

cnf(c_4975,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4972,c_1618])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4989,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4975,c_16])).

cnf(c_13,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_538,plain,
    ( v2_tops_1(sK1,sK0) = iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_549,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1588,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = sK1
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_538,c_549])).

cnf(c_4992,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4989,c_1588])).

cnf(c_11,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_540,plain,
    ( k1_tops_1(X0,X1) = k1_xboole_0
    | v2_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6255,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_540])).

cnf(c_6685,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6255,c_16])).

cnf(c_6686,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6685])).

cnf(c_6691,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_4992,c_6686])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_548,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5008,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4989,c_548])).

cnf(c_5282,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k1_tops_1(sK0,sK1),sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5008,c_549])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18256,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5282,c_0])).

cnf(c_19334,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,sK1)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6691,c_18256])).

cnf(c_977,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_548])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_547,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1157,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_977,c_547])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1159,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1157,c_3])).

cnf(c_19501,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19334,c_1159])).

cnf(c_5007,plain,
    ( r1_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4989,c_977])).

cnf(c_20793,plain,
    ( r1_tarski(k4_xboole_0(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19501,c_5007])).

cnf(c_20803,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20793,c_3])).

cnf(c_10,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_881,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_882,plain,
    ( k1_tops_1(sK0,X0) != k1_xboole_0
    | v2_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_881])).

cnf(c_884,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_12,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19,plain,
    ( v2_tops_1(sK1,sK0) != iProver_top
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_17,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20803,c_19501,c_884,c_19,c_17,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:02:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.72/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/1.49  
% 7.72/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.72/1.49  
% 7.72/1.49  ------  iProver source info
% 7.72/1.49  
% 7.72/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.72/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.72/1.49  git: non_committed_changes: false
% 7.72/1.49  git: last_make_outside_of_git: false
% 7.72/1.49  
% 7.72/1.49  ------ 
% 7.72/1.49  ------ Parsing...
% 7.72/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.72/1.49  
% 7.72/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.72/1.49  ------ Proving...
% 7.72/1.49  ------ Problem Properties 
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  clauses                                 16
% 7.72/1.49  conjectures                             4
% 7.72/1.49  EPR                                     2
% 7.72/1.49  Horn                                    15
% 7.72/1.49  unary                                   5
% 7.72/1.49  binary                                  5
% 7.72/1.49  lits                                    35
% 7.72/1.49  lits eq                                 9
% 7.72/1.49  fd_pure                                 0
% 7.72/1.49  fd_pseudo                               0
% 7.72/1.49  fd_cond                                 1
% 7.72/1.49  fd_pseudo_cond                          0
% 7.72/1.49  AC symbols                              0
% 7.72/1.49  
% 7.72/1.49  ------ Input Options Time Limit: Unbounded
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  ------ 
% 7.72/1.49  Current options:
% 7.72/1.49  ------ 
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  ------ Proving...
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  % SZS status Theorem for theBenchmark.p
% 7.72/1.49  
% 7.72/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.72/1.49  
% 7.72/1.49  fof(f13,conjecture,(
% 7.72/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f14,negated_conjecture,(
% 7.72/1.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 7.72/1.49    inference(negated_conjecture,[],[f13])).
% 7.72/1.49  
% 7.72/1.49  fof(f24,plain,(
% 7.72/1.49    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.72/1.49    inference(ennf_transformation,[],[f14])).
% 7.72/1.49  
% 7.72/1.49  fof(f26,plain,(
% 7.72/1.49    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.72/1.49    inference(nnf_transformation,[],[f24])).
% 7.72/1.49  
% 7.72/1.49  fof(f27,plain,(
% 7.72/1.49    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.72/1.49    inference(flattening,[],[f26])).
% 7.72/1.49  
% 7.72/1.49  fof(f29,plain,(
% 7.72/1.49    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~r1_tarski(sK1,k2_tops_1(X0,sK1)) | ~v2_tops_1(sK1,X0)) & (r1_tarski(sK1,k2_tops_1(X0,sK1)) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.72/1.49    introduced(choice_axiom,[])).
% 7.72/1.49  
% 7.72/1.49  fof(f28,plain,(
% 7.72/1.49    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 7.72/1.49    introduced(choice_axiom,[])).
% 7.72/1.49  
% 7.72/1.49  fof(f30,plain,(
% 7.72/1.49    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 7.72/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).
% 7.72/1.49  
% 7.72/1.49  fof(f45,plain,(
% 7.72/1.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.72/1.49    inference(cnf_transformation,[],[f30])).
% 7.72/1.49  
% 7.72/1.49  fof(f11,axiom,(
% 7.72/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f22,plain,(
% 7.72/1.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.72/1.49    inference(ennf_transformation,[],[f11])).
% 7.72/1.49  
% 7.72/1.49  fof(f41,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f22])).
% 7.72/1.49  
% 7.72/1.49  fof(f7,axiom,(
% 7.72/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f17,plain,(
% 7.72/1.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.72/1.49    inference(ennf_transformation,[],[f7])).
% 7.72/1.49  
% 7.72/1.49  fof(f37,plain,(
% 7.72/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.72/1.49    inference(cnf_transformation,[],[f17])).
% 7.72/1.49  
% 7.72/1.49  fof(f44,plain,(
% 7.72/1.49    l1_pre_topc(sK0)),
% 7.72/1.49    inference(cnf_transformation,[],[f30])).
% 7.72/1.49  
% 7.72/1.49  fof(f46,plain,(
% 7.72/1.49    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 7.72/1.49    inference(cnf_transformation,[],[f30])).
% 7.72/1.49  
% 7.72/1.49  fof(f2,axiom,(
% 7.72/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f15,plain,(
% 7.72/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.72/1.49    inference(ennf_transformation,[],[f2])).
% 7.72/1.49  
% 7.72/1.49  fof(f32,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f15])).
% 7.72/1.49  
% 7.72/1.49  fof(f6,axiom,(
% 7.72/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f36,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.72/1.49    inference(cnf_transformation,[],[f6])).
% 7.72/1.49  
% 7.72/1.49  fof(f49,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.72/1.49    inference(definition_unfolding,[],[f32,f36])).
% 7.72/1.49  
% 7.72/1.49  fof(f12,axiom,(
% 7.72/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f23,plain,(
% 7.72/1.49    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.72/1.49    inference(ennf_transformation,[],[f12])).
% 7.72/1.49  
% 7.72/1.49  fof(f25,plain,(
% 7.72/1.49    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.72/1.49    inference(nnf_transformation,[],[f23])).
% 7.72/1.49  
% 7.72/1.49  fof(f42,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f25])).
% 7.72/1.49  
% 7.72/1.49  fof(f3,axiom,(
% 7.72/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f33,plain,(
% 7.72/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f3])).
% 7.72/1.49  
% 7.72/1.49  fof(f1,axiom,(
% 7.72/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f31,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f1])).
% 7.72/1.49  
% 7.72/1.49  fof(f48,plain,(
% 7.72/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.72/1.49    inference(definition_unfolding,[],[f31,f36,f36])).
% 7.72/1.49  
% 7.72/1.49  fof(f5,axiom,(
% 7.72/1.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f16,plain,(
% 7.72/1.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 7.72/1.49    inference(ennf_transformation,[],[f5])).
% 7.72/1.49  
% 7.72/1.49  fof(f35,plain,(
% 7.72/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f16])).
% 7.72/1.49  
% 7.72/1.49  fof(f4,axiom,(
% 7.72/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.72/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.72/1.49  
% 7.72/1.49  fof(f34,plain,(
% 7.72/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.72/1.49    inference(cnf_transformation,[],[f4])).
% 7.72/1.49  
% 7.72/1.49  fof(f43,plain,(
% 7.72/1.49    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.72/1.49    inference(cnf_transformation,[],[f25])).
% 7.72/1.49  
% 7.72/1.49  fof(f47,plain,(
% 7.72/1.49    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 7.72/1.49    inference(cnf_transformation,[],[f30])).
% 7.72/1.49  
% 7.72/1.49  cnf(c_14,negated_conjecture,
% 7.72/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.72/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_537,plain,
% 7.72/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_9,plain,
% 7.72/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.72/1.49      | ~ l1_pre_topc(X1)
% 7.72/1.49      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 7.72/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_542,plain,
% 7.72/1.49      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 7.72/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.72/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4972,plain,
% 7.72/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 7.72/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_537,c_542]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_5,plain,
% 7.72/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.72/1.49      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.72/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_546,plain,
% 7.72/1.49      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 7.72/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1618,plain,
% 7.72/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_537,c_546]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4975,plain,
% 7.72/1.49      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 7.72/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_4972,c_1618]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_15,negated_conjecture,
% 7.72/1.49      ( l1_pre_topc(sK0) ),
% 7.72/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_16,plain,
% 7.72/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4989,plain,
% 7.72/1.49      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 7.72/1.49      inference(global_propositional_subsumption,
% 7.72/1.49                [status(thm)],
% 7.72/1.49                [c_4975,c_16]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_13,negated_conjecture,
% 7.72/1.49      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 7.72/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_538,plain,
% 7.72/1.49      ( v2_tops_1(sK1,sK0) = iProver_top
% 7.72/1.49      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1,plain,
% 7.72/1.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.72/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_549,plain,
% 7.72/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.72/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1588,plain,
% 7.72/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = sK1
% 7.72/1.49      | v2_tops_1(sK1,sK0) = iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_538,c_549]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4992,plain,
% 7.72/1.49      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1
% 7.72/1.49      | v2_tops_1(sK1,sK0) = iProver_top ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_4989,c_1588]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_11,plain,
% 7.72/1.49      ( ~ v2_tops_1(X0,X1)
% 7.72/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.72/1.49      | ~ l1_pre_topc(X1)
% 7.72/1.49      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 7.72/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_540,plain,
% 7.72/1.49      ( k1_tops_1(X0,X1) = k1_xboole_0
% 7.72/1.49      | v2_tops_1(X1,X0) != iProver_top
% 7.72/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.72/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_6255,plain,
% 7.72/1.49      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 7.72/1.49      | v2_tops_1(sK1,sK0) != iProver_top
% 7.72/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_537,c_540]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_6685,plain,
% 7.72/1.49      ( v2_tops_1(sK1,sK0) != iProver_top
% 7.72/1.49      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 7.72/1.49      inference(global_propositional_subsumption,
% 7.72/1.49                [status(thm)],
% 7.72/1.49                [c_6255,c_16]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_6686,plain,
% 7.72/1.49      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 7.72/1.49      | v2_tops_1(sK1,sK0) != iProver_top ),
% 7.72/1.49      inference(renaming,[status(thm)],[c_6685]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_6691,plain,
% 7.72/1.49      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 7.72/1.49      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = sK1 ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_4992,c_6686]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_2,plain,
% 7.72/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.72/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_548,plain,
% 7.72/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_5008,plain,
% 7.72/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_4989,c_548]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_5282,plain,
% 7.72/1.49      ( k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k1_tops_1(sK0,sK1),sK1)) = k1_tops_1(sK0,sK1) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_5008,c_549]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_0,plain,
% 7.72/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.72/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_18256,plain,
% 7.72/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_5282,c_0]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19334,plain,
% 7.72/1.49      ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,sK1)
% 7.72/1.49      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_6691,c_18256]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_977,plain,
% 7.72/1.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_0,c_548]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_4,plain,
% 7.72/1.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 7.72/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_547,plain,
% 7.72/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1157,plain,
% 7.72/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_977,c_547]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_3,plain,
% 7.72/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.72/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_1159,plain,
% 7.72/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.72/1.49      inference(light_normalisation,[status(thm)],[c_1157,c_3]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19501,plain,
% 7.72/1.49      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_19334,c_1159]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_5007,plain,
% 7.72/1.49      ( r1_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
% 7.72/1.49      inference(superposition,[status(thm)],[c_4989,c_977]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_20793,plain,
% 7.72/1.49      ( r1_tarski(k4_xboole_0(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) = iProver_top ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_19501,c_5007]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_20803,plain,
% 7.72/1.49      ( r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 7.72/1.49      inference(demodulation,[status(thm)],[c_20793,c_3]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_10,plain,
% 7.72/1.49      ( v2_tops_1(X0,X1)
% 7.72/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.72/1.49      | ~ l1_pre_topc(X1)
% 7.72/1.49      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 7.72/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_881,plain,
% 7.72/1.49      ( v2_tops_1(X0,sK0)
% 7.72/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.72/1.49      | ~ l1_pre_topc(sK0)
% 7.72/1.49      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 7.72/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_882,plain,
% 7.72/1.49      ( k1_tops_1(sK0,X0) != k1_xboole_0
% 7.72/1.49      | v2_tops_1(X0,sK0) = iProver_top
% 7.72/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.72/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_881]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_884,plain,
% 7.72/1.49      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 7.72/1.49      | v2_tops_1(sK1,sK0) = iProver_top
% 7.72/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.72/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.72/1.49      inference(instantiation,[status(thm)],[c_882]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_12,negated_conjecture,
% 7.72/1.49      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 7.72/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_19,plain,
% 7.72/1.49      ( v2_tops_1(sK1,sK0) != iProver_top
% 7.72/1.49      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) != iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(c_17,plain,
% 7.72/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.72/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.72/1.49  
% 7.72/1.49  cnf(contradiction,plain,
% 7.72/1.49      ( $false ),
% 7.72/1.49      inference(minisat,
% 7.72/1.49                [status(thm)],
% 7.72/1.49                [c_20803,c_19501,c_884,c_19,c_17,c_16]) ).
% 7.72/1.49  
% 7.72/1.49  
% 7.72/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.72/1.49  
% 7.72/1.49  ------                               Statistics
% 7.72/1.49  
% 7.72/1.49  ------ Selected
% 7.72/1.49  
% 7.72/1.49  total_time:                             0.701
% 7.72/1.49  
%------------------------------------------------------------------------------
