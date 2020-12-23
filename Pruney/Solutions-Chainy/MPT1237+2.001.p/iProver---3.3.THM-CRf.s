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
% DateTime   : Thu Dec  3 12:13:46 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 275 expanded)
%              Number of clauses        :   73 ( 107 expanded)
%              Number of leaves         :   13 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  314 (1102 expanded)
%              Number of equality atoms :   92 ( 118 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X1,X2)
                 => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,sK2))
        & r1_tarski(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(X0,sK1),k1_tops_1(X0,X2))
            & r1_tarski(sK1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20,f19,f18])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_10,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_135,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_136,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_135])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_136])).

cnf(c_461,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_250])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_252,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_459,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_123,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_124,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_123])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_39))) = k1_tops_1(sK0,X0_39) ),
    inference(subtyping,[status(esa)],[c_124])).

cnf(c_460,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_39))) = k1_tops_1(sK0,X0_39)
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_673,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_459,c_460])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_257,plain,
    ( r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(k3_subset_1(X0_42,X1_39),k3_subset_1(X0_42,X0_39))
    | ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_42))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_454,plain,
    ( r1_tarski(X0_39,X1_39) = iProver_top
    | r1_tarski(k3_subset_1(X0_42,X1_39),k3_subset_1(X0_42,X0_39)) != iProver_top
    | m1_subset_1(X0_39,k1_zfmisc_1(X0_42)) != iProver_top
    | m1_subset_1(X1_39,k1_zfmisc_1(X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_257])).

cnf(c_843,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0_39) = iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_39),k1_tops_1(sK0,sK1)) != iProver_top
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_454])).

cnf(c_12,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_266,plain,
    ( X0_39 != X1_39
    | k1_tops_1(X0_40,X0_39) = k1_tops_1(X0_40,X1_39) ),
    theory(equality)).

cnf(c_271,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_260,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_273,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_288,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_535,plain,
    ( k1_tops_1(sK0,sK2) = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_261,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_517,plain,
    ( X0_39 != X1_39
    | k1_tops_1(sK0,sK2) != X1_39
    | k1_tops_1(sK0,sK2) = X0_39 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_545,plain,
    ( X0_39 != k1_tops_1(sK0,sK2)
    | k1_tops_1(sK0,sK2) = X0_39
    | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_649,plain,
    ( k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2)
    | k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_650,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_42))
    | m1_subset_1(k3_subset_1(X0_42,X0_39),k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_703,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_704,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_39),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_706,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_555,plain,
    ( X0_39 != X1_39
    | k1_tops_1(sK0,sK1) != X1_39
    | k1_tops_1(sK0,sK1) = X0_39 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_693,plain,
    ( X0_39 != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = X0_39
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_895,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_693])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_256,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(k3_subset_1(X0_42,X1_39),k3_subset_1(X0_42,X0_39))
    | ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_42))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_621,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_39),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ r1_tarski(sK1,X0_39)
    | ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_909,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_910,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_909])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(X2,X0),k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_147,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(X2,X0),k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_148,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_249,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(k2_pre_topc(sK0,X0_39),k2_pre_topc(sK0,X1_39))
    | ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_148])).

cnf(c_495,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(X0_42,X0_39)),k2_pre_topc(sK0,k3_subset_1(X0_42,X1_39)))
    | ~ r1_tarski(k3_subset_1(X0_42,X0_39),k3_subset_1(X0_42,X1_39))
    | ~ m1_subset_1(k3_subset_1(X0_42,X0_39),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(X0_42,X1_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_559,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_39)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1_39)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_39),k3_subset_1(u1_struct_0(sK0),X1_39))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_39),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X1_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_1183,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_1184,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1183])).

cnf(c_264,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(X2_39,X3_39)
    | X2_39 != X0_39
    | X3_39 != X1_39 ),
    theory(equality)).

cnf(c_485,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,sK2) != X1_39
    | k1_tops_1(sK0,sK1) != X0_39 ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_858,plain,
    ( ~ r1_tarski(X0_39,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,sK2) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | k1_tops_1(sK0,sK1) != X0_39 ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_1290,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))))
    | k1_tops_1(sK0,sK2) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_1291,plain,
    ( k1_tops_1(sK0,sK2) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1290])).

cnf(c_1339,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_1340,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1339])).

cnf(c_1000,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),X1_39),k3_subset_1(u1_struct_0(sK0),X0_39))
    | ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_2077,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_2086,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2077])).

cnf(c_2627,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_2628,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2627])).

cnf(c_3539,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_843,c_9,c_12,c_8,c_13,c_14,c_15,c_271,c_273,c_288,c_535,c_649,c_650,c_706,c_895,c_910,c_1184,c_1291,c_1340,c_2086,c_2628])).

cnf(c_3543,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_461,c_3539])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3543,c_706,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 17:39:44 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.53/0.91  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/0.91  
% 3.53/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/0.91  
% 3.53/0.91  ------  iProver source info
% 3.53/0.91  
% 3.53/0.91  git: date: 2020-06-30 10:37:57 +0100
% 3.53/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/0.91  git: non_committed_changes: false
% 3.53/0.91  git: last_make_outside_of_git: false
% 3.53/0.91  
% 3.53/0.91  ------ 
% 3.53/0.91  
% 3.53/0.91  ------ Input Options
% 3.53/0.91  
% 3.53/0.91  --out_options                           all
% 3.53/0.91  --tptp_safe_out                         true
% 3.53/0.91  --problem_path                          ""
% 3.53/0.91  --include_path                          ""
% 3.53/0.91  --clausifier                            res/vclausify_rel
% 3.53/0.91  --clausifier_options                    ""
% 3.53/0.91  --stdin                                 false
% 3.53/0.91  --stats_out                             all
% 3.53/0.91  
% 3.53/0.91  ------ General Options
% 3.53/0.91  
% 3.53/0.91  --fof                                   false
% 3.53/0.91  --time_out_real                         305.
% 3.53/0.91  --time_out_virtual                      -1.
% 3.53/0.91  --symbol_type_check                     false
% 3.53/0.91  --clausify_out                          false
% 3.53/0.91  --sig_cnt_out                           false
% 3.53/0.91  --trig_cnt_out                          false
% 3.53/0.91  --trig_cnt_out_tolerance                1.
% 3.53/0.91  --trig_cnt_out_sk_spl                   false
% 3.53/0.91  --abstr_cl_out                          false
% 3.53/0.91  
% 3.53/0.91  ------ Global Options
% 3.53/0.91  
% 3.53/0.91  --schedule                              default
% 3.53/0.91  --add_important_lit                     false
% 3.53/0.91  --prop_solver_per_cl                    1000
% 3.53/0.91  --min_unsat_core                        false
% 3.53/0.91  --soft_assumptions                      false
% 3.53/0.91  --soft_lemma_size                       3
% 3.53/0.91  --prop_impl_unit_size                   0
% 3.53/0.91  --prop_impl_unit                        []
% 3.53/0.91  --share_sel_clauses                     true
% 3.53/0.91  --reset_solvers                         false
% 3.53/0.91  --bc_imp_inh                            [conj_cone]
% 3.53/0.91  --conj_cone_tolerance                   3.
% 3.53/0.91  --extra_neg_conj                        none
% 3.53/0.91  --large_theory_mode                     true
% 3.53/0.91  --prolific_symb_bound                   200
% 3.53/0.91  --lt_threshold                          2000
% 3.53/0.91  --clause_weak_htbl                      true
% 3.53/0.91  --gc_record_bc_elim                     false
% 3.53/0.91  
% 3.53/0.91  ------ Preprocessing Options
% 3.53/0.91  
% 3.53/0.91  --preprocessing_flag                    true
% 3.53/0.91  --time_out_prep_mult                    0.1
% 3.53/0.91  --splitting_mode                        input
% 3.53/0.91  --splitting_grd                         true
% 3.53/0.91  --splitting_cvd                         false
% 3.53/0.91  --splitting_cvd_svl                     false
% 3.53/0.91  --splitting_nvd                         32
% 3.53/0.91  --sub_typing                            true
% 3.53/0.91  --prep_gs_sim                           true
% 3.53/0.91  --prep_unflatten                        true
% 3.53/0.91  --prep_res_sim                          true
% 3.53/0.91  --prep_upred                            true
% 3.53/0.91  --prep_sem_filter                       exhaustive
% 3.53/0.91  --prep_sem_filter_out                   false
% 3.53/0.91  --pred_elim                             true
% 3.53/0.91  --res_sim_input                         true
% 3.53/0.91  --eq_ax_congr_red                       true
% 3.53/0.91  --pure_diseq_elim                       true
% 3.53/0.91  --brand_transform                       false
% 3.53/0.91  --non_eq_to_eq                          false
% 3.53/0.91  --prep_def_merge                        true
% 3.53/0.91  --prep_def_merge_prop_impl              false
% 3.53/0.91  --prep_def_merge_mbd                    true
% 3.53/0.91  --prep_def_merge_tr_red                 false
% 3.53/0.91  --prep_def_merge_tr_cl                  false
% 3.53/0.91  --smt_preprocessing                     true
% 3.53/0.91  --smt_ac_axioms                         fast
% 3.53/0.91  --preprocessed_out                      false
% 3.53/0.91  --preprocessed_stats                    false
% 3.53/0.91  
% 3.53/0.91  ------ Abstraction refinement Options
% 3.53/0.91  
% 3.53/0.91  --abstr_ref                             []
% 3.53/0.91  --abstr_ref_prep                        false
% 3.53/0.91  --abstr_ref_until_sat                   false
% 3.53/0.91  --abstr_ref_sig_restrict                funpre
% 3.53/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.91  --abstr_ref_under                       []
% 3.53/0.91  
% 3.53/0.91  ------ SAT Options
% 3.53/0.91  
% 3.53/0.91  --sat_mode                              false
% 3.53/0.91  --sat_fm_restart_options                ""
% 3.53/0.91  --sat_gr_def                            false
% 3.53/0.91  --sat_epr_types                         true
% 3.53/0.91  --sat_non_cyclic_types                  false
% 3.53/0.91  --sat_finite_models                     false
% 3.53/0.91  --sat_fm_lemmas                         false
% 3.53/0.91  --sat_fm_prep                           false
% 3.53/0.91  --sat_fm_uc_incr                        true
% 3.53/0.91  --sat_out_model                         small
% 3.53/0.91  --sat_out_clauses                       false
% 3.53/0.91  
% 3.53/0.91  ------ QBF Options
% 3.53/0.91  
% 3.53/0.91  --qbf_mode                              false
% 3.53/0.91  --qbf_elim_univ                         false
% 3.53/0.91  --qbf_dom_inst                          none
% 3.53/0.91  --qbf_dom_pre_inst                      false
% 3.53/0.91  --qbf_sk_in                             false
% 3.53/0.91  --qbf_pred_elim                         true
% 3.53/0.91  --qbf_split                             512
% 3.53/0.91  
% 3.53/0.91  ------ BMC1 Options
% 3.53/0.91  
% 3.53/0.91  --bmc1_incremental                      false
% 3.53/0.91  --bmc1_axioms                           reachable_all
% 3.53/0.91  --bmc1_min_bound                        0
% 3.53/0.91  --bmc1_max_bound                        -1
% 3.53/0.91  --bmc1_max_bound_default                -1
% 3.53/0.91  --bmc1_symbol_reachability              true
% 3.53/0.91  --bmc1_property_lemmas                  false
% 3.53/0.91  --bmc1_k_induction                      false
% 3.53/0.91  --bmc1_non_equiv_states                 false
% 3.53/0.91  --bmc1_deadlock                         false
% 3.53/0.91  --bmc1_ucm                              false
% 3.53/0.91  --bmc1_add_unsat_core                   none
% 3.53/0.91  --bmc1_unsat_core_children              false
% 3.53/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.91  --bmc1_out_stat                         full
% 3.53/0.91  --bmc1_ground_init                      false
% 3.53/0.91  --bmc1_pre_inst_next_state              false
% 3.53/0.91  --bmc1_pre_inst_state                   false
% 3.53/0.91  --bmc1_pre_inst_reach_state             false
% 3.53/0.91  --bmc1_out_unsat_core                   false
% 3.53/0.91  --bmc1_aig_witness_out                  false
% 3.53/0.91  --bmc1_verbose                          false
% 3.53/0.91  --bmc1_dump_clauses_tptp                false
% 3.53/0.91  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.91  --bmc1_dump_file                        -
% 3.53/0.91  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.91  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.91  --bmc1_ucm_extend_mode                  1
% 3.53/0.91  --bmc1_ucm_init_mode                    2
% 3.53/0.91  --bmc1_ucm_cone_mode                    none
% 3.53/0.91  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.91  --bmc1_ucm_relax_model                  4
% 3.53/0.91  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.91  --bmc1_ucm_layered_model                none
% 3.53/0.91  --bmc1_ucm_max_lemma_size               10
% 3.53/0.91  
% 3.53/0.91  ------ AIG Options
% 3.53/0.91  
% 3.53/0.91  --aig_mode                              false
% 3.53/0.91  
% 3.53/0.91  ------ Instantiation Options
% 3.53/0.91  
% 3.53/0.91  --instantiation_flag                    true
% 3.53/0.91  --inst_sos_flag                         true
% 3.53/0.91  --inst_sos_phase                        true
% 3.53/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.91  --inst_lit_sel_side                     num_symb
% 3.53/0.91  --inst_solver_per_active                1400
% 3.53/0.91  --inst_solver_calls_frac                1.
% 3.53/0.91  --inst_passive_queue_type               priority_queues
% 3.53/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.91  --inst_passive_queues_freq              [25;2]
% 3.53/0.91  --inst_dismatching                      true
% 3.53/0.91  --inst_eager_unprocessed_to_passive     true
% 3.53/0.91  --inst_prop_sim_given                   true
% 3.53/0.91  --inst_prop_sim_new                     false
% 3.53/0.91  --inst_subs_new                         false
% 3.53/0.91  --inst_eq_res_simp                      false
% 3.53/0.91  --inst_subs_given                       false
% 3.53/0.91  --inst_orphan_elimination               true
% 3.53/0.91  --inst_learning_loop_flag               true
% 3.53/0.91  --inst_learning_start                   3000
% 3.53/0.91  --inst_learning_factor                  2
% 3.53/0.91  --inst_start_prop_sim_after_learn       3
% 3.53/0.91  --inst_sel_renew                        solver
% 3.53/0.91  --inst_lit_activity_flag                true
% 3.53/0.91  --inst_restr_to_given                   false
% 3.53/0.91  --inst_activity_threshold               500
% 3.53/0.91  --inst_out_proof                        true
% 3.53/0.91  
% 3.53/0.91  ------ Resolution Options
% 3.53/0.91  
% 3.53/0.91  --resolution_flag                       true
% 3.53/0.91  --res_lit_sel                           adaptive
% 3.53/0.91  --res_lit_sel_side                      none
% 3.53/0.91  --res_ordering                          kbo
% 3.53/0.91  --res_to_prop_solver                    active
% 3.53/0.91  --res_prop_simpl_new                    false
% 3.53/0.91  --res_prop_simpl_given                  true
% 3.53/0.91  --res_passive_queue_type                priority_queues
% 3.53/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.91  --res_passive_queues_freq               [15;5]
% 3.53/0.91  --res_forward_subs                      full
% 3.53/0.91  --res_backward_subs                     full
% 3.53/0.91  --res_forward_subs_resolution           true
% 3.53/0.91  --res_backward_subs_resolution          true
% 3.53/0.91  --res_orphan_elimination                true
% 3.53/0.91  --res_time_limit                        2.
% 3.53/0.91  --res_out_proof                         true
% 3.53/0.91  
% 3.53/0.91  ------ Superposition Options
% 3.53/0.91  
% 3.53/0.91  --superposition_flag                    true
% 3.53/0.91  --sup_passive_queue_type                priority_queues
% 3.53/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.91  --sup_passive_queues_freq               [8;1;4]
% 3.53/0.91  --demod_completeness_check              fast
% 3.53/0.91  --demod_use_ground                      true
% 3.53/0.91  --sup_to_prop_solver                    passive
% 3.53/0.91  --sup_prop_simpl_new                    true
% 3.53/0.91  --sup_prop_simpl_given                  true
% 3.53/0.91  --sup_fun_splitting                     true
% 3.53/0.91  --sup_smt_interval                      50000
% 3.53/0.91  
% 3.53/0.91  ------ Superposition Simplification Setup
% 3.53/0.91  
% 3.53/0.91  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.53/0.91  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.53/0.91  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.53/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.53/0.91  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.53/0.91  --sup_immed_triv                        [TrivRules]
% 3.53/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.91  --sup_immed_bw_main                     []
% 3.53/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.53/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.91  --sup_input_bw                          []
% 3.53/0.91  
% 3.53/0.91  ------ Combination Options
% 3.53/0.91  
% 3.53/0.91  --comb_res_mult                         3
% 3.53/0.91  --comb_sup_mult                         2
% 3.53/0.91  --comb_inst_mult                        10
% 3.53/0.91  
% 3.53/0.91  ------ Debug Options
% 3.53/0.91  
% 3.53/0.91  --dbg_backtrace                         false
% 3.53/0.91  --dbg_dump_prop_clauses                 false
% 3.53/0.91  --dbg_dump_prop_clauses_file            -
% 3.53/0.91  --dbg_out_stat                          false
% 3.53/0.91  ------ Parsing...
% 3.53/0.91  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/0.91  
% 3.53/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.53/0.91  
% 3.53/0.91  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/0.91  
% 3.53/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.91  ------ Proving...
% 3.53/0.91  ------ Problem Properties 
% 3.53/0.91  
% 3.53/0.91  
% 3.53/0.91  clauses                                 10
% 3.53/0.91  conjectures                             4
% 3.53/0.91  EPR                                     1
% 3.53/0.91  Horn                                    10
% 3.53/0.91  unary                                   4
% 3.53/0.91  binary                                  3
% 3.53/0.91  lits                                    22
% 3.53/0.91  lits eq                                 1
% 3.53/0.91  fd_pure                                 0
% 3.53/0.91  fd_pseudo                               0
% 3.53/0.91  fd_cond                                 0
% 3.53/0.91  fd_pseudo_cond                          0
% 3.53/0.91  AC symbols                              0
% 3.53/0.91  
% 3.53/0.91  ------ Schedule dynamic 5 is on 
% 3.53/0.91  
% 3.53/0.91  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.53/0.91  
% 3.53/0.91  
% 3.53/0.91  ------ 
% 3.53/0.91  Current options:
% 3.53/0.91  ------ 
% 3.53/0.91  
% 3.53/0.91  ------ Input Options
% 3.53/0.91  
% 3.53/0.91  --out_options                           all
% 3.53/0.91  --tptp_safe_out                         true
% 3.53/0.91  --problem_path                          ""
% 3.53/0.91  --include_path                          ""
% 3.53/0.91  --clausifier                            res/vclausify_rel
% 3.53/0.91  --clausifier_options                    ""
% 3.53/0.91  --stdin                                 false
% 3.53/0.91  --stats_out                             all
% 3.53/0.91  
% 3.53/0.91  ------ General Options
% 3.53/0.91  
% 3.53/0.91  --fof                                   false
% 3.53/0.91  --time_out_real                         305.
% 3.53/0.91  --time_out_virtual                      -1.
% 3.53/0.91  --symbol_type_check                     false
% 3.53/0.91  --clausify_out                          false
% 3.53/0.91  --sig_cnt_out                           false
% 3.53/0.91  --trig_cnt_out                          false
% 3.53/0.91  --trig_cnt_out_tolerance                1.
% 3.53/0.91  --trig_cnt_out_sk_spl                   false
% 3.53/0.91  --abstr_cl_out                          false
% 3.53/0.91  
% 3.53/0.91  ------ Global Options
% 3.53/0.91  
% 3.53/0.91  --schedule                              default
% 3.53/0.91  --add_important_lit                     false
% 3.53/0.91  --prop_solver_per_cl                    1000
% 3.53/0.91  --min_unsat_core                        false
% 3.53/0.91  --soft_assumptions                      false
% 3.53/0.91  --soft_lemma_size                       3
% 3.53/0.91  --prop_impl_unit_size                   0
% 3.53/0.91  --prop_impl_unit                        []
% 3.53/0.91  --share_sel_clauses                     true
% 3.53/0.91  --reset_solvers                         false
% 3.53/0.91  --bc_imp_inh                            [conj_cone]
% 3.53/0.91  --conj_cone_tolerance                   3.
% 3.53/0.91  --extra_neg_conj                        none
% 3.53/0.91  --large_theory_mode                     true
% 3.53/0.91  --prolific_symb_bound                   200
% 3.53/0.91  --lt_threshold                          2000
% 3.53/0.91  --clause_weak_htbl                      true
% 3.53/0.91  --gc_record_bc_elim                     false
% 3.53/0.91  
% 3.53/0.91  ------ Preprocessing Options
% 3.53/0.91  
% 3.53/0.91  --preprocessing_flag                    true
% 3.53/0.91  --time_out_prep_mult                    0.1
% 3.53/0.91  --splitting_mode                        input
% 3.53/0.91  --splitting_grd                         true
% 3.53/0.91  --splitting_cvd                         false
% 3.53/0.91  --splitting_cvd_svl                     false
% 3.53/0.91  --splitting_nvd                         32
% 3.53/0.91  --sub_typing                            true
% 3.53/0.91  --prep_gs_sim                           true
% 3.53/0.91  --prep_unflatten                        true
% 3.53/0.91  --prep_res_sim                          true
% 3.53/0.91  --prep_upred                            true
% 3.53/0.91  --prep_sem_filter                       exhaustive
% 3.53/0.91  --prep_sem_filter_out                   false
% 3.53/0.91  --pred_elim                             true
% 3.53/0.91  --res_sim_input                         true
% 3.53/0.91  --eq_ax_congr_red                       true
% 3.53/0.91  --pure_diseq_elim                       true
% 3.53/0.91  --brand_transform                       false
% 3.53/0.91  --non_eq_to_eq                          false
% 3.53/0.91  --prep_def_merge                        true
% 3.53/0.91  --prep_def_merge_prop_impl              false
% 3.53/0.91  --prep_def_merge_mbd                    true
% 3.53/0.91  --prep_def_merge_tr_red                 false
% 3.53/0.91  --prep_def_merge_tr_cl                  false
% 3.53/0.91  --smt_preprocessing                     true
% 3.53/0.91  --smt_ac_axioms                         fast
% 3.53/0.91  --preprocessed_out                      false
% 3.53/0.91  --preprocessed_stats                    false
% 3.53/0.91  
% 3.53/0.91  ------ Abstraction refinement Options
% 3.53/0.91  
% 3.53/0.91  --abstr_ref                             []
% 3.53/0.91  --abstr_ref_prep                        false
% 3.53/0.91  --abstr_ref_until_sat                   false
% 3.53/0.91  --abstr_ref_sig_restrict                funpre
% 3.53/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.91  --abstr_ref_under                       []
% 3.53/0.91  
% 3.53/0.91  ------ SAT Options
% 3.53/0.91  
% 3.53/0.91  --sat_mode                              false
% 3.53/0.91  --sat_fm_restart_options                ""
% 3.53/0.91  --sat_gr_def                            false
% 3.53/0.91  --sat_epr_types                         true
% 3.53/0.91  --sat_non_cyclic_types                  false
% 3.53/0.91  --sat_finite_models                     false
% 3.53/0.91  --sat_fm_lemmas                         false
% 3.53/0.91  --sat_fm_prep                           false
% 3.53/0.91  --sat_fm_uc_incr                        true
% 3.53/0.91  --sat_out_model                         small
% 3.53/0.91  --sat_out_clauses                       false
% 3.53/0.91  
% 3.53/0.91  ------ QBF Options
% 3.53/0.91  
% 3.53/0.91  --qbf_mode                              false
% 3.53/0.91  --qbf_elim_univ                         false
% 3.53/0.91  --qbf_dom_inst                          none
% 3.53/0.91  --qbf_dom_pre_inst                      false
% 3.53/0.91  --qbf_sk_in                             false
% 3.53/0.91  --qbf_pred_elim                         true
% 3.53/0.91  --qbf_split                             512
% 3.53/0.91  
% 3.53/0.91  ------ BMC1 Options
% 3.53/0.91  
% 3.53/0.91  --bmc1_incremental                      false
% 3.53/0.91  --bmc1_axioms                           reachable_all
% 3.53/0.91  --bmc1_min_bound                        0
% 3.53/0.91  --bmc1_max_bound                        -1
% 3.53/0.91  --bmc1_max_bound_default                -1
% 3.53/0.91  --bmc1_symbol_reachability              true
% 3.53/0.91  --bmc1_property_lemmas                  false
% 3.53/0.91  --bmc1_k_induction                      false
% 3.53/0.91  --bmc1_non_equiv_states                 false
% 3.53/0.91  --bmc1_deadlock                         false
% 3.53/0.91  --bmc1_ucm                              false
% 3.53/0.91  --bmc1_add_unsat_core                   none
% 3.53/0.91  --bmc1_unsat_core_children              false
% 3.53/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.91  --bmc1_out_stat                         full
% 3.53/0.91  --bmc1_ground_init                      false
% 3.53/0.91  --bmc1_pre_inst_next_state              false
% 3.53/0.91  --bmc1_pre_inst_state                   false
% 3.53/0.91  --bmc1_pre_inst_reach_state             false
% 3.53/0.91  --bmc1_out_unsat_core                   false
% 3.53/0.91  --bmc1_aig_witness_out                  false
% 3.53/0.91  --bmc1_verbose                          false
% 3.53/0.91  --bmc1_dump_clauses_tptp                false
% 3.53/0.91  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.91  --bmc1_dump_file                        -
% 3.53/0.91  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.91  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.91  --bmc1_ucm_extend_mode                  1
% 3.53/0.91  --bmc1_ucm_init_mode                    2
% 3.53/0.91  --bmc1_ucm_cone_mode                    none
% 3.53/0.91  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.91  --bmc1_ucm_relax_model                  4
% 3.53/0.91  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.91  --bmc1_ucm_layered_model                none
% 3.53/0.91  --bmc1_ucm_max_lemma_size               10
% 3.53/0.91  
% 3.53/0.91  ------ AIG Options
% 3.53/0.91  
% 3.53/0.91  --aig_mode                              false
% 3.53/0.91  
% 3.53/0.91  ------ Instantiation Options
% 3.53/0.91  
% 3.53/0.91  --instantiation_flag                    true
% 3.53/0.91  --inst_sos_flag                         true
% 3.53/0.91  --inst_sos_phase                        true
% 3.53/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.91  --inst_lit_sel_side                     none
% 3.53/0.91  --inst_solver_per_active                1400
% 3.53/0.91  --inst_solver_calls_frac                1.
% 3.53/0.91  --inst_passive_queue_type               priority_queues
% 3.53/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.91  --inst_passive_queues_freq              [25;2]
% 3.53/0.91  --inst_dismatching                      true
% 3.53/0.91  --inst_eager_unprocessed_to_passive     true
% 3.53/0.91  --inst_prop_sim_given                   true
% 3.53/0.91  --inst_prop_sim_new                     false
% 3.53/0.91  --inst_subs_new                         false
% 3.53/0.91  --inst_eq_res_simp                      false
% 3.53/0.91  --inst_subs_given                       false
% 3.53/0.91  --inst_orphan_elimination               true
% 3.53/0.91  --inst_learning_loop_flag               true
% 3.53/0.91  --inst_learning_start                   3000
% 3.53/0.91  --inst_learning_factor                  2
% 3.53/0.91  --inst_start_prop_sim_after_learn       3
% 3.53/0.91  --inst_sel_renew                        solver
% 3.53/0.91  --inst_lit_activity_flag                true
% 3.53/0.91  --inst_restr_to_given                   false
% 3.53/0.91  --inst_activity_threshold               500
% 3.53/0.91  --inst_out_proof                        true
% 3.53/0.91  
% 3.53/0.91  ------ Resolution Options
% 3.53/0.91  
% 3.53/0.91  --resolution_flag                       false
% 3.53/0.91  --res_lit_sel                           adaptive
% 3.53/0.91  --res_lit_sel_side                      none
% 3.53/0.91  --res_ordering                          kbo
% 3.53/0.91  --res_to_prop_solver                    active
% 3.53/0.91  --res_prop_simpl_new                    false
% 3.53/0.91  --res_prop_simpl_given                  true
% 3.53/0.91  --res_passive_queue_type                priority_queues
% 3.53/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.91  --res_passive_queues_freq               [15;5]
% 3.53/0.91  --res_forward_subs                      full
% 3.53/0.91  --res_backward_subs                     full
% 3.53/0.91  --res_forward_subs_resolution           true
% 3.53/0.91  --res_backward_subs_resolution          true
% 3.53/0.91  --res_orphan_elimination                true
% 3.53/0.91  --res_time_limit                        2.
% 3.53/0.91  --res_out_proof                         true
% 3.53/0.91  
% 3.53/0.91  ------ Superposition Options
% 3.53/0.91  
% 3.53/0.91  --superposition_flag                    true
% 3.53/0.91  --sup_passive_queue_type                priority_queues
% 3.53/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.91  --sup_passive_queues_freq               [8;1;4]
% 3.53/0.91  --demod_completeness_check              fast
% 3.53/0.91  --demod_use_ground                      true
% 3.53/0.91  --sup_to_prop_solver                    passive
% 3.53/0.91  --sup_prop_simpl_new                    true
% 3.53/0.91  --sup_prop_simpl_given                  true
% 3.53/0.91  --sup_fun_splitting                     true
% 3.53/0.91  --sup_smt_interval                      50000
% 3.53/0.91  
% 3.53/0.91  ------ Superposition Simplification Setup
% 3.53/0.91  
% 3.53/0.91  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.53/0.91  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.53/0.91  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.53/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.53/0.91  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.53/0.91  --sup_immed_triv                        [TrivRules]
% 3.53/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.91  --sup_immed_bw_main                     []
% 3.53/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.53/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.91  --sup_input_bw                          []
% 3.53/0.91  
% 3.53/0.91  ------ Combination Options
% 3.53/0.91  
% 3.53/0.91  --comb_res_mult                         3
% 3.53/0.91  --comb_sup_mult                         2
% 3.53/0.91  --comb_inst_mult                        10
% 3.53/0.91  
% 3.53/0.91  ------ Debug Options
% 3.53/0.91  
% 3.53/0.91  --dbg_backtrace                         false
% 3.53/0.91  --dbg_dump_prop_clauses                 false
% 3.53/0.91  --dbg_dump_prop_clauses_file            -
% 3.53/0.91  --dbg_out_stat                          false
% 3.53/0.91  
% 3.53/0.91  
% 3.53/0.91  
% 3.53/0.91  
% 3.53/0.91  ------ Proving...
% 3.53/0.91  
% 3.53/0.91  
% 3.53/0.91  % SZS status Theorem for theBenchmark.p
% 3.53/0.91  
% 3.53/0.91  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/0.91  
% 3.53/0.91  fof(f3,axiom,(
% 3.53/0.91    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.53/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.91  
% 3.53/0.91  fof(f10,plain,(
% 3.53/0.91    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.53/0.91    inference(ennf_transformation,[],[f3])).
% 3.53/0.91  
% 3.53/0.91  fof(f11,plain,(
% 3.53/0.91    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.53/0.91    inference(flattening,[],[f10])).
% 3.53/0.91  
% 3.53/0.91  fof(f25,plain,(
% 3.53/0.91    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.53/0.91    inference(cnf_transformation,[],[f11])).
% 3.53/0.91  
% 3.53/0.91  fof(f6,conjecture,(
% 3.53/0.91    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.53/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.91  
% 3.53/0.91  fof(f7,negated_conjecture,(
% 3.53/0.91    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.53/0.91    inference(negated_conjecture,[],[f6])).
% 3.53/0.91  
% 3.53/0.91  fof(f15,plain,(
% 3.53/0.91    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.53/0.91    inference(ennf_transformation,[],[f7])).
% 3.53/0.91  
% 3.53/0.91  fof(f16,plain,(
% 3.53/0.91    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.53/0.91    inference(flattening,[],[f15])).
% 3.53/0.91  
% 3.53/0.91  fof(f20,plain,(
% 3.53/0.91    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,sK2)) & r1_tarski(X1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.53/0.91    introduced(choice_axiom,[])).
% 3.53/0.91  
% 3.53/0.91  fof(f19,plain,(
% 3.53/0.91    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k1_tops_1(X0,sK1),k1_tops_1(X0,X2)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.53/0.91    introduced(choice_axiom,[])).
% 3.53/0.91  
% 3.53/0.91  fof(f18,plain,(
% 3.53/0.91    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.53/0.91    introduced(choice_axiom,[])).
% 3.53/0.91  
% 3.53/0.91  fof(f21,plain,(
% 3.53/0.91    ((~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.53/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20,f19,f18])).
% 3.53/0.91  
% 3.53/0.91  fof(f28,plain,(
% 3.53/0.91    l1_pre_topc(sK0)),
% 3.53/0.91    inference(cnf_transformation,[],[f21])).
% 3.53/0.91  
% 3.53/0.91  fof(f29,plain,(
% 3.53/0.91    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.53/0.91    inference(cnf_transformation,[],[f21])).
% 3.53/0.91  
% 3.53/0.91  fof(f5,axiom,(
% 3.53/0.91    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.53/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.91  
% 3.53/0.91  fof(f14,plain,(
% 3.53/0.91    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.53/0.91    inference(ennf_transformation,[],[f5])).
% 3.53/0.91  
% 3.53/0.91  fof(f27,plain,(
% 3.53/0.91    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.53/0.91    inference(cnf_transformation,[],[f14])).
% 3.53/0.91  
% 3.53/0.91  fof(f2,axiom,(
% 3.53/0.91    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 3.53/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.91  
% 3.53/0.91  fof(f9,plain,(
% 3.53/0.91    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.53/0.91    inference(ennf_transformation,[],[f2])).
% 3.53/0.91  
% 3.53/0.91  fof(f17,plain,(
% 3.53/0.91    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.53/0.91    inference(nnf_transformation,[],[f9])).
% 3.53/0.91  
% 3.53/0.91  fof(f24,plain,(
% 3.53/0.91    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.53/0.91    inference(cnf_transformation,[],[f17])).
% 3.53/0.91  
% 3.53/0.91  fof(f30,plain,(
% 3.53/0.91    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.53/0.91    inference(cnf_transformation,[],[f21])).
% 3.53/0.91  
% 3.53/0.91  fof(f31,plain,(
% 3.53/0.91    r1_tarski(sK1,sK2)),
% 3.53/0.91    inference(cnf_transformation,[],[f21])).
% 3.53/0.91  
% 3.53/0.91  fof(f32,plain,(
% 3.53/0.91    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),
% 3.53/0.91    inference(cnf_transformation,[],[f21])).
% 3.53/0.91  
% 3.53/0.91  fof(f1,axiom,(
% 3.53/0.91    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.53/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.91  
% 3.53/0.91  fof(f8,plain,(
% 3.53/0.91    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.53/0.91    inference(ennf_transformation,[],[f1])).
% 3.53/0.91  
% 3.53/0.91  fof(f22,plain,(
% 3.53/0.91    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.53/0.91    inference(cnf_transformation,[],[f8])).
% 3.53/0.91  
% 3.53/0.91  fof(f23,plain,(
% 3.53/0.91    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.53/0.91    inference(cnf_transformation,[],[f17])).
% 3.53/0.91  
% 3.53/0.91  fof(f4,axiom,(
% 3.53/0.91    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 3.53/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.53/0.91  
% 3.53/0.91  fof(f12,plain,(
% 3.53/0.91    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.53/0.91    inference(ennf_transformation,[],[f4])).
% 3.53/0.91  
% 3.53/0.91  fof(f13,plain,(
% 3.53/0.91    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.53/0.91    inference(flattening,[],[f12])).
% 3.53/0.91  
% 3.53/0.91  fof(f26,plain,(
% 3.53/0.91    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.53/0.91    inference(cnf_transformation,[],[f13])).
% 3.53/0.91  
% 3.53/0.91  cnf(c_3,plain,
% 3.53/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/0.91      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/0.91      | ~ l1_pre_topc(X1) ),
% 3.53/0.91      inference(cnf_transformation,[],[f25]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_10,negated_conjecture,
% 3.53/0.91      ( l1_pre_topc(sK0) ),
% 3.53/0.91      inference(cnf_transformation,[],[f28]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_135,plain,
% 3.53/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/0.91      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/0.91      | sK0 != X1 ),
% 3.53/0.91      inference(resolution_lifted,[status(thm)],[c_3,c_10]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_136,plain,
% 3.53/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.91      inference(unflattening,[status(thm)],[c_135]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_250,plain,
% 3.53/0.91      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.91      inference(subtyping,[status(esa)],[c_136]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_461,plain,
% 3.53/0.91      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.53/0.91      | m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.53/0.91      inference(predicate_to_equality,[status(thm)],[c_250]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_9,negated_conjecture,
% 3.53/0.91      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.91      inference(cnf_transformation,[],[f29]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_252,negated_conjecture,
% 3.53/0.91      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.91      inference(subtyping,[status(esa)],[c_9]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_459,plain,
% 3.53/0.91      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.53/0.91      inference(predicate_to_equality,[status(thm)],[c_252]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_5,plain,
% 3.53/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/0.91      | ~ l1_pre_topc(X1)
% 3.53/0.91      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.53/0.91      inference(cnf_transformation,[],[f27]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_123,plain,
% 3.53/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.53/0.91      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 3.53/0.91      | sK0 != X1 ),
% 3.53/0.91      inference(resolution_lifted,[status(thm)],[c_5,c_10]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_124,plain,
% 3.53/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 3.53/0.91      inference(unflattening,[status(thm)],[c_123]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_251,plain,
% 3.53/0.91      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_39))) = k1_tops_1(sK0,X0_39) ),
% 3.53/0.91      inference(subtyping,[status(esa)],[c_124]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_460,plain,
% 3.53/0.91      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_39))) = k1_tops_1(sK0,X0_39)
% 3.53/0.91      | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.53/0.91      inference(predicate_to_equality,[status(thm)],[c_251]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_673,plain,
% 3.53/0.91      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.53/0.91      inference(superposition,[status(thm)],[c_459,c_460]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_1,plain,
% 3.53/0.91      ( r1_tarski(X0,X1)
% 3.53/0.91      | ~ r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
% 3.53/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 3.53/0.91      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.53/0.91      inference(cnf_transformation,[],[f24]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_257,plain,
% 3.53/0.91      ( r1_tarski(X0_39,X1_39)
% 3.53/0.91      | ~ r1_tarski(k3_subset_1(X0_42,X1_39),k3_subset_1(X0_42,X0_39))
% 3.53/0.91      | ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_42))
% 3.53/0.91      | ~ m1_subset_1(X1_39,k1_zfmisc_1(X0_42)) ),
% 3.53/0.91      inference(subtyping,[status(esa)],[c_1]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_454,plain,
% 3.53/0.91      ( r1_tarski(X0_39,X1_39) = iProver_top
% 3.53/0.91      | r1_tarski(k3_subset_1(X0_42,X1_39),k3_subset_1(X0_42,X0_39)) != iProver_top
% 3.53/0.91      | m1_subset_1(X0_39,k1_zfmisc_1(X0_42)) != iProver_top
% 3.53/0.91      | m1_subset_1(X1_39,k1_zfmisc_1(X0_42)) != iProver_top ),
% 3.53/0.91      inference(predicate_to_equality,[status(thm)],[c_257]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_843,plain,
% 3.53/0.91      ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0_39) = iProver_top
% 3.53/0.91      | r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_39),k1_tops_1(sK0,sK1)) != iProver_top
% 3.53/0.91      | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.53/0.91      | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.53/0.91      inference(superposition,[status(thm)],[c_673,c_454]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_12,plain,
% 3.53/0.91      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.53/0.91      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_8,negated_conjecture,
% 3.53/0.91      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.91      inference(cnf_transformation,[],[f30]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_13,plain,
% 3.53/0.91      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.53/0.91      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_7,negated_conjecture,
% 3.53/0.91      ( r1_tarski(sK1,sK2) ),
% 3.53/0.91      inference(cnf_transformation,[],[f31]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_14,plain,
% 3.53/0.91      ( r1_tarski(sK1,sK2) = iProver_top ),
% 3.53/0.91      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_6,negated_conjecture,
% 3.53/0.91      ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 3.53/0.91      inference(cnf_transformation,[],[f32]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_15,plain,
% 3.53/0.91      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != iProver_top ),
% 3.53/0.91      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_266,plain,
% 3.53/0.91      ( X0_39 != X1_39
% 3.53/0.91      | k1_tops_1(X0_40,X0_39) = k1_tops_1(X0_40,X1_39) ),
% 3.53/0.91      theory(equality) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_271,plain,
% 3.53/0.91      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) | sK1 != sK1 ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_266]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_260,plain,( X0_39 = X0_39 ),theory(equality) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_273,plain,
% 3.53/0.91      ( sK1 = sK1 ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_260]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_288,plain,
% 3.53/0.91      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_251]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_535,plain,
% 3.53/0.91      ( k1_tops_1(sK0,sK2) = k1_tops_1(sK0,sK2) ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_260]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_261,plain,
% 3.53/0.91      ( X0_39 != X1_39 | X2_39 != X1_39 | X2_39 = X0_39 ),
% 3.53/0.91      theory(equality) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_517,plain,
% 3.53/0.91      ( X0_39 != X1_39
% 3.53/0.91      | k1_tops_1(sK0,sK2) != X1_39
% 3.53/0.91      | k1_tops_1(sK0,sK2) = X0_39 ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_261]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_545,plain,
% 3.53/0.91      ( X0_39 != k1_tops_1(sK0,sK2)
% 3.53/0.91      | k1_tops_1(sK0,sK2) = X0_39
% 3.53/0.91      | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_517]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_649,plain,
% 3.53/0.91      ( k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2)
% 3.53/0.91      | k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
% 3.53/0.91      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) != k1_tops_1(sK0,sK2) ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_545]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_650,plain,
% 3.53/0.91      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k1_tops_1(sK0,sK2) ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_251]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_0,plain,
% 3.53/0.91      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.53/0.91      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.53/0.91      inference(cnf_transformation,[],[f22]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_258,plain,
% 3.53/0.91      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_42))
% 3.53/0.91      | m1_subset_1(k3_subset_1(X0_42,X0_39),k1_zfmisc_1(X0_42)) ),
% 3.53/0.91      inference(subtyping,[status(esa)],[c_0]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_703,plain,
% 3.53/0.91      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_258]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_704,plain,
% 3.53/0.91      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.53/0.91      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_39),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.53/0.91      inference(predicate_to_equality,[status(thm)],[c_703]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_706,plain,
% 3.53/0.91      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.53/0.91      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_704]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_555,plain,
% 3.53/0.91      ( X0_39 != X1_39
% 3.53/0.91      | k1_tops_1(sK0,sK1) != X1_39
% 3.53/0.91      | k1_tops_1(sK0,sK1) = X0_39 ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_261]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_693,plain,
% 3.53/0.91      ( X0_39 != k1_tops_1(sK0,sK1)
% 3.53/0.91      | k1_tops_1(sK0,sK1) = X0_39
% 3.53/0.91      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_555]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_895,plain,
% 3.53/0.91      ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
% 3.53/0.91      | k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
% 3.53/0.91      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k1_tops_1(sK0,sK1) ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_693]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_2,plain,
% 3.53/0.91      ( ~ r1_tarski(X0,X1)
% 3.53/0.91      | r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
% 3.53/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 3.53/0.91      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.53/0.91      inference(cnf_transformation,[],[f23]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_256,plain,
% 3.53/0.91      ( ~ r1_tarski(X0_39,X1_39)
% 3.53/0.91      | r1_tarski(k3_subset_1(X0_42,X1_39),k3_subset_1(X0_42,X0_39))
% 3.53/0.91      | ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_42))
% 3.53/0.91      | ~ m1_subset_1(X1_39,k1_zfmisc_1(X0_42)) ),
% 3.53/0.91      inference(subtyping,[status(esa)],[c_2]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_621,plain,
% 3.53/0.91      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_39),k3_subset_1(u1_struct_0(sK0),sK1))
% 3.53/0.91      | ~ r1_tarski(sK1,X0_39)
% 3.53/0.91      | ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_256]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_909,plain,
% 3.53/0.91      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))
% 3.53/0.91      | ~ r1_tarski(sK1,sK2)
% 3.53/0.91      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_621]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_910,plain,
% 3.53/0.91      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = iProver_top
% 3.53/0.91      | r1_tarski(sK1,sK2) != iProver_top
% 3.53/0.91      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.53/0.91      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.53/0.91      inference(predicate_to_equality,[status(thm)],[c_909]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_4,plain,
% 3.53/0.91      ( ~ r1_tarski(X0,X1)
% 3.53/0.91      | r1_tarski(k2_pre_topc(X2,X0),k2_pre_topc(X2,X1))
% 3.53/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.53/0.91      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.53/0.91      | ~ l1_pre_topc(X2) ),
% 3.53/0.91      inference(cnf_transformation,[],[f26]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_147,plain,
% 3.53/0.91      ( ~ r1_tarski(X0,X1)
% 3.53/0.91      | r1_tarski(k2_pre_topc(X2,X0),k2_pre_topc(X2,X1))
% 3.53/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.53/0.91      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.53/0.91      | sK0 != X2 ),
% 3.53/0.91      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_148,plain,
% 3.53/0.91      ( ~ r1_tarski(X0,X1)
% 3.53/0.91      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))
% 3.53/0.91      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.91      inference(unflattening,[status(thm)],[c_147]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_249,plain,
% 3.53/0.91      ( ~ r1_tarski(X0_39,X1_39)
% 3.53/0.91      | r1_tarski(k2_pre_topc(sK0,X0_39),k2_pre_topc(sK0,X1_39))
% 3.53/0.91      | ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.91      inference(subtyping,[status(esa)],[c_148]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_495,plain,
% 3.53/0.91      ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(X0_42,X0_39)),k2_pre_topc(sK0,k3_subset_1(X0_42,X1_39)))
% 3.53/0.91      | ~ r1_tarski(k3_subset_1(X0_42,X0_39),k3_subset_1(X0_42,X1_39))
% 3.53/0.91      | ~ m1_subset_1(k3_subset_1(X0_42,X0_39),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | ~ m1_subset_1(k3_subset_1(X0_42,X1_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_249]) ).
% 3.53/0.91  
% 3.53/0.91  cnf(c_559,plain,
% 3.53/0.91      ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_39)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1_39)))
% 3.53/0.91      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_39),k3_subset_1(u1_struct_0(sK0),X1_39))
% 3.53/0.91      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_39),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.91      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X1_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.91      inference(instantiation,[status(thm)],[c_495]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_1183,plain,
% 3.53/0.92      ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
% 3.53/0.92      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))
% 3.53/0.92      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.92      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.92      inference(instantiation,[status(thm)],[c_559]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_1184,plain,
% 3.53/0.92      ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = iProver_top
% 3.53/0.92      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
% 3.53/0.92      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.53/0.92      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.53/0.92      inference(predicate_to_equality,[status(thm)],[c_1183]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_264,plain,
% 3.53/0.92      ( ~ r1_tarski(X0_39,X1_39)
% 3.53/0.92      | r1_tarski(X2_39,X3_39)
% 3.53/0.92      | X2_39 != X0_39
% 3.53/0.92      | X3_39 != X1_39 ),
% 3.53/0.92      theory(equality) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_485,plain,
% 3.53/0.92      ( ~ r1_tarski(X0_39,X1_39)
% 3.53/0.92      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 3.53/0.92      | k1_tops_1(sK0,sK2) != X1_39
% 3.53/0.92      | k1_tops_1(sK0,sK1) != X0_39 ),
% 3.53/0.92      inference(instantiation,[status(thm)],[c_264]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_858,plain,
% 3.53/0.92      ( ~ r1_tarski(X0_39,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))))
% 3.53/0.92      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 3.53/0.92      | k1_tops_1(sK0,sK2) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
% 3.53/0.92      | k1_tops_1(sK0,sK1) != X0_39 ),
% 3.53/0.92      inference(instantiation,[status(thm)],[c_485]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_1290,plain,
% 3.53/0.92      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 3.53/0.92      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))))
% 3.53/0.92      | k1_tops_1(sK0,sK2) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
% 3.53/0.92      | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
% 3.53/0.92      inference(instantiation,[status(thm)],[c_858]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_1291,plain,
% 3.53/0.92      ( k1_tops_1(sK0,sK2) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
% 3.53/0.92      | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
% 3.53/0.92      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = iProver_top
% 3.53/0.92      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))) != iProver_top ),
% 3.53/0.92      inference(predicate_to_equality,[status(thm)],[c_1290]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_1339,plain,
% 3.53/0.92      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.92      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.92      inference(instantiation,[status(thm)],[c_703]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_1340,plain,
% 3.53/0.92      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.53/0.92      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.53/0.92      inference(predicate_to_equality,[status(thm)],[c_1339]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_1000,plain,
% 3.53/0.92      ( ~ r1_tarski(X0_39,X1_39)
% 3.53/0.92      | r1_tarski(k3_subset_1(u1_struct_0(sK0),X1_39),k3_subset_1(u1_struct_0(sK0),X0_39))
% 3.53/0.92      | ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.92      | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.92      inference(instantiation,[status(thm)],[c_256]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_2077,plain,
% 3.53/0.92      ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
% 3.53/0.92      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))))
% 3.53/0.92      | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.92      | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.92      inference(instantiation,[status(thm)],[c_1000]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_2086,plain,
% 3.53/0.92      ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != iProver_top
% 3.53/0.92      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))) = iProver_top
% 3.53/0.92      | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.53/0.92      | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.53/0.92      inference(predicate_to_equality,[status(thm)],[c_2077]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_2627,plain,
% 3.53/0.92      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.53/0.92      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.53/0.92      inference(instantiation,[status(thm)],[c_250]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_2628,plain,
% 3.53/0.92      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.53/0.92      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.53/0.92      inference(predicate_to_equality,[status(thm)],[c_2627]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_3539,plain,
% 3.53/0.92      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.53/0.92      inference(global_propositional_subsumption,
% 3.53/0.92                [status(thm)],
% 3.53/0.92                [c_843,c_9,c_12,c_8,c_13,c_14,c_15,c_271,c_273,c_288,
% 3.53/0.92                 c_535,c_649,c_650,c_706,c_895,c_910,c_1184,c_1291,
% 3.53/0.92                 c_1340,c_2086,c_2628]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(c_3543,plain,
% 3.53/0.92      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.53/0.92      inference(superposition,[status(thm)],[c_461,c_3539]) ).
% 3.53/0.92  
% 3.53/0.92  cnf(contradiction,plain,
% 3.53/0.92      ( $false ),
% 3.53/0.92      inference(minisat,[status(thm)],[c_3543,c_706,c_12]) ).
% 3.53/0.92  
% 3.53/0.92  
% 3.53/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/0.92  
% 3.53/0.92  ------                               Statistics
% 3.53/0.92  
% 3.53/0.92  ------ General
% 3.53/0.92  
% 3.53/0.92  abstr_ref_over_cycles:                  0
% 3.53/0.92  abstr_ref_under_cycles:                 0
% 3.53/0.92  gc_basic_clause_elim:                   0
% 3.53/0.92  forced_gc_time:                         0
% 3.53/0.92  parsing_time:                           0.007
% 3.53/0.92  unif_index_cands_time:                  0.
% 3.53/0.92  unif_index_add_time:                    0.
% 3.53/0.92  orderings_time:                         0.
% 3.53/0.92  out_proof_time:                         0.009
% 3.53/0.92  total_time:                             0.168
% 3.53/0.92  num_of_symbols:                         43
% 3.53/0.92  num_of_terms:                           4214
% 3.53/0.92  
% 3.53/0.92  ------ Preprocessing
% 3.53/0.92  
% 3.53/0.92  num_of_splits:                          0
% 3.53/0.92  num_of_split_atoms:                     0
% 3.53/0.92  num_of_reused_defs:                     0
% 3.53/0.92  num_eq_ax_congr_red:                    7
% 3.53/0.92  num_of_sem_filtered_clauses:            1
% 3.53/0.92  num_of_subtypes:                        4
% 3.53/0.92  monotx_restored_types:                  0
% 3.53/0.92  sat_num_of_epr_types:                   0
% 3.53/0.92  sat_num_of_non_cyclic_types:            0
% 3.53/0.92  sat_guarded_non_collapsed_types:        0
% 3.53/0.92  num_pure_diseq_elim:                    0
% 3.53/0.92  simp_replaced_by:                       0
% 3.53/0.92  res_preprocessed:                       56
% 3.53/0.92  prep_upred:                             0
% 3.53/0.92  prep_unflattend:                        3
% 3.53/0.92  smt_new_axioms:                         0
% 3.53/0.92  pred_elim_cands:                        2
% 3.53/0.92  pred_elim:                              1
% 3.53/0.92  pred_elim_cl:                           1
% 3.53/0.92  pred_elim_cycles:                       3
% 3.53/0.92  merged_defs:                            0
% 3.53/0.92  merged_defs_ncl:                        0
% 3.53/0.92  bin_hyper_res:                          0
% 3.53/0.92  prep_cycles:                            4
% 3.53/0.92  pred_elim_time:                         0.001
% 3.53/0.92  splitting_time:                         0.
% 3.53/0.92  sem_filter_time:                        0.
% 3.53/0.92  monotx_time:                            0.
% 3.53/0.92  subtype_inf_time:                       0.
% 3.53/0.92  
% 3.53/0.92  ------ Problem properties
% 3.53/0.92  
% 3.53/0.92  clauses:                                10
% 3.53/0.92  conjectures:                            4
% 3.53/0.92  epr:                                    1
% 3.53/0.92  horn:                                   10
% 3.53/0.92  ground:                                 4
% 3.53/0.92  unary:                                  4
% 3.53/0.92  binary:                                 3
% 3.53/0.92  lits:                                   22
% 3.53/0.92  lits_eq:                                1
% 3.53/0.92  fd_pure:                                0
% 3.53/0.92  fd_pseudo:                              0
% 3.53/0.92  fd_cond:                                0
% 3.53/0.92  fd_pseudo_cond:                         0
% 3.53/0.92  ac_symbols:                             0
% 3.53/0.92  
% 3.53/0.92  ------ Propositional Solver
% 3.53/0.92  
% 3.53/0.92  prop_solver_calls:                      30
% 3.53/0.92  prop_fast_solver_calls:                 388
% 3.53/0.92  smt_solver_calls:                       0
% 3.53/0.92  smt_fast_solver_calls:                  0
% 3.53/0.92  prop_num_of_clauses:                    1603
% 3.53/0.92  prop_preprocess_simplified:             3473
% 3.53/0.92  prop_fo_subsumed:                       12
% 3.53/0.92  prop_solver_time:                       0.
% 3.53/0.92  smt_solver_time:                        0.
% 3.53/0.92  smt_fast_solver_time:                   0.
% 3.53/0.92  prop_fast_solver_time:                  0.
% 3.53/0.92  prop_unsat_core_time:                   0.
% 3.53/0.92  
% 3.53/0.92  ------ QBF
% 3.53/0.92  
% 3.53/0.92  qbf_q_res:                              0
% 3.53/0.92  qbf_num_tautologies:                    0
% 3.53/0.92  qbf_prep_cycles:                        0
% 3.53/0.92  
% 3.53/0.92  ------ BMC1
% 3.53/0.92  
% 3.53/0.92  bmc1_current_bound:                     -1
% 3.53/0.92  bmc1_last_solved_bound:                 -1
% 3.53/0.92  bmc1_unsat_core_size:                   -1
% 3.53/0.92  bmc1_unsat_core_parents_size:           -1
% 3.53/0.92  bmc1_merge_next_fun:                    0
% 3.53/0.92  bmc1_unsat_core_clauses_time:           0.
% 3.53/0.92  
% 3.53/0.92  ------ Instantiation
% 3.53/0.92  
% 3.53/0.92  inst_num_of_clauses:                    470
% 3.53/0.92  inst_num_in_passive:                    61
% 3.53/0.92  inst_num_in_active:                     283
% 3.53/0.92  inst_num_in_unprocessed:                126
% 3.53/0.92  inst_num_of_loops:                      310
% 3.53/0.92  inst_num_of_learning_restarts:          0
% 3.53/0.92  inst_num_moves_active_passive:          22
% 3.53/0.92  inst_lit_activity:                      0
% 3.53/0.92  inst_lit_activity_moves:                0
% 3.53/0.92  inst_num_tautologies:                   0
% 3.53/0.92  inst_num_prop_implied:                  0
% 3.53/0.92  inst_num_existing_simplified:           0
% 3.53/0.92  inst_num_eq_res_simplified:             0
% 3.53/0.92  inst_num_child_elim:                    0
% 3.53/0.92  inst_num_of_dismatching_blockings:      384
% 3.53/0.92  inst_num_of_non_proper_insts:           727
% 3.53/0.92  inst_num_of_duplicates:                 0
% 3.53/0.92  inst_inst_num_from_inst_to_res:         0
% 3.53/0.92  inst_dismatching_checking_time:         0.
% 3.53/0.92  
% 3.53/0.92  ------ Resolution
% 3.53/0.92  
% 3.53/0.92  res_num_of_clauses:                     0
% 3.53/0.92  res_num_in_passive:                     0
% 3.53/0.92  res_num_in_active:                      0
% 3.53/0.92  res_num_of_loops:                       60
% 3.53/0.92  res_forward_subset_subsumed:            57
% 3.53/0.92  res_backward_subset_subsumed:           0
% 3.53/0.92  res_forward_subsumed:                   0
% 3.53/0.92  res_backward_subsumed:                  0
% 3.53/0.92  res_forward_subsumption_resolution:     0
% 3.53/0.92  res_backward_subsumption_resolution:    0
% 3.53/0.92  res_clause_to_clause_subsumption:       322
% 3.53/0.92  res_orphan_elimination:                 0
% 3.53/0.92  res_tautology_del:                      76
% 3.53/0.92  res_num_eq_res_simplified:              0
% 3.53/0.92  res_num_sel_changes:                    0
% 3.53/0.92  res_moves_from_active_to_pass:          0
% 3.53/0.92  
% 3.53/0.92  ------ Superposition
% 3.53/0.92  
% 3.53/0.92  sup_time_total:                         0.
% 3.53/0.92  sup_time_generating:                    0.
% 3.53/0.92  sup_time_sim_full:                      0.
% 3.53/0.92  sup_time_sim_immed:                     0.
% 3.53/0.92  
% 3.53/0.92  sup_num_of_clauses:                     173
% 3.53/0.92  sup_num_in_active:                      46
% 3.53/0.92  sup_num_in_passive:                     127
% 3.53/0.92  sup_num_of_loops:                       60
% 3.53/0.92  sup_fw_superposition:                   80
% 3.53/0.92  sup_bw_superposition:                   99
% 3.53/0.92  sup_immediate_simplified:               0
% 3.53/0.92  sup_given_eliminated:                   0
% 3.53/0.92  comparisons_done:                       0
% 3.53/0.92  comparisons_avoided:                    0
% 3.53/0.92  
% 3.53/0.92  ------ Simplifications
% 3.53/0.92  
% 3.53/0.92  
% 3.53/0.92  sim_fw_subset_subsumed:                 0
% 3.53/0.92  sim_bw_subset_subsumed:                 14
% 3.53/0.92  sim_fw_subsumed:                        0
% 3.53/0.92  sim_bw_subsumed:                        1
% 3.53/0.92  sim_fw_subsumption_res:                 0
% 3.53/0.92  sim_bw_subsumption_res:                 0
% 3.53/0.92  sim_tautology_del:                      1
% 3.53/0.92  sim_eq_tautology_del:                   0
% 3.53/0.92  sim_eq_res_simp:                        0
% 3.53/0.92  sim_fw_demodulated:                     0
% 3.53/0.92  sim_bw_demodulated:                     0
% 3.53/0.92  sim_light_normalised:                   0
% 3.53/0.92  sim_joinable_taut:                      0
% 3.53/0.92  sim_joinable_simp:                      0
% 3.53/0.92  sim_ac_normalised:                      0
% 3.53/0.92  sim_smt_subsumption:                    0
% 3.53/0.92  
%------------------------------------------------------------------------------
