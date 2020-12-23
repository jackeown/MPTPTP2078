%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1237+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:13 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
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
fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

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

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
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

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_123,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_124,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_123])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_124])).

cnf(c_460,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_252,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_459,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_135,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_136,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_135])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_39))) = k1_tops_1(sK0,X0_39) ),
    inference(subtyping,[status(esa)],[c_136])).

cnf(c_461,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_39))) = k1_tops_1(sK0,X0_39)
    | m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_250])).

cnf(c_673,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_459,c_461])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_257,plain,
    ( r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(k3_subset_1(X0_42,X1_39),k3_subset_1(X0_42,X0_39))
    | ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_42))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_3])).

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

cnf(c_262,plain,
    ( X0_39 != X1_39
    | k1_tops_1(X0_40,X0_39) = k1_tops_1(X0_40,X1_39) ),
    theory(equality)).

cnf(c_267,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_260,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_273,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_291,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_250])).

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
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) != k1_tops_1(sK0,sK2)
    | k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_650,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_42))
    | m1_subset_1(k3_subset_1(X0_42,X0_39),k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_2])).

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
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_693])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_256,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(k3_subset_1(X0_42,X1_39),k3_subset_1(X0_42,X0_39))
    | ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_42))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_4])).

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

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(X2,X0),k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_147,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(X2,X0),k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

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

cnf(c_266,plain,
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
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_858,plain,
    ( ~ r1_tarski(X0_39,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,sK2) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | k1_tops_1(sK0,sK1) != X0_39 ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_1290,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,sK2) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_1291,plain,
    ( k1_tops_1(sK0,sK2) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = iProver_top ),
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

cnf(c_2075,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_2084,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2075])).

cnf(c_2623,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_2624,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2623])).

cnf(c_3530,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_843,c_9,c_12,c_8,c_13,c_14,c_15,c_267,c_273,c_291,c_535,c_649,c_650,c_706,c_895,c_910,c_1184,c_1291,c_1340,c_2084,c_2624])).

cnf(c_3534,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_3530])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3534,c_706,c_12])).


%------------------------------------------------------------------------------
