%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:49 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 465 expanded)
%              Number of clauses        :   82 ( 164 expanded)
%              Number of leaves         :   12 ( 122 expanded)
%              Depth                    :   19
%              Number of atoms          :  332 (1868 expanded)
%              Number of equality atoms :  115 ( 184 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f28])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & ( v2_tex_2(X2,X0)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & ( v2_tex_2(sK2,X0)
          | v2_tex_2(X1,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & ( v2_tex_2(X2,X0)
              | v2_tex_2(sK1,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21,f20,f19])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f27,f28])).

cnf(c_3,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_483,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_484,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_476,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_481,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_479,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2154,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_481,c_479])).

cnf(c_8810,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_476,c_2154])).

cnf(c_3683,plain,
    ( v2_tex_2(X0,sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_7,c_10])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4176,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK2,sK0)
    | v2_tex_2(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3683,c_12])).

cnf(c_4177,plain,
    ( v2_tex_2(X0,sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2) ),
    inference(renaming,[status(thm)],[c_4176])).

cnf(c_4202,plain,
    ( v2_tex_2(X0,sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_4177,c_5])).

cnf(c_4203,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4202])).

cnf(c_9608,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | v2_tex_2(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8810,c_4203])).

cnf(c_9609,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9608])).

cnf(c_9616,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X0,X1)),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_484,c_9609])).

cnf(c_13,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,negated_conjecture,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,plain,
    ( v2_tex_2(sK2,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_573,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_576,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_577,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_147,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_853,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X1)),u1_struct_0(sK0))
    | X0 != k1_setfam_1(k2_tarski(sK1,X1)) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_1466,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_1468,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_80,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_81,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_80])).

cnf(c_103,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_81])).

cnf(c_669,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_1467,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_692,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2088,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_2089,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2088])).

cnf(c_1567,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2666,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_1567])).

cnf(c_2669,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2666])).

cnf(c_4709,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4710,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4709])).

cnf(c_4932,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X0,X1)),sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK2) ),
    inference(resolution,[status(thm)],[c_4202,c_0])).

cnf(c_4933,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X0,X1)),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4932])).

cnf(c_2297,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0,sK2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,sK2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7932,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2297])).

cnf(c_7933,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7932])).

cnf(c_661,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)
    | X0 != k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_971,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,sK2),X0)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),X0)
    | k9_subset_1(u1_struct_0(sK0),X0,sK2) != k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_10321,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_10322,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) = iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10321])).

cnf(c_10730,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X0,X1)),sK0) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9616,c_13,c_14,c_10,c_16,c_17,c_573,c_577,c_1468,c_1467,c_2089,c_2669,c_4710,c_4933,c_7933,c_10322])).

cnf(c_10740,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,X0)),sK0) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_10730])).

cnf(c_15,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_574,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_668,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_675,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_827,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_828,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_624,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(k1_setfam_1(k2_tarski(X0,X2)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_945,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,X0)),sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_946,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,X0)),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),sK2) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_945])).

cnf(c_1148,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1149,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

cnf(c_13505,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,X0)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10740,c_13,c_14,c_10,c_15,c_16,c_17,c_573,c_574,c_577,c_675,c_828,c_946,c_1149,c_1468,c_1467,c_2089,c_2669,c_4710,c_7933,c_10322])).

cnf(c_13523,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_13505])).

cnf(c_480,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1029,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_476,c_480])).

cnf(c_473,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_103])).

cnf(c_1365,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1029,c_473])).

cnf(c_478,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1789,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1365,c_478])).

cnf(c_13761,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_13523,c_1789])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:34:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.76/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/0.98  
% 3.76/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.76/0.98  
% 3.76/0.98  ------  iProver source info
% 3.76/0.98  
% 3.76/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.76/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.76/0.98  git: non_committed_changes: false
% 3.76/0.98  git: last_make_outside_of_git: false
% 3.76/0.98  
% 3.76/0.98  ------ 
% 3.76/0.98  ------ Parsing...
% 3.76/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/0.98  
% 3.76/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.76/0.98  
% 3.76/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/0.98  
% 3.76/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.76/0.98  ------ Proving...
% 3.76/0.98  ------ Problem Properties 
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  clauses                                 13
% 3.76/0.98  conjectures                             5
% 3.76/0.98  EPR                                     2
% 3.76/0.98  Horn                                    12
% 3.76/0.98  unary                                   6
% 3.76/0.98  binary                                  6
% 3.76/0.98  lits                                    24
% 3.76/0.98  lits eq                                 3
% 3.76/0.98  fd_pure                                 0
% 3.76/0.98  fd_pseudo                               0
% 3.76/0.98  fd_cond                                 0
% 3.76/0.98  fd_pseudo_cond                          0
% 3.76/0.98  AC symbols                              0
% 3.76/0.98  
% 3.76/0.98  ------ Input Options Time Limit: Unbounded
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  ------ 
% 3.76/0.98  Current options:
% 3.76/0.98  ------ 
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  ------ Proving...
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  % SZS status Theorem for theBenchmark.p
% 3.76/0.98  
% 3.76/0.98   Resolution empty clause
% 3.76/0.98  
% 3.76/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/0.98  
% 3.76/0.98  fof(f4,axiom,(
% 3.76/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f26,plain,(
% 3.76/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f4])).
% 3.76/0.98  
% 3.76/0.98  fof(f2,axiom,(
% 3.76/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f24,plain,(
% 3.76/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f2])).
% 3.76/0.98  
% 3.76/0.98  fof(f6,axiom,(
% 3.76/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f28,plain,(
% 3.76/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.76/0.98    inference(cnf_transformation,[],[f6])).
% 3.76/0.98  
% 3.76/0.98  fof(f38,plain,(
% 3.76/0.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 3.76/0.98    inference(definition_unfolding,[],[f24,f28])).
% 3.76/0.98  
% 3.76/0.98  fof(f1,axiom,(
% 3.76/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f11,plain,(
% 3.76/0.98    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.76/0.98    inference(ennf_transformation,[],[f1])).
% 3.76/0.98  
% 3.76/0.98  fof(f23,plain,(
% 3.76/0.98    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f11])).
% 3.76/0.98  
% 3.76/0.98  fof(f37,plain,(
% 3.76/0.98    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 3.76/0.98    inference(definition_unfolding,[],[f23,f28])).
% 3.76/0.98  
% 3.76/0.98  fof(f9,conjecture,(
% 3.76/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f10,negated_conjecture,(
% 3.76/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.76/0.98    inference(negated_conjecture,[],[f9])).
% 3.76/0.98  
% 3.76/0.98  fof(f16,plain,(
% 3.76/0.98    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.76/0.98    inference(ennf_transformation,[],[f10])).
% 3.76/0.98  
% 3.76/0.98  fof(f17,plain,(
% 3.76/0.98    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.76/0.98    inference(flattening,[],[f16])).
% 3.76/0.98  
% 3.76/0.98  fof(f21,plain,(
% 3.76/0.98    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & (v2_tex_2(sK2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.76/0.98    introduced(choice_axiom,[])).
% 3.76/0.98  
% 3.76/0.98  fof(f20,plain,(
% 3.76/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.76/0.98    introduced(choice_axiom,[])).
% 3.76/0.98  
% 3.76/0.98  fof(f19,plain,(
% 3.76/0.98    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.76/0.98    introduced(choice_axiom,[])).
% 3.76/0.98  
% 3.76/0.98  fof(f22,plain,(
% 3.76/0.98    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.76/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21,f20,f19])).
% 3.76/0.98  
% 3.76/0.98  fof(f34,plain,(
% 3.76/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.76/0.98    inference(cnf_transformation,[],[f22])).
% 3.76/0.98  
% 3.76/0.98  fof(f7,axiom,(
% 3.76/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f18,plain,(
% 3.76/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.76/0.98    inference(nnf_transformation,[],[f7])).
% 3.76/0.98  
% 3.76/0.98  fof(f30,plain,(
% 3.76/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f18])).
% 3.76/0.98  
% 3.76/0.98  fof(f8,axiom,(
% 3.76/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f14,plain,(
% 3.76/0.98    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.76/0.98    inference(ennf_transformation,[],[f8])).
% 3.76/0.98  
% 3.76/0.98  fof(f15,plain,(
% 3.76/0.98    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.76/0.98    inference(flattening,[],[f14])).
% 3.76/0.98  
% 3.76/0.98  fof(f31,plain,(
% 3.76/0.98    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f15])).
% 3.76/0.98  
% 3.76/0.98  fof(f32,plain,(
% 3.76/0.98    l1_pre_topc(sK0)),
% 3.76/0.98    inference(cnf_transformation,[],[f22])).
% 3.76/0.98  
% 3.76/0.98  fof(f33,plain,(
% 3.76/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.76/0.98    inference(cnf_transformation,[],[f22])).
% 3.76/0.98  
% 3.76/0.98  fof(f35,plain,(
% 3.76/0.98    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 3.76/0.98    inference(cnf_transformation,[],[f22])).
% 3.76/0.98  
% 3.76/0.98  fof(f36,plain,(
% 3.76/0.98    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 3.76/0.98    inference(cnf_transformation,[],[f22])).
% 3.76/0.98  
% 3.76/0.98  fof(f29,plain,(
% 3.76/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.76/0.98    inference(cnf_transformation,[],[f18])).
% 3.76/0.98  
% 3.76/0.98  fof(f5,axiom,(
% 3.76/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f13,plain,(
% 3.76/0.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.76/0.98    inference(ennf_transformation,[],[f5])).
% 3.76/0.98  
% 3.76/0.98  fof(f27,plain,(
% 3.76/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.76/0.98    inference(cnf_transformation,[],[f13])).
% 3.76/0.98  
% 3.76/0.98  fof(f40,plain,(
% 3.76/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.76/0.98    inference(definition_unfolding,[],[f27,f28])).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3,plain,
% 3.76/0.98      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.76/0.98      inference(cnf_transformation,[],[f26]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_1,plain,
% 3.76/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 3.76/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_483,plain,
% 3.76/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_0,plain,
% 3.76/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
% 3.76/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_484,plain,
% 3.76/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.76/0.98      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_10,negated_conjecture,
% 3.76/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.76/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_476,plain,
% 3.76/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5,plain,
% 3.76/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.76/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_481,plain,
% 3.76/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.76/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_7,plain,
% 3.76/0.98      ( ~ v2_tex_2(X0,X1)
% 3.76/0.98      | v2_tex_2(X2,X1)
% 3.76/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/0.98      | ~ r1_tarski(X2,X0)
% 3.76/0.98      | ~ l1_pre_topc(X1) ),
% 3.76/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_479,plain,
% 3.76/0.98      ( v2_tex_2(X0,X1) != iProver_top
% 3.76/0.98      | v2_tex_2(X2,X1) = iProver_top
% 3.76/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.76/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.76/0.98      | r1_tarski(X2,X0) != iProver_top
% 3.76/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2154,plain,
% 3.76/0.98      ( v2_tex_2(X0,X1) != iProver_top
% 3.76/0.98      | v2_tex_2(X2,X1) = iProver_top
% 3.76/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.76/0.98      | r1_tarski(X2,X0) != iProver_top
% 3.76/0.98      | r1_tarski(X2,u1_struct_0(X1)) != iProver_top
% 3.76/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_481,c_479]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_8810,plain,
% 3.76/0.98      ( v2_tex_2(X0,sK0) = iProver_top
% 3.76/0.98      | v2_tex_2(sK2,sK0) != iProver_top
% 3.76/0.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.76/0.98      | r1_tarski(X0,sK2) != iProver_top
% 3.76/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_476,c_2154]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3683,plain,
% 3.76/0.98      ( v2_tex_2(X0,sK0)
% 3.76/0.98      | ~ v2_tex_2(sK2,sK0)
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.76/0.98      | ~ r1_tarski(X0,sK2)
% 3.76/0.98      | ~ l1_pre_topc(sK0) ),
% 3.76/0.98      inference(resolution,[status(thm)],[c_7,c_10]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_12,negated_conjecture,
% 3.76/0.98      ( l1_pre_topc(sK0) ),
% 3.76/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4176,plain,
% 3.76/0.98      ( ~ r1_tarski(X0,sK2)
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.76/0.98      | ~ v2_tex_2(sK2,sK0)
% 3.76/0.98      | v2_tex_2(X0,sK0) ),
% 3.76/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3683,c_12]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4177,plain,
% 3.76/0.98      ( v2_tex_2(X0,sK0)
% 3.76/0.98      | ~ v2_tex_2(sK2,sK0)
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.76/0.98      | ~ r1_tarski(X0,sK2) ),
% 3.76/0.98      inference(renaming,[status(thm)],[c_4176]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4202,plain,
% 3.76/0.98      ( v2_tex_2(X0,sK0)
% 3.76/0.98      | ~ v2_tex_2(sK2,sK0)
% 3.76/0.98      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 3.76/0.98      | ~ r1_tarski(X0,sK2) ),
% 3.76/0.98      inference(resolution,[status(thm)],[c_4177,c_5]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4203,plain,
% 3.76/0.98      ( v2_tex_2(X0,sK0) = iProver_top
% 3.76/0.98      | v2_tex_2(sK2,sK0) != iProver_top
% 3.76/0.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.76/0.98      | r1_tarski(X0,sK2) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_4202]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_9608,plain,
% 3.76/0.98      ( r1_tarski(X0,sK2) != iProver_top
% 3.76/0.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.76/0.98      | v2_tex_2(sK2,sK0) != iProver_top
% 3.76/0.98      | v2_tex_2(X0,sK0) = iProver_top ),
% 3.76/0.98      inference(global_propositional_subsumption,[status(thm)],[c_8810,c_4203]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_9609,plain,
% 3.76/0.98      ( v2_tex_2(X0,sK0) = iProver_top
% 3.76/0.98      | v2_tex_2(sK2,sK0) != iProver_top
% 3.76/0.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.76/0.98      | r1_tarski(X0,sK2) != iProver_top ),
% 3.76/0.98      inference(renaming,[status(thm)],[c_9608]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_9616,plain,
% 3.76/0.98      ( v2_tex_2(k1_setfam_1(k2_tarski(X0,X1)),sK0) = iProver_top
% 3.76/0.98      | v2_tex_2(sK2,sK0) != iProver_top
% 3.76/0.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.76/0.98      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK2) != iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_484,c_9609]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_13,plain,
% 3.76/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_11,negated_conjecture,
% 3.76/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.76/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_14,plain,
% 3.76/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_9,negated_conjecture,
% 3.76/0.98      ( v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0) ),
% 3.76/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_16,plain,
% 3.76/0.98      ( v2_tex_2(sK2,sK0) = iProver_top | v2_tex_2(sK1,sK0) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_8,negated_conjecture,
% 3.76/0.98      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 3.76/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_17,plain,
% 3.76/0.98      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_6,plain,
% 3.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.76/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_573,plain,
% 3.76/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.76/0.98      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_576,plain,
% 3.76/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.76/0.98      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_577,plain,
% 3.76/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.76/0.98      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_147,plain,
% 3.76/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.76/0.98      theory(equality) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_853,plain,
% 3.76/0.98      ( r1_tarski(X0,u1_struct_0(sK0))
% 3.76/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X1)),u1_struct_0(sK0))
% 3.76/0.98      | X0 != k1_setfam_1(k2_tarski(sK1,X1)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_147]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_1466,plain,
% 3.76/0.98      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
% 3.76/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
% 3.76/0.98      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_853]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_1468,plain,
% 3.76/0.98      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))
% 3.76/0.98      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) = iProver_top
% 3.76/0.98      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_1466]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4,plain,
% 3.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.76/0.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.76/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_80,plain,
% 3.76/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.76/0.98      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_81,plain,
% 3.76/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.76/0.98      inference(renaming,[status(thm)],[c_80]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_103,plain,
% 3.76/0.98      ( ~ r1_tarski(X0,X1)
% 3.76/0.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.76/0.98      inference(bin_hyper_res,[status(thm)],[c_4,c_81]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_669,plain,
% 3.76/0.98      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 3.76/0.98      | k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_103]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_1467,plain,
% 3.76/0.98      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 3.76/0.98      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_669]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_692,plain,
% 3.76/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0))
% 3.76/0.98      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2088,plain,
% 3.76/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
% 3.76/0.98      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_692]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2089,plain,
% 3.76/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) = iProver_top
% 3.76/0.98      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_2088]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_1567,plain,
% 3.76/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),X0) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2666,plain,
% 3.76/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_1567]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2669,plain,
% 3.76/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_2666]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4709,plain,
% 3.76/0.98      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.76/0.98      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4710,plain,
% 3.76/0.98      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.76/0.98      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_4709]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4932,plain,
% 3.76/0.98      ( v2_tex_2(k1_setfam_1(k2_tarski(X0,X1)),sK0)
% 3.76/0.98      | ~ v2_tex_2(sK2,sK0)
% 3.76/0.98      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 3.76/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK2) ),
% 3.76/0.98      inference(resolution,[status(thm)],[c_4202,c_0]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4933,plain,
% 3.76/0.98      ( v2_tex_2(k1_setfam_1(k2_tarski(X0,X1)),sK0) = iProver_top
% 3.76/0.98      | v2_tex_2(sK2,sK0) != iProver_top
% 3.76/0.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.76/0.98      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK2) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_4932]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2297,plain,
% 3.76/0.98      ( ~ v2_tex_2(X0,X1)
% 3.76/0.98      | v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0,sK2),X1)
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/0.98      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/0.98      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,sK2),X0)
% 3.76/0.98      | ~ l1_pre_topc(X1) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_7932,plain,
% 3.76/0.98      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 3.76/0.98      | ~ v2_tex_2(sK1,sK0)
% 3.76/0.98      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.76/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.76/0.98      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 3.76/0.98      | ~ l1_pre_topc(sK0) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_2297]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_7933,plain,
% 3.76/0.98      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
% 3.76/0.98      | v2_tex_2(sK1,sK0) != iProver_top
% 3.76/0.98      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.76/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.76/0.98      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) != iProver_top
% 3.76/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_7932]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_661,plain,
% 3.76/0.98      ( r1_tarski(X0,X1)
% 3.76/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)
% 3.76/0.98      | X0 != k1_setfam_1(k2_tarski(X1,X2)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_147]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_971,plain,
% 3.76/0.98      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,sK2),X0)
% 3.76/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),X0)
% 3.76/0.98      | k9_subset_1(u1_struct_0(sK0),X0,sK2) != k1_setfam_1(k2_tarski(X0,sK2)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_661]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_10321,plain,
% 3.76/0.98      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 3.76/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
% 3.76/0.98      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_971]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_10322,plain,
% 3.76/0.98      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))
% 3.76/0.98      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) = iProver_top
% 3.76/0.98      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_10321]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_10730,plain,
% 3.76/0.98      ( v2_tex_2(k1_setfam_1(k2_tarski(X0,X1)),sK0) = iProver_top
% 3.76/0.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.76/0.98      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),sK2) != iProver_top ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_9616,c_13,c_14,c_10,c_16,c_17,c_573,c_577,c_1468,c_1467,
% 3.76/0.98                 c_2089,c_2669,c_4710,c_4933,c_7933,c_10322]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_10740,plain,
% 3.76/0.98      ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,X0)),sK0) = iProver_top
% 3.76/0.98      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_483,c_10730]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_15,plain,
% 3.76/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_574,plain,
% 3.76/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.76/0.98      | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_668,plain,
% 3.76/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),u1_struct_0(sK0))
% 3.76/0.98      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_675,plain,
% 3.76/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),u1_struct_0(sK0)) = iProver_top
% 3.76/0.98      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_827,plain,
% 3.76/0.98      ( m1_subset_1(k1_setfam_1(k2_tarski(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.76/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),u1_struct_0(sK0)) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_828,plain,
% 3.76/0.98      ( m1_subset_1(k1_setfam_1(k2_tarski(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.76/0.98      | r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),u1_struct_0(sK0)) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_624,plain,
% 3.76/0.98      ( ~ v2_tex_2(X0,X1)
% 3.76/0.98      | v2_tex_2(k1_setfam_1(k2_tarski(X0,X2)),X1)
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/0.98      | ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,X2)),k1_zfmisc_1(u1_struct_0(X1)))
% 3.76/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X0)
% 3.76/0.98      | ~ l1_pre_topc(X1) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_945,plain,
% 3.76/0.98      ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,X0)),sK0)
% 3.76/0.98      | ~ v2_tex_2(sK2,sK0)
% 3.76/0.98      | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.76/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.76/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),sK2)
% 3.76/0.98      | ~ l1_pre_topc(sK0) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_624]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_946,plain,
% 3.76/0.98      ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,X0)),sK0) = iProver_top
% 3.76/0.98      | v2_tex_2(sK2,sK0) != iProver_top
% 3.76/0.98      | m1_subset_1(k1_setfam_1(k2_tarski(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.76/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.76/0.98      | r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),sK2) != iProver_top
% 3.76/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_945]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_1148,plain,
% 3.76/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),sK2) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_1149,plain,
% 3.76/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),sK2) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_1148]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_13505,plain,
% 3.76/0.98      ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,X0)),sK0) = iProver_top ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_10740,c_13,c_14,c_10,c_15,c_16,c_17,c_573,c_574,c_577,
% 3.76/0.98                 c_675,c_828,c_946,c_1149,c_1468,c_1467,c_2089,c_2669,c_4710,
% 3.76/0.98                 c_7933,c_10322]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_13523,plain,
% 3.76/0.98      ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_3,c_13505]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_480,plain,
% 3.76/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.76/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_1029,plain,
% 3.76/0.98      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_476,c_480]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_473,plain,
% 3.76/0.98      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 3.76/0.98      | r1_tarski(X2,X0) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_103]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_1365,plain,
% 3.76/0.98      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_1029,c_473]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_478,plain,
% 3.76/0.98      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_1789,plain,
% 3.76/0.98      ( v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
% 3.76/0.98      inference(demodulation,[status(thm)],[c_1365,c_478]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_13761,plain,
% 3.76/0.98      ( $false ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_13523,c_1789]) ).
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/0.98  
% 3.76/0.98  ------                               Statistics
% 3.76/0.98  
% 3.76/0.98  ------ Selected
% 3.76/0.98  
% 3.76/0.98  total_time:                             0.416
% 3.76/0.98  
%------------------------------------------------------------------------------
