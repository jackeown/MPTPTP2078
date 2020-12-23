%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:50 EST 2020

% Result     : Theorem 15.64s
% Output     : CNFRefutation 15.64s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_693)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f23,plain,(
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

fof(f22,plain,(
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

fof(f21,plain,
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

fof(f24,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23,f22,f21])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f29,f30])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f29,f29])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_486,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_490,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1748,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_486,c_490])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_493,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_521,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_493,c_5])).

cnf(c_2360,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,u1_struct_0(sK0))) = sK2 ),
    inference(superposition,[status(thm)],[c_1748,c_521])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_492,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_82,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_83,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_82])).

cnf(c_106,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_83])).

cnf(c_483,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_106])).

cnf(c_530,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_483,c_5])).

cnf(c_3189,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) = k9_subset_1(X1,X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_492,c_530])).

cnf(c_46286,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k9_subset_1(X2,X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_3189])).

cnf(c_47199,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k9_subset_1(X2,X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
    inference(demodulation,[status(thm)],[c_46286,c_5])).

cnf(c_52083,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k1_setfam_1(k1_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),sK2))) = k1_setfam_1(k1_enumset1(X0,X0,sK2)) ),
    inference(superposition,[status(thm)],[c_2360,c_47199])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_494,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2202,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_494])).

cnf(c_54623,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,k1_setfam_1(k1_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),sK2))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_52083,c_2202])).

cnf(c_3188,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) = k9_subset_1(X3,X0,k4_xboole_0(X1,X2))
    | r1_tarski(X1,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_530])).

cnf(c_40711,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(sK2,X1))) = k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_1748,c_3188])).

cnf(c_994,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_492])).

cnf(c_2509,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_994])).

cnf(c_40715,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(sK2,X1))) = k9_subset_1(sK2,X0,k4_xboole_0(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_2509,c_3188])).

cnf(c_40890,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(sK2,X1)) = k9_subset_1(sK2,X0,k4_xboole_0(sK2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_40711,c_40715])).

cnf(c_45364,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(X1,k4_xboole_0(X1,sK2))) = k9_subset_1(sK2,X0,k4_xboole_0(sK2,k4_xboole_0(sK2,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_40890])).

cnf(c_45414,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k1_setfam_1(k1_enumset1(X1,X1,sK2))) = k9_subset_1(sK2,X0,k1_setfam_1(k1_enumset1(sK2,sK2,X1))) ),
    inference(demodulation,[status(thm)],[c_45364,c_5])).

cnf(c_54698,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(sK2,X0,k1_setfam_1(k1_enumset1(sK2,sK2,u1_struct_0(sK0)))),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_54623,c_45414])).

cnf(c_54699,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(sK2,X0,sK2),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_54698,c_2360])).

cnf(c_2205,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_494])).

cnf(c_2208,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k1_enumset1(X2,X2,X0)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2205,c_5])).

cnf(c_54611,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,k1_setfam_1(k1_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),sK2))),X1) = iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_52083,c_2208])).

cnf(c_54740,plain,
    ( r1_tarski(k9_subset_1(sK2,X0,k1_setfam_1(k1_enumset1(sK2,sK2,u1_struct_0(sK0)))),X1) = iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_54611,c_45414])).

cnf(c_54741,plain,
    ( r1_tarski(k9_subset_1(sK2,X0,sK2),X1) = iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_54740,c_2360])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_485,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_491,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_489,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1920,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_491,c_489])).

cnf(c_4828,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_485,c_1920])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5771,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | v2_tex_2(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4828,c_14])).

cnf(c_5772,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5771])).

cnf(c_60183,plain,
    ( v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(k9_subset_1(sK2,X0,sK2),sK1) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_54741,c_5772])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,negated_conjecture,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,plain,
    ( v2_tex_2(sK2,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_591,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_592,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_4827,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_486,c_1920])).

cnf(c_3686,plain,
    ( v2_tex_2(X0,sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_8,c_11])).

cnf(c_3878,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK2,sK0)
    | v2_tex_2(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3686,c_13])).

cnf(c_3879,plain,
    ( v2_tex_2(X0,sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2) ),
    inference(renaming,[status(thm)],[c_3878])).

cnf(c_3904,plain,
    ( v2_tex_2(X0,sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_3879,c_6])).

cnf(c_3905,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3904])).

cnf(c_5700,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | v2_tex_2(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4827,c_3905])).

cnf(c_5701,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5700])).

cnf(c_5708,plain,
    ( v2_tex_2(k4_xboole_0(X0,X1),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_5701])).

cnf(c_6753,plain,
    ( v2_tex_2(k4_xboole_0(sK2,X0),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_492,c_5708])).

cnf(c_14658,plain,
    ( v2_tex_2(sK2,sK0) != iProver_top
    | v2_tex_2(k4_xboole_0(sK2,X0),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6753,c_14,c_16,c_592,c_693,c_811,c_944,c_2774])).

cnf(c_14659,plain,
    ( v2_tex_2(k4_xboole_0(sK2,X0),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14658])).

cnf(c_14669,plain,
    ( v2_tex_2(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_14659])).

cnf(c_14708,plain,
    ( v2_tex_2(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14669,c_5])).

cnf(c_54629,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0,k1_setfam_1(k1_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),sK2))),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_52083,c_14708])).

cnf(c_54673,plain,
    ( v2_tex_2(k9_subset_1(sK2,X0,k1_setfam_1(k1_enumset1(sK2,sK2,u1_struct_0(sK0)))),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_54629,c_45414])).

cnf(c_54674,plain,
    ( v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_54673,c_2360])).

cnf(c_3190,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(superposition,[status(thm)],[c_1748,c_530])).

cnf(c_3194,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k9_subset_1(sK2,X0,sK2) ),
    inference(superposition,[status(thm)],[c_2509,c_530])).

cnf(c_3216,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3190,c_3194])).

cnf(c_9,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_488,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4240,plain,
    ( v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3216,c_488])).

cnf(c_55482,plain,
    ( v2_tex_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_54674,c_4240])).

cnf(c_60760,plain,
    ( r1_tarski(k9_subset_1(sK2,X0,sK2),sK1) != iProver_top
    | v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_60183,c_16,c_17,c_592,c_55482])).

cnf(c_60761,plain,
    ( v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | r1_tarski(k9_subset_1(sK2,X0,sK2),sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_60760])).

cnf(c_60769,plain,
    ( v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_54699,c_60761])).

cnf(c_61253,plain,
    ( r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_60769,c_4240])).

cnf(c_1749,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_485,c_490])).

cnf(c_2361,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,u1_struct_0(sK0))) = sK1 ),
    inference(superposition,[status(thm)],[c_1749,c_521])).

cnf(c_2522,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2361,c_994])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_61253,c_2522])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:44:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.64/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.64/2.49  
% 15.64/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.64/2.49  
% 15.64/2.49  ------  iProver source info
% 15.64/2.49  
% 15.64/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.64/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.64/2.49  git: non_committed_changes: false
% 15.64/2.49  git: last_make_outside_of_git: false
% 15.64/2.49  
% 15.64/2.49  ------ 
% 15.64/2.49  ------ Parsing...
% 15.64/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.64/2.49  
% 15.64/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.64/2.49  
% 15.64/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.64/2.49  
% 15.64/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.64/2.49  ------ Proving...
% 15.64/2.49  ------ Problem Properties 
% 15.64/2.49  
% 15.64/2.49  
% 15.64/2.49  clauses                                 14
% 15.64/2.49  conjectures                             5
% 15.64/2.49  EPR                                     2
% 15.64/2.49  Horn                                    13
% 15.64/2.49  unary                                   7
% 15.64/2.49  binary                                  6
% 15.64/2.49  lits                                    25
% 15.64/2.49  lits eq                                 4
% 15.64/2.49  fd_pure                                 0
% 15.64/2.49  fd_pseudo                               0
% 15.64/2.49  fd_cond                                 0
% 15.64/2.49  fd_pseudo_cond                          0
% 15.64/2.49  AC symbols                              0
% 15.64/2.49  
% 15.64/2.49  ------ Input Options Time Limit: Unbounded
% 15.64/2.49  
% 15.64/2.49  
% 15.64/2.49  ------ 
% 15.64/2.49  Current options:
% 15.64/2.49  ------ 
% 15.64/2.49  
% 15.64/2.49  
% 15.64/2.49  
% 15.64/2.49  
% 15.64/2.49  ------ Proving...
% 15.64/2.49  
% 15.64/2.49  
% 15.64/2.49  % SZS status Theorem for theBenchmark.p
% 15.64/2.49  
% 15.64/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.64/2.49  
% 15.64/2.49  fof(f11,conjecture,(
% 15.64/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 15.64/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.64/2.49  
% 15.64/2.49  fof(f12,negated_conjecture,(
% 15.64/2.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 15.64/2.49    inference(negated_conjecture,[],[f11])).
% 15.64/2.49  
% 15.64/2.49  fof(f18,plain,(
% 15.64/2.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.64/2.49    inference(ennf_transformation,[],[f12])).
% 15.64/2.49  
% 15.64/2.49  fof(f19,plain,(
% 15.64/2.49    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.64/2.49    inference(flattening,[],[f18])).
% 15.64/2.49  
% 15.64/2.49  fof(f23,plain,(
% 15.64/2.49    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & (v2_tex_2(sK2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.64/2.49    introduced(choice_axiom,[])).
% 15.64/2.49  
% 15.64/2.49  fof(f22,plain,(
% 15.64/2.49    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.64/2.49    introduced(choice_axiom,[])).
% 15.64/2.49  
% 15.64/2.49  fof(f21,plain,(
% 15.64/2.49    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 15.64/2.49    introduced(choice_axiom,[])).
% 15.64/2.49  
% 15.64/2.49  fof(f24,plain,(
% 15.64/2.49    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 15.64/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23,f22,f21])).
% 15.64/2.49  
% 15.64/2.49  fof(f38,plain,(
% 15.64/2.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.64/2.49    inference(cnf_transformation,[],[f24])).
% 15.64/2.49  
% 15.64/2.49  fof(f9,axiom,(
% 15.64/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.64/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.64/2.49  
% 15.64/2.49  fof(f20,plain,(
% 15.64/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.64/2.49    inference(nnf_transformation,[],[f9])).
% 15.64/2.49  
% 15.64/2.49  fof(f33,plain,(
% 15.64/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.64/2.49    inference(cnf_transformation,[],[f20])).
% 15.64/2.49  
% 15.64/2.49  fof(f3,axiom,(
% 15.64/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.64/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.64/2.49  
% 15.64/2.49  fof(f14,plain,(
% 15.64/2.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.64/2.49    inference(ennf_transformation,[],[f3])).
% 15.64/2.49  
% 15.64/2.49  fof(f27,plain,(
% 15.64/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.64/2.49    inference(cnf_transformation,[],[f14])).
% 15.64/2.49  
% 15.64/2.49  fof(f5,axiom,(
% 15.64/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.64/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.64/2.49  
% 15.64/2.49  fof(f29,plain,(
% 15.64/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.64/2.49    inference(cnf_transformation,[],[f5])).
% 15.64/2.49  
% 15.64/2.49  fof(f42,plain,(
% 15.64/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 15.64/2.49    inference(definition_unfolding,[],[f27,f29])).
% 15.64/2.49  
% 15.64/2.49  fof(f8,axiom,(
% 15.64/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.64/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.64/2.49  
% 15.64/2.49  fof(f32,plain,(
% 15.64/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.64/2.49    inference(cnf_transformation,[],[f8])).
% 15.64/2.49  
% 15.64/2.49  fof(f6,axiom,(
% 15.64/2.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.64/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.64/2.49  
% 15.64/2.49  fof(f30,plain,(
% 15.64/2.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.64/2.49    inference(cnf_transformation,[],[f6])).
% 15.64/2.49  
% 15.64/2.49  fof(f44,plain,(
% 15.64/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 15.64/2.49    inference(definition_unfolding,[],[f32,f29,f30])).
% 15.64/2.49  
% 15.64/2.49  fof(f1,axiom,(
% 15.64/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.64/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.64/2.49  
% 15.64/2.49  fof(f25,plain,(
% 15.64/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.64/2.49    inference(cnf_transformation,[],[f1])).
% 15.64/2.49  
% 15.64/2.49  fof(f41,plain,(
% 15.64/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 15.64/2.49    inference(definition_unfolding,[],[f25,f29,f29])).
% 15.64/2.49  
% 15.64/2.49  fof(f4,axiom,(
% 15.64/2.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.64/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.64/2.49  
% 15.64/2.49  fof(f28,plain,(
% 15.64/2.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.64/2.49    inference(cnf_transformation,[],[f4])).
% 15.64/2.49  
% 15.64/2.49  fof(f7,axiom,(
% 15.64/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 15.64/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.64/2.49  
% 15.64/2.49  fof(f15,plain,(
% 15.64/2.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.64/2.49    inference(ennf_transformation,[],[f7])).
% 15.64/2.49  
% 15.64/2.49  fof(f31,plain,(
% 15.64/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.64/2.49    inference(cnf_transformation,[],[f15])).
% 15.64/2.49  
% 15.64/2.49  fof(f43,plain,(
% 15.64/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.64/2.49    inference(definition_unfolding,[],[f31,f29])).
% 15.64/2.49  
% 15.64/2.49  fof(f34,plain,(
% 15.64/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.64/2.49    inference(cnf_transformation,[],[f20])).
% 15.64/2.49  
% 15.64/2.49  fof(f2,axiom,(
% 15.64/2.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 15.64/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.64/2.49  
% 15.64/2.49  fof(f13,plain,(
% 15.64/2.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 15.64/2.49    inference(ennf_transformation,[],[f2])).
% 15.64/2.49  
% 15.64/2.49  fof(f26,plain,(
% 15.64/2.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 15.64/2.49    inference(cnf_transformation,[],[f13])).
% 15.64/2.49  
% 15.64/2.49  fof(f37,plain,(
% 15.64/2.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.64/2.49    inference(cnf_transformation,[],[f24])).
% 15.64/2.49  
% 15.64/2.49  fof(f10,axiom,(
% 15.64/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 15.64/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.64/2.49  
% 15.64/2.49  fof(f16,plain,(
% 15.64/2.49    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.64/2.49    inference(ennf_transformation,[],[f10])).
% 15.64/2.49  
% 15.64/2.49  fof(f17,plain,(
% 15.64/2.49    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.64/2.49    inference(flattening,[],[f16])).
% 15.64/2.49  
% 15.64/2.49  fof(f35,plain,(
% 15.64/2.49    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.64/2.49    inference(cnf_transformation,[],[f17])).
% 15.64/2.49  
% 15.64/2.49  fof(f36,plain,(
% 15.64/2.49    l1_pre_topc(sK0)),
% 15.64/2.49    inference(cnf_transformation,[],[f24])).
% 15.64/2.49  
% 15.64/2.49  fof(f39,plain,(
% 15.64/2.49    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 15.64/2.49    inference(cnf_transformation,[],[f24])).
% 15.64/2.49  
% 15.64/2.49  fof(f40,plain,(
% 15.64/2.49    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 15.64/2.49    inference(cnf_transformation,[],[f24])).
% 15.64/2.49  
% 15.64/2.49  cnf(c_11,negated_conjecture,
% 15.64/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.64/2.49      inference(cnf_transformation,[],[f38]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_486,plain,
% 15.64/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_7,plain,
% 15.64/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.64/2.49      inference(cnf_transformation,[],[f33]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_490,plain,
% 15.64/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.64/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_1748,plain,
% 15.64/2.49      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_486,c_490]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_2,plain,
% 15.64/2.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 15.64/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_493,plain,
% 15.64/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 15.64/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_5,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 15.64/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_521,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
% 15.64/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.64/2.49      inference(demodulation,[status(thm)],[c_493,c_5]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_2360,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(sK2,sK2,u1_struct_0(sK0))) = sK2 ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_1748,c_521]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_0,plain,
% 15.64/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 15.64/2.49      inference(cnf_transformation,[],[f41]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_3,plain,
% 15.64/2.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 15.64/2.49      inference(cnf_transformation,[],[f28]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_492,plain,
% 15.64/2.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_4,plain,
% 15.64/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.64/2.49      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 15.64/2.49      inference(cnf_transformation,[],[f43]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_6,plain,
% 15.64/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.64/2.49      inference(cnf_transformation,[],[f34]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_82,plain,
% 15.64/2.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.64/2.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_83,plain,
% 15.64/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.64/2.49      inference(renaming,[status(thm)],[c_82]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_106,plain,
% 15.64/2.49      ( ~ r1_tarski(X0,X1)
% 15.64/2.49      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 15.64/2.49      inference(bin_hyper_res,[status(thm)],[c_4,c_83]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_483,plain,
% 15.64/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 15.64/2.49      | r1_tarski(X1,X2) != iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_106]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_530,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 15.64/2.49      | r1_tarski(X1,X2) != iProver_top ),
% 15.64/2.49      inference(demodulation,[status(thm)],[c_483,c_5]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_3189,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) = k9_subset_1(X1,X0,k4_xboole_0(X1,X2)) ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_492,c_530]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_46286,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k9_subset_1(X2,X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_0,c_3189]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_47199,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k9_subset_1(X2,X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
% 15.64/2.49      inference(demodulation,[status(thm)],[c_46286,c_5]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_52083,plain,
% 15.64/2.49      ( k9_subset_1(u1_struct_0(sK0),X0,k1_setfam_1(k1_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),sK2))) = k1_setfam_1(k1_enumset1(X0,X0,sK2)) ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_2360,c_47199]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_1,plain,
% 15.64/2.49      ( ~ r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1) ),
% 15.64/2.49      inference(cnf_transformation,[],[f26]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_494,plain,
% 15.64/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.64/2.49      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_2202,plain,
% 15.64/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.64/2.49      | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_5,c_494]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_54623,plain,
% 15.64/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.64/2.49      | r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,k1_setfam_1(k1_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),sK2))),X1) = iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_52083,c_2202]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_3188,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) = k9_subset_1(X3,X0,k4_xboole_0(X1,X2))
% 15.64/2.49      | r1_tarski(X1,X3) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_494,c_530]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_40711,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(sK2,X1))) = k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(sK2,X1)) ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_1748,c_3188]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_994,plain,
% 15.64/2.49      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_5,c_492]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_2509,plain,
% 15.64/2.49      ( r1_tarski(sK2,sK2) = iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_2360,c_994]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_40715,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(sK2,X1))) = k9_subset_1(sK2,X0,k4_xboole_0(sK2,X1)) ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_2509,c_3188]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_40890,plain,
% 15.64/2.49      ( k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(sK2,X1)) = k9_subset_1(sK2,X0,k4_xboole_0(sK2,X1)) ),
% 15.64/2.49      inference(light_normalisation,[status(thm)],[c_40711,c_40715]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_45364,plain,
% 15.64/2.49      ( k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(X1,k4_xboole_0(X1,sK2))) = k9_subset_1(sK2,X0,k4_xboole_0(sK2,k4_xboole_0(sK2,X1))) ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_0,c_40890]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_45414,plain,
% 15.64/2.49      ( k9_subset_1(u1_struct_0(sK0),X0,k1_setfam_1(k1_enumset1(X1,X1,sK2))) = k9_subset_1(sK2,X0,k1_setfam_1(k1_enumset1(sK2,sK2,X1))) ),
% 15.64/2.49      inference(demodulation,[status(thm)],[c_45364,c_5]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_54698,plain,
% 15.64/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.64/2.49      | r1_tarski(k9_subset_1(sK2,X0,k1_setfam_1(k1_enumset1(sK2,sK2,u1_struct_0(sK0)))),X1) = iProver_top ),
% 15.64/2.49      inference(demodulation,[status(thm)],[c_54623,c_45414]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_54699,plain,
% 15.64/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.64/2.49      | r1_tarski(k9_subset_1(sK2,X0,sK2),X1) = iProver_top ),
% 15.64/2.49      inference(light_normalisation,[status(thm)],[c_54698,c_2360]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_2205,plain,
% 15.64/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.64/2.49      | r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1) = iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_0,c_494]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_2208,plain,
% 15.64/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.64/2.49      | r1_tarski(k1_setfam_1(k1_enumset1(X2,X2,X0)),X1) = iProver_top ),
% 15.64/2.49      inference(demodulation,[status(thm)],[c_2205,c_5]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_54611,plain,
% 15.64/2.49      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,k1_setfam_1(k1_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),sK2))),X1) = iProver_top
% 15.64/2.49      | r1_tarski(sK2,X1) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_52083,c_2208]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_54740,plain,
% 15.64/2.49      ( r1_tarski(k9_subset_1(sK2,X0,k1_setfam_1(k1_enumset1(sK2,sK2,u1_struct_0(sK0)))),X1) = iProver_top
% 15.64/2.49      | r1_tarski(sK2,X1) != iProver_top ),
% 15.64/2.49      inference(demodulation,[status(thm)],[c_54611,c_45414]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_54741,plain,
% 15.64/2.49      ( r1_tarski(k9_subset_1(sK2,X0,sK2),X1) = iProver_top
% 15.64/2.49      | r1_tarski(sK2,X1) != iProver_top ),
% 15.64/2.49      inference(light_normalisation,[status(thm)],[c_54740,c_2360]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_12,negated_conjecture,
% 15.64/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.64/2.49      inference(cnf_transformation,[],[f37]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_485,plain,
% 15.64/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_491,plain,
% 15.64/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.64/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_8,plain,
% 15.64/2.49      ( ~ v2_tex_2(X0,X1)
% 15.64/2.49      | v2_tex_2(X2,X1)
% 15.64/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.64/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.64/2.49      | ~ r1_tarski(X2,X0)
% 15.64/2.49      | ~ l1_pre_topc(X1) ),
% 15.64/2.49      inference(cnf_transformation,[],[f35]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_489,plain,
% 15.64/2.49      ( v2_tex_2(X0,X1) != iProver_top
% 15.64/2.49      | v2_tex_2(X2,X1) = iProver_top
% 15.64/2.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.64/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.64/2.49      | r1_tarski(X2,X0) != iProver_top
% 15.64/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_1920,plain,
% 15.64/2.49      ( v2_tex_2(X0,X1) != iProver_top
% 15.64/2.49      | v2_tex_2(X2,X1) = iProver_top
% 15.64/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.64/2.49      | r1_tarski(X2,X0) != iProver_top
% 15.64/2.49      | r1_tarski(X2,u1_struct_0(X1)) != iProver_top
% 15.64/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_491,c_489]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_4828,plain,
% 15.64/2.49      ( v2_tex_2(X0,sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK1,sK0) != iProver_top
% 15.64/2.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 15.64/2.49      | r1_tarski(X0,sK1) != iProver_top
% 15.64/2.49      | l1_pre_topc(sK0) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_485,c_1920]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_13,negated_conjecture,
% 15.64/2.49      ( l1_pre_topc(sK0) ),
% 15.64/2.49      inference(cnf_transformation,[],[f36]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_14,plain,
% 15.64/2.49      ( l1_pre_topc(sK0) = iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_5771,plain,
% 15.64/2.49      ( r1_tarski(X0,sK1) != iProver_top
% 15.64/2.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 15.64/2.49      | v2_tex_2(sK1,sK0) != iProver_top
% 15.64/2.49      | v2_tex_2(X0,sK0) = iProver_top ),
% 15.64/2.49      inference(global_propositional_subsumption,
% 15.64/2.49                [status(thm)],
% 15.64/2.49                [c_4828,c_14]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_5772,plain,
% 15.64/2.49      ( v2_tex_2(X0,sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK1,sK0) != iProver_top
% 15.64/2.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 15.64/2.49      | r1_tarski(X0,sK1) != iProver_top ),
% 15.64/2.49      inference(renaming,[status(thm)],[c_5771]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_60183,plain,
% 15.64/2.49      ( v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK1,sK0) != iProver_top
% 15.64/2.49      | r1_tarski(k9_subset_1(sK2,X0,sK2),sK1) != iProver_top
% 15.64/2.49      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_54741,c_5772]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_16,plain,
% 15.64/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_10,negated_conjecture,
% 15.64/2.49      ( v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0) ),
% 15.64/2.49      inference(cnf_transformation,[],[f39]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_17,plain,
% 15.64/2.49      ( v2_tex_2(sK2,sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK1,sK0) = iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_591,plain,
% 15.64/2.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.64/2.49      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 15.64/2.49      inference(instantiation,[status(thm)],[c_7]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_592,plain,
% 15.64/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.64/2.49      | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_4827,plain,
% 15.64/2.49      ( v2_tex_2(X0,sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK2,sK0) != iProver_top
% 15.64/2.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 15.64/2.49      | r1_tarski(X0,sK2) != iProver_top
% 15.64/2.49      | l1_pre_topc(sK0) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_486,c_1920]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_3686,plain,
% 15.64/2.49      ( v2_tex_2(X0,sK0)
% 15.64/2.49      | ~ v2_tex_2(sK2,sK0)
% 15.64/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.64/2.49      | ~ r1_tarski(X0,sK2)
% 15.64/2.49      | ~ l1_pre_topc(sK0) ),
% 15.64/2.49      inference(resolution,[status(thm)],[c_8,c_11]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_3878,plain,
% 15.64/2.49      ( ~ r1_tarski(X0,sK2)
% 15.64/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.64/2.49      | ~ v2_tex_2(sK2,sK0)
% 15.64/2.49      | v2_tex_2(X0,sK0) ),
% 15.64/2.49      inference(global_propositional_subsumption,
% 15.64/2.49                [status(thm)],
% 15.64/2.49                [c_3686,c_13]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_3879,plain,
% 15.64/2.49      ( v2_tex_2(X0,sK0)
% 15.64/2.49      | ~ v2_tex_2(sK2,sK0)
% 15.64/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.64/2.49      | ~ r1_tarski(X0,sK2) ),
% 15.64/2.49      inference(renaming,[status(thm)],[c_3878]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_3904,plain,
% 15.64/2.49      ( v2_tex_2(X0,sK0)
% 15.64/2.49      | ~ v2_tex_2(sK2,sK0)
% 15.64/2.49      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 15.64/2.49      | ~ r1_tarski(X0,sK2) ),
% 15.64/2.49      inference(resolution,[status(thm)],[c_3879,c_6]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_3905,plain,
% 15.64/2.49      ( v2_tex_2(X0,sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK2,sK0) != iProver_top
% 15.64/2.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 15.64/2.49      | r1_tarski(X0,sK2) != iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_3904]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_5700,plain,
% 15.64/2.49      ( r1_tarski(X0,sK2) != iProver_top
% 15.64/2.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 15.64/2.49      | v2_tex_2(sK2,sK0) != iProver_top
% 15.64/2.49      | v2_tex_2(X0,sK0) = iProver_top ),
% 15.64/2.49      inference(global_propositional_subsumption,
% 15.64/2.49                [status(thm)],
% 15.64/2.49                [c_4827,c_3905]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_5701,plain,
% 15.64/2.49      ( v2_tex_2(X0,sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK2,sK0) != iProver_top
% 15.64/2.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 15.64/2.49      | r1_tarski(X0,sK2) != iProver_top ),
% 15.64/2.49      inference(renaming,[status(thm)],[c_5700]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_5708,plain,
% 15.64/2.49      ( v2_tex_2(k4_xboole_0(X0,X1),sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK2,sK0) != iProver_top
% 15.64/2.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 15.64/2.49      | r1_tarski(k4_xboole_0(X0,X1),sK2) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_494,c_5701]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_6753,plain,
% 15.64/2.49      ( v2_tex_2(k4_xboole_0(sK2,X0),sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK2,sK0) != iProver_top
% 15.64/2.49      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_492,c_5708]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_14658,plain,
% 15.64/2.49      ( v2_tex_2(sK2,sK0) != iProver_top
% 15.64/2.49      | v2_tex_2(k4_xboole_0(sK2,X0),sK0) = iProver_top ),
% 15.64/2.49      inference(global_propositional_subsumption,
% 15.64/2.49                [status(thm)],
% 15.64/2.49                [c_6753,c_14,c_16,c_592,c_693,c_811,c_944,c_2774]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_14659,plain,
% 15.64/2.49      ( v2_tex_2(k4_xboole_0(sK2,X0),sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK2,sK0) != iProver_top ),
% 15.64/2.49      inference(renaming,[status(thm)],[c_14658]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_14669,plain,
% 15.64/2.49      ( v2_tex_2(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK2,sK0) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_0,c_14659]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_14708,plain,
% 15.64/2.49      ( v2_tex_2(k1_setfam_1(k1_enumset1(X0,X0,sK2)),sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK2,sK0) != iProver_top ),
% 15.64/2.49      inference(demodulation,[status(thm)],[c_14669,c_5]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_54629,plain,
% 15.64/2.49      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0,k1_setfam_1(k1_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),sK2))),sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK2,sK0) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_52083,c_14708]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_54673,plain,
% 15.64/2.49      ( v2_tex_2(k9_subset_1(sK2,X0,k1_setfam_1(k1_enumset1(sK2,sK2,u1_struct_0(sK0)))),sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK2,sK0) != iProver_top ),
% 15.64/2.49      inference(demodulation,[status(thm)],[c_54629,c_45414]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_54674,plain,
% 15.64/2.49      ( v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 15.64/2.49      | v2_tex_2(sK2,sK0) != iProver_top ),
% 15.64/2.49      inference(light_normalisation,[status(thm)],[c_54673,c_2360]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_3190,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_1748,c_530]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_3194,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k9_subset_1(sK2,X0,sK2) ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_2509,c_530]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_3216,plain,
% 15.64/2.49      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
% 15.64/2.49      inference(light_normalisation,[status(thm)],[c_3190,c_3194]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_9,negated_conjecture,
% 15.64/2.49      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 15.64/2.49      inference(cnf_transformation,[],[f40]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_488,plain,
% 15.64/2.49      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 15.64/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_4240,plain,
% 15.64/2.49      ( v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
% 15.64/2.49      inference(demodulation,[status(thm)],[c_3216,c_488]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_55482,plain,
% 15.64/2.49      ( v2_tex_2(sK2,sK0) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_54674,c_4240]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_60760,plain,
% 15.64/2.49      ( r1_tarski(k9_subset_1(sK2,X0,sK2),sK1) != iProver_top
% 15.64/2.49      | v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top ),
% 15.64/2.49      inference(global_propositional_subsumption,
% 15.64/2.49                [status(thm)],
% 15.64/2.49                [c_60183,c_16,c_17,c_592,c_55482]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_60761,plain,
% 15.64/2.49      ( v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 15.64/2.49      | r1_tarski(k9_subset_1(sK2,X0,sK2),sK1) != iProver_top ),
% 15.64/2.49      inference(renaming,[status(thm)],[c_60760]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_60769,plain,
% 15.64/2.49      ( v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 15.64/2.49      | r1_tarski(X0,sK1) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_54699,c_60761]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_61253,plain,
% 15.64/2.49      ( r1_tarski(sK1,sK1) != iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_60769,c_4240]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_1749,plain,
% 15.64/2.49      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_485,c_490]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_2361,plain,
% 15.64/2.49      ( k1_setfam_1(k1_enumset1(sK1,sK1,u1_struct_0(sK0))) = sK1 ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_1749,c_521]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(c_2522,plain,
% 15.64/2.49      ( r1_tarski(sK1,sK1) = iProver_top ),
% 15.64/2.49      inference(superposition,[status(thm)],[c_2361,c_994]) ).
% 15.64/2.49  
% 15.64/2.49  cnf(contradiction,plain,
% 15.64/2.49      ( $false ),
% 15.64/2.49      inference(minisat,[status(thm)],[c_61253,c_2522]) ).
% 15.64/2.49  
% 15.64/2.49  
% 15.64/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.64/2.49  
% 15.64/2.49  ------                               Statistics
% 15.64/2.49  
% 15.64/2.49  ------ Selected
% 15.64/2.49  
% 15.64/2.49  total_time:                             1.934
% 15.64/2.49  
%------------------------------------------------------------------------------
