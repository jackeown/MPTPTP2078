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
% DateTime   : Thu Dec  3 12:25:50 EST 2020

% Result     : Theorem 15.97s
% Output     : CNFRefutation 15.97s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 946 expanded)
%              Number of clauses        :   66 ( 296 expanded)
%              Number of leaves         :   15 ( 271 expanded)
%              Depth                    :   17
%              Number of atoms          :  251 (2004 expanded)
%              Number of equality atoms :   98 ( 775 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f26,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f34,f28])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f28,f29])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f28,f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_423,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_430,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_431,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_430,c_1])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_427,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_432,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_427,c_6])).

cnf(c_1113,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_431,c_432])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_801,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_1199,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_801,c_6])).

cnf(c_2357,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X0,X1,X0) ),
    inference(superposition,[status(thm)],[c_1113,c_1199])).

cnf(c_11826,plain,
    ( k9_subset_1(X0,X1,X0) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2357,c_432])).

cnf(c_41500,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(X0,sK1,X0) ),
    inference(superposition,[status(thm)],[c_423,c_11826])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_428,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1680,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_431,c_428])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_429,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6838,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1680,c_429])).

cnf(c_29252,plain,
    ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6838,c_431])).

cnf(c_29262,plain,
    ( m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_29252])).

cnf(c_2353,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X0,X1,X0) ),
    inference(superposition,[status(thm)],[c_1113,c_801])).

cnf(c_29333,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29262,c_2353])).

cnf(c_42049,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_41500,c_29333])).

cnf(c_1112,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,sK1)) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
    inference(superposition,[status(thm)],[c_423,c_432])).

cnf(c_2341,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(sK1,X0,sK1) ),
    inference(demodulation,[status(thm)],[c_1113,c_1112])).

cnf(c_42114,plain,
    ( m1_subset_1(k9_subset_1(sK1,X0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42049,c_2341])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_424,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1678,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_424,c_428])).

cnf(c_1852,plain,
    ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_429])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2209,plain,
    ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1852,c_16])).

cnf(c_2218,plain,
    ( m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2209])).

cnf(c_2232,plain,
    ( m1_subset_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2218,c_6])).

cnf(c_2474,plain,
    ( m1_subset_1(k9_subset_1(X0,sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2232,c_2357])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_131,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_132,plain,
    ( ~ v2_tex_2(X0,sK0)
    | v2_tex_2(X1,sK0)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_131])).

cnf(c_156,plain,
    ( ~ v2_tex_2(X0,sK0)
    | v2_tex_2(X1,sK0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1 != X2
    | X0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_132])).

cnf(c_157,plain,
    ( ~ v2_tex_2(X0,sK0)
    | v2_tex_2(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_156])).

cnf(c_422,plain,
    ( v2_tex_2(X0,sK0) != iProver_top
    | v2_tex_2(X1,sK0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_600,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_423,c_422])).

cnf(c_2482,plain,
    ( v2_tex_2(k9_subset_1(X0,sK2,X0),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | m1_subset_1(k9_subset_1(X0,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2474,c_600])).

cnf(c_42354,plain,
    ( v2_tex_2(k9_subset_1(sK1,sK2,sK1),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_42114,c_2482])).

cnf(c_599,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_424,c_422])).

cnf(c_2483,plain,
    ( v2_tex_2(k9_subset_1(X0,sK2,X0),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | m1_subset_1(k9_subset_1(X0,sK2,X0),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2474,c_599])).

cnf(c_29574,plain,
    ( v2_tex_2(k9_subset_1(X0,sK2,X0),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_29333,c_2483])).

cnf(c_7079,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_2353,c_0])).

cnf(c_9118,plain,
    ( k9_subset_1(X0,X1,X0) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_7079,c_2353])).

cnf(c_1111,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(superposition,[status(thm)],[c_424,c_432])).

cnf(c_9,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_426,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1343,plain,
    ( v2_tex_2(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1111,c_426])).

cnf(c_2339,plain,
    ( v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1113,c_1343])).

cnf(c_10002,plain,
    ( v2_tex_2(k9_subset_1(sK1,sK2,sK1),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9118,c_2339])).

cnf(c_31501,plain,
    ( v2_tex_2(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_29574,c_10002])).

cnf(c_10,negated_conjecture,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,plain,
    ( v2_tex_2(sK2,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42354,c_31501,c_10002,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.97/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.97/2.49  
% 15.97/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.97/2.49  
% 15.97/2.49  ------  iProver source info
% 15.97/2.49  
% 15.97/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.97/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.97/2.49  git: non_committed_changes: false
% 15.97/2.49  git: last_make_outside_of_git: false
% 15.97/2.49  
% 15.97/2.49  ------ 
% 15.97/2.49  
% 15.97/2.49  ------ Input Options
% 15.97/2.49  
% 15.97/2.49  --out_options                           all
% 15.97/2.49  --tptp_safe_out                         true
% 15.97/2.49  --problem_path                          ""
% 15.97/2.49  --include_path                          ""
% 15.97/2.49  --clausifier                            res/vclausify_rel
% 15.97/2.49  --clausifier_options                    ""
% 15.97/2.49  --stdin                                 false
% 15.97/2.49  --stats_out                             all
% 15.97/2.49  
% 15.97/2.49  ------ General Options
% 15.97/2.49  
% 15.97/2.49  --fof                                   false
% 15.97/2.49  --time_out_real                         305.
% 15.97/2.49  --time_out_virtual                      -1.
% 15.97/2.49  --symbol_type_check                     false
% 15.97/2.49  --clausify_out                          false
% 15.97/2.49  --sig_cnt_out                           false
% 15.97/2.49  --trig_cnt_out                          false
% 15.97/2.49  --trig_cnt_out_tolerance                1.
% 15.97/2.49  --trig_cnt_out_sk_spl                   false
% 15.97/2.49  --abstr_cl_out                          false
% 15.97/2.49  
% 15.97/2.49  ------ Global Options
% 15.97/2.49  
% 15.97/2.49  --schedule                              default
% 15.97/2.49  --add_important_lit                     false
% 15.97/2.49  --prop_solver_per_cl                    1000
% 15.97/2.49  --min_unsat_core                        false
% 15.97/2.49  --soft_assumptions                      false
% 15.97/2.49  --soft_lemma_size                       3
% 15.97/2.49  --prop_impl_unit_size                   0
% 15.97/2.49  --prop_impl_unit                        []
% 15.97/2.49  --share_sel_clauses                     true
% 15.97/2.49  --reset_solvers                         false
% 15.97/2.49  --bc_imp_inh                            [conj_cone]
% 15.97/2.49  --conj_cone_tolerance                   3.
% 15.97/2.49  --extra_neg_conj                        none
% 15.97/2.49  --large_theory_mode                     true
% 15.97/2.49  --prolific_symb_bound                   200
% 15.97/2.49  --lt_threshold                          2000
% 15.97/2.49  --clause_weak_htbl                      true
% 15.97/2.49  --gc_record_bc_elim                     false
% 15.97/2.49  
% 15.97/2.49  ------ Preprocessing Options
% 15.97/2.49  
% 15.97/2.49  --preprocessing_flag                    true
% 15.97/2.49  --time_out_prep_mult                    0.1
% 15.97/2.49  --splitting_mode                        input
% 15.97/2.49  --splitting_grd                         true
% 15.97/2.49  --splitting_cvd                         false
% 15.97/2.49  --splitting_cvd_svl                     false
% 15.97/2.49  --splitting_nvd                         32
% 15.97/2.49  --sub_typing                            true
% 15.97/2.49  --prep_gs_sim                           true
% 15.97/2.49  --prep_unflatten                        true
% 15.97/2.49  --prep_res_sim                          true
% 15.97/2.49  --prep_upred                            true
% 15.97/2.49  --prep_sem_filter                       exhaustive
% 15.97/2.49  --prep_sem_filter_out                   false
% 15.97/2.49  --pred_elim                             true
% 15.97/2.49  --res_sim_input                         true
% 15.97/2.49  --eq_ax_congr_red                       true
% 15.97/2.49  --pure_diseq_elim                       true
% 15.97/2.49  --brand_transform                       false
% 15.97/2.49  --non_eq_to_eq                          false
% 15.97/2.49  --prep_def_merge                        true
% 15.97/2.49  --prep_def_merge_prop_impl              false
% 15.97/2.49  --prep_def_merge_mbd                    true
% 15.97/2.49  --prep_def_merge_tr_red                 false
% 15.97/2.49  --prep_def_merge_tr_cl                  false
% 15.97/2.49  --smt_preprocessing                     true
% 15.97/2.49  --smt_ac_axioms                         fast
% 15.97/2.49  --preprocessed_out                      false
% 15.97/2.49  --preprocessed_stats                    false
% 15.97/2.49  
% 15.97/2.49  ------ Abstraction refinement Options
% 15.97/2.49  
% 15.97/2.49  --abstr_ref                             []
% 15.97/2.49  --abstr_ref_prep                        false
% 15.97/2.49  --abstr_ref_until_sat                   false
% 15.97/2.49  --abstr_ref_sig_restrict                funpre
% 15.97/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.97/2.49  --abstr_ref_under                       []
% 15.97/2.49  
% 15.97/2.49  ------ SAT Options
% 15.97/2.49  
% 15.97/2.49  --sat_mode                              false
% 15.97/2.49  --sat_fm_restart_options                ""
% 15.97/2.49  --sat_gr_def                            false
% 15.97/2.49  --sat_epr_types                         true
% 15.97/2.49  --sat_non_cyclic_types                  false
% 15.97/2.49  --sat_finite_models                     false
% 15.97/2.49  --sat_fm_lemmas                         false
% 15.97/2.49  --sat_fm_prep                           false
% 15.97/2.49  --sat_fm_uc_incr                        true
% 15.97/2.49  --sat_out_model                         small
% 15.97/2.49  --sat_out_clauses                       false
% 15.97/2.49  
% 15.97/2.49  ------ QBF Options
% 15.97/2.49  
% 15.97/2.49  --qbf_mode                              false
% 15.97/2.49  --qbf_elim_univ                         false
% 15.97/2.49  --qbf_dom_inst                          none
% 15.97/2.49  --qbf_dom_pre_inst                      false
% 15.97/2.49  --qbf_sk_in                             false
% 15.97/2.49  --qbf_pred_elim                         true
% 15.97/2.49  --qbf_split                             512
% 15.97/2.49  
% 15.97/2.49  ------ BMC1 Options
% 15.97/2.49  
% 15.97/2.49  --bmc1_incremental                      false
% 15.97/2.49  --bmc1_axioms                           reachable_all
% 15.97/2.49  --bmc1_min_bound                        0
% 15.97/2.49  --bmc1_max_bound                        -1
% 15.97/2.49  --bmc1_max_bound_default                -1
% 15.97/2.49  --bmc1_symbol_reachability              true
% 15.97/2.49  --bmc1_property_lemmas                  false
% 15.97/2.49  --bmc1_k_induction                      false
% 15.97/2.49  --bmc1_non_equiv_states                 false
% 15.97/2.49  --bmc1_deadlock                         false
% 15.97/2.49  --bmc1_ucm                              false
% 15.97/2.49  --bmc1_add_unsat_core                   none
% 15.97/2.49  --bmc1_unsat_core_children              false
% 15.97/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.97/2.49  --bmc1_out_stat                         full
% 15.97/2.49  --bmc1_ground_init                      false
% 15.97/2.49  --bmc1_pre_inst_next_state              false
% 15.97/2.49  --bmc1_pre_inst_state                   false
% 15.97/2.49  --bmc1_pre_inst_reach_state             false
% 15.97/2.49  --bmc1_out_unsat_core                   false
% 15.97/2.49  --bmc1_aig_witness_out                  false
% 15.97/2.49  --bmc1_verbose                          false
% 15.97/2.49  --bmc1_dump_clauses_tptp                false
% 15.97/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.97/2.49  --bmc1_dump_file                        -
% 15.97/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.97/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.97/2.49  --bmc1_ucm_extend_mode                  1
% 15.97/2.49  --bmc1_ucm_init_mode                    2
% 15.97/2.49  --bmc1_ucm_cone_mode                    none
% 15.97/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.97/2.49  --bmc1_ucm_relax_model                  4
% 15.97/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.97/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.97/2.49  --bmc1_ucm_layered_model                none
% 15.97/2.49  --bmc1_ucm_max_lemma_size               10
% 15.97/2.49  
% 15.97/2.49  ------ AIG Options
% 15.97/2.49  
% 15.97/2.49  --aig_mode                              false
% 15.97/2.49  
% 15.97/2.49  ------ Instantiation Options
% 15.97/2.49  
% 15.97/2.49  --instantiation_flag                    true
% 15.97/2.49  --inst_sos_flag                         true
% 15.97/2.49  --inst_sos_phase                        true
% 15.97/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.97/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.97/2.49  --inst_lit_sel_side                     num_symb
% 15.97/2.49  --inst_solver_per_active                1400
% 15.97/2.49  --inst_solver_calls_frac                1.
% 15.97/2.49  --inst_passive_queue_type               priority_queues
% 15.97/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.97/2.49  --inst_passive_queues_freq              [25;2]
% 15.97/2.49  --inst_dismatching                      true
% 15.97/2.49  --inst_eager_unprocessed_to_passive     true
% 15.97/2.49  --inst_prop_sim_given                   true
% 15.97/2.49  --inst_prop_sim_new                     false
% 15.97/2.49  --inst_subs_new                         false
% 15.97/2.49  --inst_eq_res_simp                      false
% 15.97/2.49  --inst_subs_given                       false
% 15.97/2.49  --inst_orphan_elimination               true
% 15.97/2.49  --inst_learning_loop_flag               true
% 15.97/2.49  --inst_learning_start                   3000
% 15.97/2.49  --inst_learning_factor                  2
% 15.97/2.49  --inst_start_prop_sim_after_learn       3
% 15.97/2.49  --inst_sel_renew                        solver
% 15.97/2.49  --inst_lit_activity_flag                true
% 15.97/2.49  --inst_restr_to_given                   false
% 15.97/2.49  --inst_activity_threshold               500
% 15.97/2.49  --inst_out_proof                        true
% 15.97/2.49  
% 15.97/2.49  ------ Resolution Options
% 15.97/2.49  
% 15.97/2.49  --resolution_flag                       true
% 15.97/2.49  --res_lit_sel                           adaptive
% 15.97/2.49  --res_lit_sel_side                      none
% 15.97/2.49  --res_ordering                          kbo
% 15.97/2.49  --res_to_prop_solver                    active
% 15.97/2.49  --res_prop_simpl_new                    false
% 15.97/2.49  --res_prop_simpl_given                  true
% 15.97/2.49  --res_passive_queue_type                priority_queues
% 15.97/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.97/2.49  --res_passive_queues_freq               [15;5]
% 15.97/2.49  --res_forward_subs                      full
% 15.97/2.49  --res_backward_subs                     full
% 15.97/2.49  --res_forward_subs_resolution           true
% 15.97/2.49  --res_backward_subs_resolution          true
% 15.97/2.49  --res_orphan_elimination                true
% 15.97/2.49  --res_time_limit                        2.
% 15.97/2.49  --res_out_proof                         true
% 15.97/2.49  
% 15.97/2.49  ------ Superposition Options
% 15.97/2.49  
% 15.97/2.49  --superposition_flag                    true
% 15.97/2.49  --sup_passive_queue_type                priority_queues
% 15.97/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.97/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.97/2.49  --demod_completeness_check              fast
% 15.97/2.49  --demod_use_ground                      true
% 15.97/2.49  --sup_to_prop_solver                    passive
% 15.97/2.49  --sup_prop_simpl_new                    true
% 15.97/2.49  --sup_prop_simpl_given                  true
% 15.97/2.49  --sup_fun_splitting                     true
% 15.97/2.49  --sup_smt_interval                      50000
% 15.97/2.49  
% 15.97/2.49  ------ Superposition Simplification Setup
% 15.97/2.49  
% 15.97/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.97/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.97/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.97/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.97/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.97/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.97/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.97/2.49  --sup_immed_triv                        [TrivRules]
% 15.97/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.97/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.97/2.49  --sup_immed_bw_main                     []
% 15.97/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.97/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.97/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.97/2.49  --sup_input_bw                          []
% 15.97/2.49  
% 15.97/2.49  ------ Combination Options
% 15.97/2.49  
% 15.97/2.49  --comb_res_mult                         3
% 15.97/2.49  --comb_sup_mult                         2
% 15.97/2.49  --comb_inst_mult                        10
% 15.97/2.49  
% 15.97/2.49  ------ Debug Options
% 15.97/2.49  
% 15.97/2.49  --dbg_backtrace                         false
% 15.97/2.49  --dbg_dump_prop_clauses                 false
% 15.97/2.49  --dbg_dump_prop_clauses_file            -
% 15.97/2.49  --dbg_out_stat                          false
% 15.97/2.49  ------ Parsing...
% 15.97/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.97/2.49  
% 15.97/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.97/2.49  
% 15.97/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.97/2.49  
% 15.97/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.97/2.49  ------ Proving...
% 15.97/2.49  ------ Problem Properties 
% 15.97/2.49  
% 15.97/2.49  
% 15.97/2.49  clauses                                 12
% 15.97/2.49  conjectures                             4
% 15.97/2.49  EPR                                     1
% 15.97/2.49  Horn                                    11
% 15.97/2.49  unary                                   7
% 15.97/2.49  binary                                  4
% 15.97/2.49  lits                                    20
% 15.97/2.49  lits eq                                 5
% 15.97/2.49  fd_pure                                 0
% 15.97/2.49  fd_pseudo                               0
% 15.97/2.49  fd_cond                                 0
% 15.97/2.49  fd_pseudo_cond                          0
% 15.97/2.49  AC symbols                              0
% 15.97/2.49  
% 15.97/2.49  ------ Schedule dynamic 5 is on 
% 15.97/2.49  
% 15.97/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.97/2.49  
% 15.97/2.49  
% 15.97/2.49  ------ 
% 15.97/2.49  Current options:
% 15.97/2.49  ------ 
% 15.97/2.49  
% 15.97/2.49  ------ Input Options
% 15.97/2.49  
% 15.97/2.49  --out_options                           all
% 15.97/2.49  --tptp_safe_out                         true
% 15.97/2.49  --problem_path                          ""
% 15.97/2.49  --include_path                          ""
% 15.97/2.49  --clausifier                            res/vclausify_rel
% 15.97/2.49  --clausifier_options                    ""
% 15.97/2.49  --stdin                                 false
% 15.97/2.49  --stats_out                             all
% 15.97/2.49  
% 15.97/2.49  ------ General Options
% 15.97/2.49  
% 15.97/2.49  --fof                                   false
% 15.97/2.49  --time_out_real                         305.
% 15.97/2.49  --time_out_virtual                      -1.
% 15.97/2.49  --symbol_type_check                     false
% 15.97/2.49  --clausify_out                          false
% 15.97/2.49  --sig_cnt_out                           false
% 15.97/2.49  --trig_cnt_out                          false
% 15.97/2.49  --trig_cnt_out_tolerance                1.
% 15.97/2.49  --trig_cnt_out_sk_spl                   false
% 15.97/2.49  --abstr_cl_out                          false
% 15.97/2.49  
% 15.97/2.49  ------ Global Options
% 15.97/2.49  
% 15.97/2.49  --schedule                              default
% 15.97/2.49  --add_important_lit                     false
% 15.97/2.49  --prop_solver_per_cl                    1000
% 15.97/2.49  --min_unsat_core                        false
% 15.97/2.49  --soft_assumptions                      false
% 15.97/2.49  --soft_lemma_size                       3
% 15.97/2.49  --prop_impl_unit_size                   0
% 15.97/2.49  --prop_impl_unit                        []
% 15.97/2.49  --share_sel_clauses                     true
% 15.97/2.49  --reset_solvers                         false
% 15.97/2.49  --bc_imp_inh                            [conj_cone]
% 15.97/2.49  --conj_cone_tolerance                   3.
% 15.97/2.49  --extra_neg_conj                        none
% 15.97/2.49  --large_theory_mode                     true
% 15.97/2.49  --prolific_symb_bound                   200
% 15.97/2.49  --lt_threshold                          2000
% 15.97/2.49  --clause_weak_htbl                      true
% 15.97/2.49  --gc_record_bc_elim                     false
% 15.97/2.49  
% 15.97/2.49  ------ Preprocessing Options
% 15.97/2.49  
% 15.97/2.49  --preprocessing_flag                    true
% 15.97/2.49  --time_out_prep_mult                    0.1
% 15.97/2.49  --splitting_mode                        input
% 15.97/2.49  --splitting_grd                         true
% 15.97/2.49  --splitting_cvd                         false
% 15.97/2.49  --splitting_cvd_svl                     false
% 15.97/2.49  --splitting_nvd                         32
% 15.97/2.49  --sub_typing                            true
% 15.97/2.49  --prep_gs_sim                           true
% 15.97/2.49  --prep_unflatten                        true
% 15.97/2.49  --prep_res_sim                          true
% 15.97/2.49  --prep_upred                            true
% 15.97/2.49  --prep_sem_filter                       exhaustive
% 15.97/2.49  --prep_sem_filter_out                   false
% 15.97/2.49  --pred_elim                             true
% 15.97/2.49  --res_sim_input                         true
% 15.97/2.49  --eq_ax_congr_red                       true
% 15.97/2.49  --pure_diseq_elim                       true
% 15.97/2.49  --brand_transform                       false
% 15.97/2.49  --non_eq_to_eq                          false
% 15.97/2.49  --prep_def_merge                        true
% 15.97/2.49  --prep_def_merge_prop_impl              false
% 15.97/2.49  --prep_def_merge_mbd                    true
% 15.97/2.49  --prep_def_merge_tr_red                 false
% 15.97/2.49  --prep_def_merge_tr_cl                  false
% 15.97/2.49  --smt_preprocessing                     true
% 15.97/2.49  --smt_ac_axioms                         fast
% 15.97/2.49  --preprocessed_out                      false
% 15.97/2.49  --preprocessed_stats                    false
% 15.97/2.49  
% 15.97/2.49  ------ Abstraction refinement Options
% 15.97/2.49  
% 15.97/2.49  --abstr_ref                             []
% 15.97/2.49  --abstr_ref_prep                        false
% 15.97/2.49  --abstr_ref_until_sat                   false
% 15.97/2.49  --abstr_ref_sig_restrict                funpre
% 15.97/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.97/2.49  --abstr_ref_under                       []
% 15.97/2.49  
% 15.97/2.49  ------ SAT Options
% 15.97/2.49  
% 15.97/2.49  --sat_mode                              false
% 15.97/2.49  --sat_fm_restart_options                ""
% 15.97/2.49  --sat_gr_def                            false
% 15.97/2.49  --sat_epr_types                         true
% 15.97/2.49  --sat_non_cyclic_types                  false
% 15.97/2.49  --sat_finite_models                     false
% 15.97/2.49  --sat_fm_lemmas                         false
% 15.97/2.49  --sat_fm_prep                           false
% 15.97/2.49  --sat_fm_uc_incr                        true
% 15.97/2.49  --sat_out_model                         small
% 15.97/2.49  --sat_out_clauses                       false
% 15.97/2.49  
% 15.97/2.49  ------ QBF Options
% 15.97/2.49  
% 15.97/2.49  --qbf_mode                              false
% 15.97/2.49  --qbf_elim_univ                         false
% 15.97/2.49  --qbf_dom_inst                          none
% 15.97/2.49  --qbf_dom_pre_inst                      false
% 15.97/2.49  --qbf_sk_in                             false
% 15.97/2.49  --qbf_pred_elim                         true
% 15.97/2.49  --qbf_split                             512
% 15.97/2.49  
% 15.97/2.49  ------ BMC1 Options
% 15.97/2.49  
% 15.97/2.49  --bmc1_incremental                      false
% 15.97/2.49  --bmc1_axioms                           reachable_all
% 15.97/2.49  --bmc1_min_bound                        0
% 15.97/2.49  --bmc1_max_bound                        -1
% 15.97/2.49  --bmc1_max_bound_default                -1
% 15.97/2.49  --bmc1_symbol_reachability              true
% 15.97/2.49  --bmc1_property_lemmas                  false
% 15.97/2.49  --bmc1_k_induction                      false
% 15.97/2.49  --bmc1_non_equiv_states                 false
% 15.97/2.49  --bmc1_deadlock                         false
% 15.97/2.49  --bmc1_ucm                              false
% 15.97/2.49  --bmc1_add_unsat_core                   none
% 15.97/2.49  --bmc1_unsat_core_children              false
% 15.97/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.97/2.49  --bmc1_out_stat                         full
% 15.97/2.49  --bmc1_ground_init                      false
% 15.97/2.49  --bmc1_pre_inst_next_state              false
% 15.97/2.49  --bmc1_pre_inst_state                   false
% 15.97/2.49  --bmc1_pre_inst_reach_state             false
% 15.97/2.49  --bmc1_out_unsat_core                   false
% 15.97/2.49  --bmc1_aig_witness_out                  false
% 15.97/2.49  --bmc1_verbose                          false
% 15.97/2.49  --bmc1_dump_clauses_tptp                false
% 15.97/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.97/2.49  --bmc1_dump_file                        -
% 15.97/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.97/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.97/2.49  --bmc1_ucm_extend_mode                  1
% 15.97/2.49  --bmc1_ucm_init_mode                    2
% 15.97/2.49  --bmc1_ucm_cone_mode                    none
% 15.97/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.97/2.49  --bmc1_ucm_relax_model                  4
% 15.97/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.97/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.97/2.49  --bmc1_ucm_layered_model                none
% 15.97/2.49  --bmc1_ucm_max_lemma_size               10
% 15.97/2.49  
% 15.97/2.49  ------ AIG Options
% 15.97/2.49  
% 15.97/2.49  --aig_mode                              false
% 15.97/2.49  
% 15.97/2.49  ------ Instantiation Options
% 15.97/2.49  
% 15.97/2.49  --instantiation_flag                    true
% 15.97/2.49  --inst_sos_flag                         true
% 15.97/2.49  --inst_sos_phase                        true
% 15.97/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.97/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.97/2.49  --inst_lit_sel_side                     none
% 15.97/2.49  --inst_solver_per_active                1400
% 15.97/2.49  --inst_solver_calls_frac                1.
% 15.97/2.49  --inst_passive_queue_type               priority_queues
% 15.97/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.97/2.49  --inst_passive_queues_freq              [25;2]
% 15.97/2.49  --inst_dismatching                      true
% 15.97/2.49  --inst_eager_unprocessed_to_passive     true
% 15.97/2.49  --inst_prop_sim_given                   true
% 15.97/2.49  --inst_prop_sim_new                     false
% 15.97/2.49  --inst_subs_new                         false
% 15.97/2.49  --inst_eq_res_simp                      false
% 15.97/2.49  --inst_subs_given                       false
% 15.97/2.49  --inst_orphan_elimination               true
% 15.97/2.49  --inst_learning_loop_flag               true
% 15.97/2.49  --inst_learning_start                   3000
% 15.97/2.49  --inst_learning_factor                  2
% 15.97/2.49  --inst_start_prop_sim_after_learn       3
% 15.97/2.49  --inst_sel_renew                        solver
% 15.97/2.49  --inst_lit_activity_flag                true
% 15.97/2.49  --inst_restr_to_given                   false
% 15.97/2.49  --inst_activity_threshold               500
% 15.97/2.49  --inst_out_proof                        true
% 15.97/2.49  
% 15.97/2.49  ------ Resolution Options
% 15.97/2.49  
% 15.97/2.49  --resolution_flag                       false
% 15.97/2.49  --res_lit_sel                           adaptive
% 15.97/2.49  --res_lit_sel_side                      none
% 15.97/2.49  --res_ordering                          kbo
% 15.97/2.49  --res_to_prop_solver                    active
% 15.97/2.49  --res_prop_simpl_new                    false
% 15.97/2.49  --res_prop_simpl_given                  true
% 15.97/2.49  --res_passive_queue_type                priority_queues
% 15.97/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.97/2.49  --res_passive_queues_freq               [15;5]
% 15.97/2.49  --res_forward_subs                      full
% 15.97/2.49  --res_backward_subs                     full
% 15.97/2.49  --res_forward_subs_resolution           true
% 15.97/2.49  --res_backward_subs_resolution          true
% 15.97/2.49  --res_orphan_elimination                true
% 15.97/2.49  --res_time_limit                        2.
% 15.97/2.49  --res_out_proof                         true
% 15.97/2.49  
% 15.97/2.49  ------ Superposition Options
% 15.97/2.49  
% 15.97/2.49  --superposition_flag                    true
% 15.97/2.49  --sup_passive_queue_type                priority_queues
% 15.97/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.97/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.97/2.49  --demod_completeness_check              fast
% 15.97/2.49  --demod_use_ground                      true
% 15.97/2.49  --sup_to_prop_solver                    passive
% 15.97/2.49  --sup_prop_simpl_new                    true
% 15.97/2.49  --sup_prop_simpl_given                  true
% 15.97/2.49  --sup_fun_splitting                     true
% 15.97/2.49  --sup_smt_interval                      50000
% 15.97/2.49  
% 15.97/2.49  ------ Superposition Simplification Setup
% 15.97/2.49  
% 15.97/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.97/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.97/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.97/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.97/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.97/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.97/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.97/2.49  --sup_immed_triv                        [TrivRules]
% 15.97/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.97/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.97/2.49  --sup_immed_bw_main                     []
% 15.97/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.97/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.97/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.97/2.49  --sup_input_bw                          []
% 15.97/2.49  
% 15.97/2.49  ------ Combination Options
% 15.97/2.49  
% 15.97/2.49  --comb_res_mult                         3
% 15.97/2.49  --comb_sup_mult                         2
% 15.97/2.49  --comb_inst_mult                        10
% 15.97/2.49  
% 15.97/2.49  ------ Debug Options
% 15.97/2.49  
% 15.97/2.49  --dbg_backtrace                         false
% 15.97/2.49  --dbg_dump_prop_clauses                 false
% 15.97/2.49  --dbg_dump_prop_clauses_file            -
% 15.97/2.49  --dbg_out_stat                          false
% 15.97/2.49  
% 15.97/2.49  
% 15.97/2.49  
% 15.97/2.49  
% 15.97/2.49  ------ Proving...
% 15.97/2.49  
% 15.97/2.49  
% 15.97/2.49  % SZS status Theorem for theBenchmark.p
% 15.97/2.49  
% 15.97/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.97/2.49  
% 15.97/2.49  fof(f12,conjecture,(
% 15.97/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 15.97/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.49  
% 15.97/2.49  fof(f13,negated_conjecture,(
% 15.97/2.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 15.97/2.49    inference(negated_conjecture,[],[f12])).
% 15.97/2.49  
% 15.97/2.49  fof(f21,plain,(
% 15.97/2.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.97/2.49    inference(ennf_transformation,[],[f13])).
% 15.97/2.49  
% 15.97/2.49  fof(f22,plain,(
% 15.97/2.49    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.97/2.49    inference(flattening,[],[f21])).
% 15.97/2.49  
% 15.97/2.49  fof(f25,plain,(
% 15.97/2.49    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & (v2_tex_2(sK2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.97/2.49    introduced(choice_axiom,[])).
% 15.97/2.49  
% 15.97/2.49  fof(f24,plain,(
% 15.97/2.49    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.97/2.49    introduced(choice_axiom,[])).
% 15.97/2.49  
% 15.97/2.49  fof(f23,plain,(
% 15.97/2.49    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 15.97/2.49    introduced(choice_axiom,[])).
% 15.97/2.49  
% 15.97/2.49  fof(f26,plain,(
% 15.97/2.49    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 15.97/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25,f24,f23])).
% 15.97/2.49  
% 15.97/2.49  fof(f39,plain,(
% 15.97/2.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.97/2.49    inference(cnf_transformation,[],[f26])).
% 15.97/2.49  
% 15.97/2.49  fof(f5,axiom,(
% 15.97/2.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 15.97/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.49  
% 15.97/2.49  fof(f31,plain,(
% 15.97/2.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 15.97/2.49    inference(cnf_transformation,[],[f5])).
% 15.97/2.49  
% 15.97/2.49  fof(f4,axiom,(
% 15.97/2.49    ! [X0] : k2_subset_1(X0) = X0),
% 15.97/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.49  
% 15.97/2.49  fof(f30,plain,(
% 15.97/2.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 15.97/2.49    inference(cnf_transformation,[],[f4])).
% 15.97/2.49  
% 15.97/2.49  fof(f8,axiom,(
% 15.97/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 15.97/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.49  
% 15.97/2.49  fof(f17,plain,(
% 15.97/2.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.97/2.49    inference(ennf_transformation,[],[f8])).
% 15.97/2.49  
% 15.97/2.49  fof(f34,plain,(
% 15.97/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.97/2.49    inference(cnf_transformation,[],[f17])).
% 15.97/2.49  
% 15.97/2.49  fof(f2,axiom,(
% 15.97/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.97/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.49  
% 15.97/2.49  fof(f28,plain,(
% 15.97/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.97/2.49    inference(cnf_transformation,[],[f2])).
% 15.97/2.49  
% 15.97/2.49  fof(f44,plain,(
% 15.97/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.97/2.49    inference(definition_unfolding,[],[f34,f28])).
% 15.97/2.49  
% 15.97/2.49  fof(f9,axiom,(
% 15.97/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.97/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.49  
% 15.97/2.49  fof(f35,plain,(
% 15.97/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.97/2.49    inference(cnf_transformation,[],[f9])).
% 15.97/2.49  
% 15.97/2.49  fof(f3,axiom,(
% 15.97/2.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.97/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.49  
% 15.97/2.49  fof(f29,plain,(
% 15.97/2.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.97/2.49    inference(cnf_transformation,[],[f3])).
% 15.97/2.49  
% 15.97/2.49  fof(f45,plain,(
% 15.97/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 15.97/2.49    inference(definition_unfolding,[],[f35,f28,f29])).
% 15.97/2.49  
% 15.97/2.49  fof(f1,axiom,(
% 15.97/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.97/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.49  
% 15.97/2.49  fof(f27,plain,(
% 15.97/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.97/2.49    inference(cnf_transformation,[],[f1])).
% 15.97/2.49  
% 15.97/2.49  fof(f43,plain,(
% 15.97/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 15.97/2.49    inference(definition_unfolding,[],[f27,f28,f28])).
% 15.97/2.49  
% 15.97/2.49  fof(f7,axiom,(
% 15.97/2.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 15.97/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.49  
% 15.97/2.49  fof(f16,plain,(
% 15.97/2.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.97/2.49    inference(ennf_transformation,[],[f7])).
% 15.97/2.49  
% 15.97/2.49  fof(f33,plain,(
% 15.97/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.97/2.49    inference(cnf_transformation,[],[f16])).
% 15.97/2.49  
% 15.97/2.49  fof(f6,axiom,(
% 15.97/2.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 15.97/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.49  
% 15.97/2.49  fof(f15,plain,(
% 15.97/2.49    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.97/2.49    inference(ennf_transformation,[],[f6])).
% 15.97/2.49  
% 15.97/2.49  fof(f32,plain,(
% 15.97/2.49    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.97/2.49    inference(cnf_transformation,[],[f15])).
% 15.97/2.49  
% 15.97/2.49  fof(f40,plain,(
% 15.97/2.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.97/2.49    inference(cnf_transformation,[],[f26])).
% 15.97/2.49  
% 15.97/2.49  fof(f10,axiom,(
% 15.97/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.97/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.49  
% 15.97/2.49  fof(f14,plain,(
% 15.97/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 15.97/2.49    inference(unused_predicate_definition_removal,[],[f10])).
% 15.97/2.49  
% 15.97/2.49  fof(f18,plain,(
% 15.97/2.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 15.97/2.49    inference(ennf_transformation,[],[f14])).
% 15.97/2.49  
% 15.97/2.49  fof(f36,plain,(
% 15.97/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.97/2.49    inference(cnf_transformation,[],[f18])).
% 15.97/2.49  
% 15.97/2.49  fof(f11,axiom,(
% 15.97/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 15.97/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.97/2.49  
% 15.97/2.49  fof(f19,plain,(
% 15.97/2.49    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.97/2.49    inference(ennf_transformation,[],[f11])).
% 15.97/2.49  
% 15.97/2.49  fof(f20,plain,(
% 15.97/2.49    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.97/2.49    inference(flattening,[],[f19])).
% 15.97/2.49  
% 15.97/2.49  fof(f37,plain,(
% 15.97/2.49    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.97/2.49    inference(cnf_transformation,[],[f20])).
% 15.97/2.49  
% 15.97/2.49  fof(f38,plain,(
% 15.97/2.49    l1_pre_topc(sK0)),
% 15.97/2.49    inference(cnf_transformation,[],[f26])).
% 15.97/2.49  
% 15.97/2.49  fof(f42,plain,(
% 15.97/2.49    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 15.97/2.49    inference(cnf_transformation,[],[f26])).
% 15.97/2.49  
% 15.97/2.49  fof(f41,plain,(
% 15.97/2.49    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 15.97/2.49    inference(cnf_transformation,[],[f26])).
% 15.97/2.49  
% 15.97/2.49  cnf(c_12,negated_conjecture,
% 15.97/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.97/2.49      inference(cnf_transformation,[],[f39]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_423,plain,
% 15.97/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.97/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_2,plain,
% 15.97/2.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 15.97/2.49      inference(cnf_transformation,[],[f31]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_430,plain,
% 15.97/2.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 15.97/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_1,plain,
% 15.97/2.49      ( k2_subset_1(X0) = X0 ),
% 15.97/2.49      inference(cnf_transformation,[],[f30]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_431,plain,
% 15.97/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.97/2.49      inference(light_normalisation,[status(thm)],[c_430,c_1]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_5,plain,
% 15.97/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.97/2.49      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 15.97/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_427,plain,
% 15.97/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 15.97/2.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 15.97/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_6,plain,
% 15.97/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 15.97/2.49      inference(cnf_transformation,[],[f45]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_432,plain,
% 15.97/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 15.97/2.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 15.97/2.49      inference(demodulation,[status(thm)],[c_427,c_6]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_1113,plain,
% 15.97/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_431,c_432]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_0,plain,
% 15.97/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 15.97/2.49      inference(cnf_transformation,[],[f43]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_801,plain,
% 15.97/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_1199,plain,
% 15.97/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_801,c_6]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_2357,plain,
% 15.97/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X0,X1,X0) ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_1113,c_1199]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_11826,plain,
% 15.97/2.49      ( k9_subset_1(X0,X1,X0) = k9_subset_1(X2,X0,X1)
% 15.97/2.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 15.97/2.49      inference(demodulation,[status(thm)],[c_2357,c_432]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_41500,plain,
% 15.97/2.49      ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(X0,sK1,X0) ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_423,c_11826]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_4,plain,
% 15.97/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.97/2.49      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 15.97/2.49      inference(cnf_transformation,[],[f33]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_428,plain,
% 15.97/2.49      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 15.97/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 15.97/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_1680,plain,
% 15.97/2.49      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_431,c_428]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_3,plain,
% 15.97/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.97/2.49      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 15.97/2.49      inference(cnf_transformation,[],[f32]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_429,plain,
% 15.97/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.97/2.49      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 15.97/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_6838,plain,
% 15.97/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
% 15.97/2.49      | m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_1680,c_429]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_29252,plain,
% 15.97/2.49      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 15.97/2.49      inference(global_propositional_subsumption,
% 15.97/2.49                [status(thm)],
% 15.97/2.49                [c_6838,c_431]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_29262,plain,
% 15.97/2.49      ( m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_0,c_29252]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_2353,plain,
% 15.97/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X0,X1,X0) ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_1113,c_801]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_29333,plain,
% 15.97/2.49      ( m1_subset_1(k9_subset_1(X0,X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 15.97/2.49      inference(light_normalisation,[status(thm)],[c_29262,c_2353]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_42049,plain,
% 15.97/2.49      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_41500,c_29333]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_1112,plain,
% 15.97/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,sK1)) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_423,c_432]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_2341,plain,
% 15.97/2.49      ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(sK1,X0,sK1) ),
% 15.97/2.49      inference(demodulation,[status(thm)],[c_1113,c_1112]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_42114,plain,
% 15.97/2.49      ( m1_subset_1(k9_subset_1(sK1,X0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
% 15.97/2.49      inference(light_normalisation,[status(thm)],[c_42049,c_2341]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_11,negated_conjecture,
% 15.97/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.97/2.49      inference(cnf_transformation,[],[f40]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_424,plain,
% 15.97/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.97/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_1678,plain,
% 15.97/2.49      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_424,c_428]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_1852,plain,
% 15.97/2.49      ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.97/2.49      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_1678,c_429]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_16,plain,
% 15.97/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.97/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_2209,plain,
% 15.97/2.49      ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.97/2.49      inference(global_propositional_subsumption,
% 15.97/2.49                [status(thm)],
% 15.97/2.49                [c_1852,c_16]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_2218,plain,
% 15.97/2.49      ( m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_0,c_2209]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_2232,plain,
% 15.97/2.49      ( m1_subset_1(k1_setfam_1(k1_enumset1(X0,X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.97/2.49      inference(demodulation,[status(thm)],[c_2218,c_6]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_2474,plain,
% 15.97/2.49      ( m1_subset_1(k9_subset_1(X0,sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.97/2.49      inference(demodulation,[status(thm)],[c_2232,c_2357]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_7,plain,
% 15.97/2.49      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.97/2.49      inference(cnf_transformation,[],[f36]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_8,plain,
% 15.97/2.49      ( ~ v2_tex_2(X0,X1)
% 15.97/2.49      | v2_tex_2(X2,X1)
% 15.97/2.49      | ~ r1_tarski(X2,X0)
% 15.97/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.97/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.97/2.49      | ~ l1_pre_topc(X1) ),
% 15.97/2.49      inference(cnf_transformation,[],[f37]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_13,negated_conjecture,
% 15.97/2.49      ( l1_pre_topc(sK0) ),
% 15.97/2.49      inference(cnf_transformation,[],[f38]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_131,plain,
% 15.97/2.49      ( ~ v2_tex_2(X0,X1)
% 15.97/2.49      | v2_tex_2(X2,X1)
% 15.97/2.49      | ~ r1_tarski(X2,X0)
% 15.97/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.97/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.97/2.49      | sK0 != X1 ),
% 15.97/2.49      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_132,plain,
% 15.97/2.49      ( ~ v2_tex_2(X0,sK0)
% 15.97/2.49      | v2_tex_2(X1,sK0)
% 15.97/2.49      | ~ r1_tarski(X1,X0)
% 15.97/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.97/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.97/2.49      inference(unflattening,[status(thm)],[c_131]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_156,plain,
% 15.97/2.49      ( ~ v2_tex_2(X0,sK0)
% 15.97/2.49      | v2_tex_2(X1,sK0)
% 15.97/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 15.97/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.97/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.97/2.49      | X1 != X2
% 15.97/2.49      | X0 != X3 ),
% 15.97/2.49      inference(resolution_lifted,[status(thm)],[c_7,c_132]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_157,plain,
% 15.97/2.49      ( ~ v2_tex_2(X0,sK0)
% 15.97/2.49      | v2_tex_2(X1,sK0)
% 15.97/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 15.97/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.97/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.97/2.49      inference(unflattening,[status(thm)],[c_156]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_422,plain,
% 15.97/2.49      ( v2_tex_2(X0,sK0) != iProver_top
% 15.97/2.49      | v2_tex_2(X1,sK0) = iProver_top
% 15.97/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.97/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.97/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.97/2.49      inference(predicate_to_equality,[status(thm)],[c_157]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_600,plain,
% 15.97/2.49      ( v2_tex_2(X0,sK0) = iProver_top
% 15.97/2.49      | v2_tex_2(sK1,sK0) != iProver_top
% 15.97/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.97/2.49      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_423,c_422]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_2482,plain,
% 15.97/2.49      ( v2_tex_2(k9_subset_1(X0,sK2,X0),sK0) = iProver_top
% 15.97/2.49      | v2_tex_2(sK1,sK0) != iProver_top
% 15.97/2.49      | m1_subset_1(k9_subset_1(X0,sK2,X0),k1_zfmisc_1(sK1)) != iProver_top ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_2474,c_600]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_42354,plain,
% 15.97/2.49      ( v2_tex_2(k9_subset_1(sK1,sK2,sK1),sK0) = iProver_top
% 15.97/2.49      | v2_tex_2(sK1,sK0) != iProver_top ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_42114,c_2482]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_599,plain,
% 15.97/2.49      ( v2_tex_2(X0,sK0) = iProver_top
% 15.97/2.49      | v2_tex_2(sK2,sK0) != iProver_top
% 15.97/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.97/2.49      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_424,c_422]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_2483,plain,
% 15.97/2.49      ( v2_tex_2(k9_subset_1(X0,sK2,X0),sK0) = iProver_top
% 15.97/2.49      | v2_tex_2(sK2,sK0) != iProver_top
% 15.97/2.49      | m1_subset_1(k9_subset_1(X0,sK2,X0),k1_zfmisc_1(sK2)) != iProver_top ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_2474,c_599]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_29574,plain,
% 15.97/2.49      ( v2_tex_2(k9_subset_1(X0,sK2,X0),sK0) = iProver_top
% 15.97/2.49      | v2_tex_2(sK2,sK0) != iProver_top ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_29333,c_2483]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_7079,plain,
% 15.97/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_2353,c_0]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_9118,plain,
% 15.97/2.49      ( k9_subset_1(X0,X1,X0) = k9_subset_1(X1,X0,X1) ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_7079,c_2353]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_1111,plain,
% 15.97/2.49      ( k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_424,c_432]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_9,negated_conjecture,
% 15.97/2.49      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 15.97/2.49      inference(cnf_transformation,[],[f42]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_426,plain,
% 15.97/2.49      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 15.97/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_1343,plain,
% 15.97/2.49      ( v2_tex_2(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK0) != iProver_top ),
% 15.97/2.49      inference(demodulation,[status(thm)],[c_1111,c_426]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_2339,plain,
% 15.97/2.49      ( v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
% 15.97/2.49      inference(demodulation,[status(thm)],[c_1113,c_1343]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_10002,plain,
% 15.97/2.49      ( v2_tex_2(k9_subset_1(sK1,sK2,sK1),sK0) != iProver_top ),
% 15.97/2.49      inference(demodulation,[status(thm)],[c_9118,c_2339]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_31501,plain,
% 15.97/2.49      ( v2_tex_2(sK2,sK0) != iProver_top ),
% 15.97/2.49      inference(superposition,[status(thm)],[c_29574,c_10002]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_10,negated_conjecture,
% 15.97/2.49      ( v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0) ),
% 15.97/2.49      inference(cnf_transformation,[],[f41]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(c_17,plain,
% 15.97/2.49      ( v2_tex_2(sK2,sK0) = iProver_top
% 15.97/2.49      | v2_tex_2(sK1,sK0) = iProver_top ),
% 15.97/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.97/2.49  
% 15.97/2.49  cnf(contradiction,plain,
% 15.97/2.49      ( $false ),
% 15.97/2.49      inference(minisat,[status(thm)],[c_42354,c_31501,c_10002,c_17]) ).
% 15.97/2.49  
% 15.97/2.49  
% 15.97/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.97/2.49  
% 15.97/2.49  ------                               Statistics
% 15.97/2.49  
% 15.97/2.49  ------ General
% 15.97/2.49  
% 15.97/2.49  abstr_ref_over_cycles:                  0
% 15.97/2.49  abstr_ref_under_cycles:                 0
% 15.97/2.49  gc_basic_clause_elim:                   0
% 15.97/2.49  forced_gc_time:                         0
% 15.97/2.49  parsing_time:                           0.008
% 15.97/2.49  unif_index_cands_time:                  0.
% 15.97/2.49  unif_index_add_time:                    0.
% 15.97/2.49  orderings_time:                         0.
% 15.97/2.49  out_proof_time:                         0.132
% 15.97/2.49  total_time:                             1.879
% 15.97/2.49  num_of_symbols:                         46
% 15.97/2.49  num_of_terms:                           95522
% 15.97/2.49  
% 15.97/2.49  ------ Preprocessing
% 15.97/2.49  
% 15.97/2.49  num_of_splits:                          0
% 15.97/2.49  num_of_split_atoms:                     0
% 15.97/2.49  num_of_reused_defs:                     0
% 15.97/2.49  num_eq_ax_congr_red:                    26
% 15.97/2.49  num_of_sem_filtered_clauses:            1
% 15.97/2.49  num_of_subtypes:                        0
% 15.97/2.49  monotx_restored_types:                  0
% 15.97/2.49  sat_num_of_epr_types:                   0
% 15.97/2.49  sat_num_of_non_cyclic_types:            0
% 15.97/2.49  sat_guarded_non_collapsed_types:        0
% 15.97/2.49  num_pure_diseq_elim:                    0
% 15.97/2.49  simp_replaced_by:                       0
% 15.97/2.49  res_preprocessed:                       69
% 15.97/2.49  prep_upred:                             0
% 15.97/2.49  prep_unflattend:                        3
% 15.97/2.49  smt_new_axioms:                         0
% 15.97/2.49  pred_elim_cands:                        2
% 15.97/2.49  pred_elim:                              2
% 15.97/2.49  pred_elim_cl:                           2
% 15.97/2.49  pred_elim_cycles:                       4
% 15.97/2.49  merged_defs:                            0
% 15.97/2.49  merged_defs_ncl:                        0
% 15.97/2.49  bin_hyper_res:                          0
% 15.97/2.49  prep_cycles:                            4
% 15.97/2.49  pred_elim_time:                         0.002
% 15.97/2.49  splitting_time:                         0.
% 15.97/2.49  sem_filter_time:                        0.
% 15.97/2.49  monotx_time:                            0.
% 15.97/2.49  subtype_inf_time:                       0.
% 15.97/2.49  
% 15.97/2.49  ------ Problem properties
% 15.97/2.49  
% 15.97/2.49  clauses:                                12
% 15.97/2.49  conjectures:                            4
% 15.97/2.49  epr:                                    1
% 15.97/2.49  horn:                                   11
% 15.97/2.49  ground:                                 4
% 15.97/2.49  unary:                                  7
% 15.97/2.49  binary:                                 4
% 15.97/2.49  lits:                                   20
% 15.97/2.49  lits_eq:                                5
% 15.97/2.49  fd_pure:                                0
% 15.97/2.49  fd_pseudo:                              0
% 15.97/2.49  fd_cond:                                0
% 15.97/2.49  fd_pseudo_cond:                         0
% 15.97/2.49  ac_symbols:                             0
% 15.97/2.49  
% 15.97/2.49  ------ Propositional Solver
% 15.97/2.49  
% 15.97/2.49  prop_solver_calls:                      35
% 15.97/2.49  prop_fast_solver_calls:                 792
% 15.97/2.49  smt_solver_calls:                       0
% 15.97/2.49  smt_fast_solver_calls:                  0
% 15.97/2.49  prop_num_of_clauses:                    18081
% 15.97/2.49  prop_preprocess_simplified:             15466
% 15.97/2.49  prop_fo_subsumed:                       30
% 15.97/2.49  prop_solver_time:                       0.
% 15.97/2.49  smt_solver_time:                        0.
% 15.97/2.49  smt_fast_solver_time:                   0.
% 15.97/2.49  prop_fast_solver_time:                  0.
% 15.97/2.49  prop_unsat_core_time:                   0.001
% 15.97/2.49  
% 15.97/2.49  ------ QBF
% 15.97/2.49  
% 15.97/2.49  qbf_q_res:                              0
% 15.97/2.49  qbf_num_tautologies:                    0
% 15.97/2.49  qbf_prep_cycles:                        0
% 15.97/2.49  
% 15.97/2.49  ------ BMC1
% 15.97/2.49  
% 15.97/2.49  bmc1_current_bound:                     -1
% 15.97/2.49  bmc1_last_solved_bound:                 -1
% 15.97/2.49  bmc1_unsat_core_size:                   -1
% 15.97/2.49  bmc1_unsat_core_parents_size:           -1
% 15.97/2.49  bmc1_merge_next_fun:                    0
% 15.97/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.97/2.49  
% 15.97/2.49  ------ Instantiation
% 15.97/2.49  
% 15.97/2.49  inst_num_of_clauses:                    2780
% 15.97/2.49  inst_num_in_passive:                    612
% 15.97/2.49  inst_num_in_active:                     1180
% 15.97/2.49  inst_num_in_unprocessed:                988
% 15.97/2.49  inst_num_of_loops:                      1240
% 15.97/2.49  inst_num_of_learning_restarts:          0
% 15.97/2.49  inst_num_moves_active_passive:          54
% 15.97/2.49  inst_lit_activity:                      0
% 15.97/2.49  inst_lit_activity_moves:                0
% 15.97/2.49  inst_num_tautologies:                   0
% 15.97/2.49  inst_num_prop_implied:                  0
% 15.97/2.49  inst_num_existing_simplified:           0
% 15.97/2.49  inst_num_eq_res_simplified:             0
% 15.97/2.49  inst_num_child_elim:                    0
% 15.97/2.49  inst_num_of_dismatching_blockings:      1225
% 15.97/2.49  inst_num_of_non_proper_insts:           3189
% 15.97/2.49  inst_num_of_duplicates:                 0
% 15.97/2.49  inst_inst_num_from_inst_to_res:         0
% 15.97/2.49  inst_dismatching_checking_time:         0.
% 15.97/2.49  
% 15.97/2.49  ------ Resolution
% 15.97/2.49  
% 15.97/2.49  res_num_of_clauses:                     0
% 15.97/2.49  res_num_in_passive:                     0
% 15.97/2.49  res_num_in_active:                      0
% 15.97/2.49  res_num_of_loops:                       73
% 15.97/2.49  res_forward_subset_subsumed:            494
% 15.97/2.49  res_backward_subset_subsumed:           0
% 15.97/2.49  res_forward_subsumed:                   0
% 15.97/2.49  res_backward_subsumed:                  0
% 15.97/2.49  res_forward_subsumption_resolution:     0
% 15.97/2.49  res_backward_subsumption_resolution:    0
% 15.97/2.49  res_clause_to_clause_subsumption:       32072
% 15.97/2.49  res_orphan_elimination:                 0
% 15.97/2.49  res_tautology_del:                      333
% 15.97/2.49  res_num_eq_res_simplified:              0
% 15.97/2.49  res_num_sel_changes:                    0
% 15.97/2.49  res_moves_from_active_to_pass:          0
% 15.97/2.49  
% 15.97/2.49  ------ Superposition
% 15.97/2.49  
% 15.97/2.49  sup_time_total:                         0.
% 15.97/2.49  sup_time_generating:                    0.
% 15.97/2.49  sup_time_sim_full:                      0.
% 15.97/2.49  sup_time_sim_immed:                     0.
% 15.97/2.49  
% 15.97/2.49  sup_num_of_clauses:                     4543
% 15.97/2.49  sup_num_in_active:                      182
% 15.97/2.49  sup_num_in_passive:                     4361
% 15.97/2.49  sup_num_of_loops:                       247
% 15.97/2.49  sup_fw_superposition:                   8376
% 15.97/2.49  sup_bw_superposition:                   4005
% 15.97/2.49  sup_immediate_simplified:               6947
% 15.97/2.49  sup_given_eliminated:                   3
% 15.97/2.49  comparisons_done:                       0
% 15.97/2.49  comparisons_avoided:                    0
% 15.97/2.49  
% 15.97/2.49  ------ Simplifications
% 15.97/2.49  
% 15.97/2.49  
% 15.97/2.49  sim_fw_subset_subsumed:                 35
% 15.97/2.49  sim_bw_subset_subsumed:                 43
% 15.97/2.49  sim_fw_subsumed:                        419
% 15.97/2.49  sim_bw_subsumed:                        317
% 15.97/2.49  sim_fw_subsumption_res:                 0
% 15.97/2.49  sim_bw_subsumption_res:                 0
% 15.97/2.49  sim_tautology_del:                      11
% 15.97/2.49  sim_eq_tautology_del:                   502
% 15.97/2.49  sim_eq_res_simp:                        0
% 15.97/2.49  sim_fw_demodulated:                     6788
% 15.97/2.49  sim_bw_demodulated:                     256
% 15.97/2.49  sim_light_normalised:                   1721
% 15.97/2.49  sim_joinable_taut:                      0
% 15.97/2.49  sim_joinable_simp:                      0
% 15.97/2.49  sim_ac_normalised:                      0
% 15.97/2.49  sim_smt_subsumption:                    0
% 15.97/2.49  
%------------------------------------------------------------------------------
