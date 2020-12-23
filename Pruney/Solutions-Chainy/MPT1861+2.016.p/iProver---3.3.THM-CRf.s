%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:50 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 372 expanded)
%              Number of clauses        :   89 ( 150 expanded)
%              Number of leaves         :   18 (  99 expanded)
%              Depth                    :   24
%              Number of atoms          :  335 (1458 expanded)
%              Number of equality atoms :   63 (  94 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f26,f27])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f37,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f26,f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_145,plain,
    ( k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)) = k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_155,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(X2_41,X1_41)
    | X2_41 != X0_41 ),
    theory(equality)).

cnf(c_4314,plain,
    ( ~ r1_tarski(k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)),X2_41)
    | r1_tarski(k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)),X2_41) ),
    inference(resolution,[status(thm)],[c_145,c_155])).

cnf(c_7,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_142,plain,
    ( ~ v2_tex_2(X0_41,X0_42)
    | v2_tex_2(X1_41,X0_42)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ r1_tarski(X1_41,X0_41)
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_139,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_6985,plain,
    ( v2_tex_2(X0_41,sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_41,sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_142,c_139])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7362,plain,
    ( ~ r1_tarski(X0_41,sK2)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK2,sK0)
    | v2_tex_2(X0_41,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6985,c_12])).

cnf(c_7363,plain,
    ( v2_tex_2(X0_41,sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_41,sK2) ),
    inference(renaming,[status(thm)],[c_7362])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_144,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(X1_41))
    | ~ r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_7773,plain,
    ( v2_tex_2(X0_41,sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ r1_tarski(X0_41,u1_struct_0(sK0))
    | ~ r1_tarski(X0_41,sK2) ),
    inference(resolution,[status(thm)],[c_7363,c_144])).

cnf(c_13865,plain,
    ( v2_tex_2(k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)),sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ r1_tarski(k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)),u1_struct_0(sK0))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)),sK2) ),
    inference(resolution,[status(thm)],[c_4314,c_7773])).

cnf(c_473,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_139])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_143,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X1_41))
    | r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_469,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(X1_41)) != iProver_top
    | r1_tarski(X0_41,X1_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_1036,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_473,c_469])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_74,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_75,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_74])).

cnf(c_97,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_75])).

cnf(c_136,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | k4_xboole_0(X2_41,k4_xboole_0(X2_41,X0_41)) = k9_subset_1(X1_41,X2_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_97])).

cnf(c_476,plain,
    ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = k9_subset_1(X2_41,X0_41,X1_41)
    | r1_tarski(X1_41,X2_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_136])).

cnf(c_1334,plain,
    ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)) = k9_subset_1(u1_struct_0(sK0),X0_41,sK2) ),
    inference(superposition,[status(thm)],[c_1036,c_476])).

cnf(c_8,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_141,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_471,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_141])).

cnf(c_1367,plain,
    ( v2_tex_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1334,c_471])).

cnf(c_1368,plain,
    ( ~ v2_tex_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1367])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_148,plain,
    ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = k4_xboole_0(X1_41,k4_xboole_0(X1_41,X0_41)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_160,plain,
    ( ~ v2_tex_2(X0_41,X0_42)
    | v2_tex_2(X1_41,X0_42)
    | X1_41 != X0_41 ),
    theory(equality)).

cnf(c_3787,plain,
    ( ~ v2_tex_2(k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)),X0_42)
    | v2_tex_2(k4_xboole_0(X1_41,k4_xboole_0(X1_41,X0_41)),X0_42) ),
    inference(resolution,[status(thm)],[c_148,c_160])).

cnf(c_154,plain,
    ( X0_41 != X1_41
    | k4_xboole_0(X2_41,X0_41) = k4_xboole_0(X2_41,X1_41) ),
    theory(equality)).

cnf(c_1819,plain,
    ( ~ v2_tex_2(k4_xboole_0(X0_41,X1_41),X0_42)
    | v2_tex_2(k4_xboole_0(X0_41,X2_41),X0_42)
    | X2_41 != X1_41 ),
    inference(resolution,[status(thm)],[c_154,c_160])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_147,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k4_xboole_0(X0_41,X2_41),X1_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_8609,plain,
    ( v2_tex_2(k4_xboole_0(X0_41,X1_41),sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ r1_tarski(X0_41,u1_struct_0(sK0))
    | ~ r1_tarski(k4_xboole_0(X0_41,X1_41),sK2) ),
    inference(resolution,[status(thm)],[c_7773,c_147])).

cnf(c_10060,plain,
    ( v2_tex_2(k4_xboole_0(X0_41,X1_41),sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ r1_tarski(X0_41,u1_struct_0(sK0))
    | ~ r1_tarski(k4_xboole_0(X0_41,X2_41),sK2)
    | X1_41 != X2_41 ),
    inference(resolution,[status(thm)],[c_1819,c_8609])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_146,plain,
    ( r1_tarski(k4_xboole_0(X0_41,X1_41),X0_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_10977,plain,
    ( v2_tex_2(k4_xboole_0(sK2,X0_41),sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | X0_41 != X1_41 ),
    inference(resolution,[status(thm)],[c_10060,c_146])).

cnf(c_560,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_650,plain,
    ( r1_tarski(k4_xboole_0(sK2,X0_41),u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_615,plain,
    ( ~ v2_tex_2(X0_41,X0_42)
    | v2_tex_2(k4_xboole_0(X0_41,X1_41),X0_42)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ m1_subset_1(k4_xboole_0(X0_41,X1_41),k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ r1_tarski(k4_xboole_0(X0_41,X1_41),X0_41)
    | ~ l1_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_734,plain,
    ( v2_tex_2(k4_xboole_0(sK2,X0_41),sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(k4_xboole_0(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK2,X0_41),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_781,plain,
    ( r1_tarski(k4_xboole_0(sK2,X0_41),sK2) ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_793,plain,
    ( m1_subset_1(k4_xboole_0(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK2,X0_41),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_11523,plain,
    ( v2_tex_2(k4_xboole_0(sK2,X0_41),sK0)
    | ~ v2_tex_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10977,c_12,c_10,c_560,c_650,c_734,c_781,c_793])).

cnf(c_13843,plain,
    ( v2_tex_2(k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)),sK0)
    | ~ v2_tex_2(sK2,sK0) ),
    inference(resolution,[status(thm)],[c_3787,c_11523])).

cnf(c_13845,plain,
    ( v2_tex_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | ~ v2_tex_2(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_13843])).

cnf(c_14160,plain,
    ( ~ v2_tex_2(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13865,c_1368,c_13845])).

cnf(c_9,negated_conjecture,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_140,negated_conjecture,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_14171,plain,
    ( v2_tex_2(sK1,sK0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_14160,c_140])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_138,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_6988,plain,
    ( v2_tex_2(X0_41,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_41,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_142,c_138])).

cnf(c_8569,plain,
    ( ~ r1_tarski(X0_41,sK1)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_tex_2(X0_41,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6988,c_12])).

cnf(c_8570,plain,
    ( v2_tex_2(X0_41,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_41,sK1) ),
    inference(renaming,[status(thm)],[c_8569])).

cnf(c_14177,plain,
    ( v2_tex_2(X0_41,sK0)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_41,sK1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_14171,c_8570])).

cnf(c_15213,plain,
    ( v2_tex_2(X0_41,sK0)
    | ~ r1_tarski(X0_41,u1_struct_0(sK0))
    | ~ r1_tarski(X0_41,sK1) ),
    inference(resolution,[status(thm)],[c_14177,c_144])).

cnf(c_153,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_150,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_2038,plain,
    ( X0_41 != X1_41
    | X1_41 = X0_41 ),
    inference(resolution,[status(thm)],[c_153,c_150])).

cnf(c_3770,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | k9_subset_1(X1_41,X2_41,X0_41) = k4_xboole_0(X2_41,k4_xboole_0(X2_41,X0_41)) ),
    inference(resolution,[status(thm)],[c_2038,c_136])).

cnf(c_4899,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k9_subset_1(X1_41,X2_41,X0_41),X3_41)
    | ~ r1_tarski(k4_xboole_0(X2_41,k4_xboole_0(X2_41,X0_41)),X3_41) ),
    inference(resolution,[status(thm)],[c_3770,c_155])).

cnf(c_6582,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(X2_41,X3_41)
    | r1_tarski(k9_subset_1(X1_41,X2_41,X0_41),X3_41) ),
    inference(resolution,[status(thm)],[c_4899,c_147])).

cnf(c_16870,plain,
    ( v2_tex_2(k9_subset_1(X0_41,X1_41,X2_41),sK0)
    | ~ r1_tarski(X2_41,X0_41)
    | ~ r1_tarski(X1_41,u1_struct_0(sK0))
    | ~ r1_tarski(k9_subset_1(X0_41,X1_41,X2_41),sK1) ),
    inference(resolution,[status(thm)],[c_15213,c_6582])).

cnf(c_17241,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_16870,c_141])).

cnf(c_11120,plain,
    ( r1_tarski(k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)),X0_41) ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_11122,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_11120])).

cnf(c_644,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(k4_xboole_0(X1_41,X2_41),X1_41)
    | X0_41 != k4_xboole_0(X1_41,X2_41) ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_3254,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),X0_41)
    | ~ r1_tarski(k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)),X0_41)
    | k9_subset_1(u1_struct_0(sK0),X0_41,sK2) != k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)) ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_3256,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3254])).

cnf(c_2248,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_41,sK2) = k9_subset_1(u1_struct_0(sK0),X0_41,sK2) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_2250,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2248])).

cnf(c_962,plain,
    ( X0_41 != X1_41
    | X0_41 = k4_xboole_0(X2_41,X3_41)
    | k4_xboole_0(X2_41,X3_41) != X1_41 ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_1680,plain,
    ( X0_41 != k9_subset_1(u1_struct_0(sK0),X1_41,sK2)
    | X0_41 = k4_xboole_0(X1_41,k4_xboole_0(X1_41,sK2))
    | k4_xboole_0(X1_41,k4_xboole_0(X1_41,sK2)) != k9_subset_1(u1_struct_0(sK0),X1_41,sK2) ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_2247,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_41,sK2) != k9_subset_1(u1_struct_0(sK0),X0_41,sK2)
    | k9_subset_1(u1_struct_0(sK0),X0_41,sK2) = k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2))
    | k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)) != k9_subset_1(u1_struct_0(sK0),X0_41,sK2) ),
    inference(instantiation,[status(thm)],[c_1680])).

cnf(c_2249,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2247])).

cnf(c_651,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)) = k9_subset_1(u1_struct_0(sK0),X0_41,sK2) ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_654,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_563,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17241,c_11122,c_3256,c_2250,c_2249,c_654,c_563,c_560,c_10,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:29:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.82/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/1.50  
% 7.82/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.82/1.50  
% 7.82/1.50  ------  iProver source info
% 7.82/1.50  
% 7.82/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.82/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.82/1.50  git: non_committed_changes: false
% 7.82/1.50  git: last_make_outside_of_git: false
% 7.82/1.50  
% 7.82/1.50  ------ 
% 7.82/1.50  ------ Parsing...
% 7.82/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.82/1.50  
% 7.82/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.82/1.50  
% 7.82/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.82/1.50  
% 7.82/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.50  ------ Proving...
% 7.82/1.50  ------ Problem Properties 
% 7.82/1.50  
% 7.82/1.50  
% 7.82/1.50  clauses                                 13
% 7.82/1.50  conjectures                             5
% 7.82/1.50  EPR                                     2
% 7.82/1.50  Horn                                    12
% 7.82/1.50  unary                                   7
% 7.82/1.50  binary                                  5
% 7.82/1.50  lits                                    23
% 7.82/1.50  lits eq                                 3
% 7.82/1.50  fd_pure                                 0
% 7.82/1.50  fd_pseudo                               0
% 7.82/1.50  fd_cond                                 0
% 7.82/1.50  fd_pseudo_cond                          0
% 7.82/1.50  AC symbols                              0
% 7.82/1.50  
% 7.82/1.50  ------ Input Options Time Limit: Unbounded
% 7.82/1.50  
% 7.82/1.50  
% 7.82/1.50  ------ 
% 7.82/1.50  Current options:
% 7.82/1.50  ------ 
% 7.82/1.50  
% 7.82/1.50  
% 7.82/1.50  
% 7.82/1.50  
% 7.82/1.50  ------ Proving...
% 7.82/1.50  
% 7.82/1.50  
% 7.82/1.50  % SZS status Theorem for theBenchmark.p
% 7.82/1.50  
% 7.82/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.82/1.50  
% 7.82/1.50  fof(f7,axiom,(
% 7.82/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.82/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f29,plain,(
% 7.82/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.82/1.50    inference(cnf_transformation,[],[f7])).
% 7.82/1.50  
% 7.82/1.50  fof(f4,axiom,(
% 7.82/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.82/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f26,plain,(
% 7.82/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.82/1.50    inference(cnf_transformation,[],[f4])).
% 7.82/1.50  
% 7.82/1.50  fof(f5,axiom,(
% 7.82/1.50    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 7.82/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f27,plain,(
% 7.82/1.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f5])).
% 7.82/1.50  
% 7.82/1.50  fof(f40,plain,(
% 7.82/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 7.82/1.50    inference(definition_unfolding,[],[f29,f26,f27])).
% 7.82/1.50  
% 7.82/1.50  fof(f9,axiom,(
% 7.82/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 7.82/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f14,plain,(
% 7.82/1.50    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.82/1.50    inference(ennf_transformation,[],[f9])).
% 7.82/1.50  
% 7.82/1.50  fof(f15,plain,(
% 7.82/1.50    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.82/1.50    inference(flattening,[],[f14])).
% 7.82/1.50  
% 7.82/1.50  fof(f32,plain,(
% 7.82/1.50    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f15])).
% 7.82/1.50  
% 7.82/1.50  fof(f10,conjecture,(
% 7.82/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.82/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f11,negated_conjecture,(
% 7.82/1.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.82/1.50    inference(negated_conjecture,[],[f10])).
% 7.82/1.50  
% 7.82/1.50  fof(f16,plain,(
% 7.82/1.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.82/1.50    inference(ennf_transformation,[],[f11])).
% 7.82/1.50  
% 7.82/1.50  fof(f17,plain,(
% 7.82/1.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.82/1.50    inference(flattening,[],[f16])).
% 7.82/1.50  
% 7.82/1.50  fof(f21,plain,(
% 7.82/1.50    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & (v2_tex_2(sK2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.82/1.50    introduced(choice_axiom,[])).
% 7.82/1.50  
% 7.82/1.50  fof(f20,plain,(
% 7.82/1.50    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.82/1.50    introduced(choice_axiom,[])).
% 7.82/1.50  
% 7.82/1.50  fof(f19,plain,(
% 7.82/1.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 7.82/1.50    introduced(choice_axiom,[])).
% 7.82/1.50  
% 7.82/1.50  fof(f22,plain,(
% 7.82/1.50    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 7.82/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21,f20,f19])).
% 7.82/1.50  
% 7.82/1.50  fof(f35,plain,(
% 7.82/1.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.82/1.50    inference(cnf_transformation,[],[f22])).
% 7.82/1.50  
% 7.82/1.50  fof(f33,plain,(
% 7.82/1.50    l1_pre_topc(sK0)),
% 7.82/1.50    inference(cnf_transformation,[],[f22])).
% 7.82/1.50  
% 7.82/1.50  fof(f8,axiom,(
% 7.82/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.82/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f18,plain,(
% 7.82/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.82/1.50    inference(nnf_transformation,[],[f8])).
% 7.82/1.50  
% 7.82/1.50  fof(f31,plain,(
% 7.82/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f18])).
% 7.82/1.50  
% 7.82/1.50  fof(f30,plain,(
% 7.82/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.82/1.50    inference(cnf_transformation,[],[f18])).
% 7.82/1.50  
% 7.82/1.50  fof(f6,axiom,(
% 7.82/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.82/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f13,plain,(
% 7.82/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.82/1.50    inference(ennf_transformation,[],[f6])).
% 7.82/1.50  
% 7.82/1.50  fof(f28,plain,(
% 7.82/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.82/1.50    inference(cnf_transformation,[],[f13])).
% 7.82/1.50  
% 7.82/1.50  fof(f39,plain,(
% 7.82/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.82/1.50    inference(definition_unfolding,[],[f28,f26])).
% 7.82/1.50  
% 7.82/1.50  fof(f37,plain,(
% 7.82/1.50    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 7.82/1.50    inference(cnf_transformation,[],[f22])).
% 7.82/1.50  
% 7.82/1.50  fof(f1,axiom,(
% 7.82/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.82/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f23,plain,(
% 7.82/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f1])).
% 7.82/1.50  
% 7.82/1.50  fof(f38,plain,(
% 7.82/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.82/1.50    inference(definition_unfolding,[],[f23,f26,f26])).
% 7.82/1.50  
% 7.82/1.50  fof(f2,axiom,(
% 7.82/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 7.82/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f12,plain,(
% 7.82/1.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 7.82/1.50    inference(ennf_transformation,[],[f2])).
% 7.82/1.50  
% 7.82/1.50  fof(f24,plain,(
% 7.82/1.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f12])).
% 7.82/1.50  
% 7.82/1.50  fof(f3,axiom,(
% 7.82/1.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.82/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f25,plain,(
% 7.82/1.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f3])).
% 7.82/1.50  
% 7.82/1.50  fof(f36,plain,(
% 7.82/1.50    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 7.82/1.50    inference(cnf_transformation,[],[f22])).
% 7.82/1.50  
% 7.82/1.50  fof(f34,plain,(
% 7.82/1.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.82/1.50    inference(cnf_transformation,[],[f22])).
% 7.82/1.50  
% 7.82/1.50  cnf(c_4,plain,
% 7.82/1.50      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.82/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_145,plain,
% 7.82/1.50      ( k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)) = k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) ),
% 7.82/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_155,plain,
% 7.82/1.50      ( ~ r1_tarski(X0_41,X1_41)
% 7.82/1.50      | r1_tarski(X2_41,X1_41)
% 7.82/1.50      | X2_41 != X0_41 ),
% 7.82/1.50      theory(equality) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_4314,plain,
% 7.82/1.50      ( ~ r1_tarski(k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)),X2_41)
% 7.82/1.50      | r1_tarski(k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)),X2_41) ),
% 7.82/1.50      inference(resolution,[status(thm)],[c_145,c_155]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_7,plain,
% 7.82/1.50      ( ~ v2_tex_2(X0,X1)
% 7.82/1.50      | v2_tex_2(X2,X1)
% 7.82/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.82/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.82/1.50      | ~ r1_tarski(X2,X0)
% 7.82/1.50      | ~ l1_pre_topc(X1) ),
% 7.82/1.50      inference(cnf_transformation,[],[f32]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_142,plain,
% 7.82/1.50      ( ~ v2_tex_2(X0_41,X0_42)
% 7.82/1.50      | v2_tex_2(X1_41,X0_42)
% 7.82/1.50      | ~ m1_subset_1(X1_41,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.82/1.50      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.82/1.50      | ~ r1_tarski(X1_41,X0_41)
% 7.82/1.50      | ~ l1_pre_topc(X0_42) ),
% 7.82/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_10,negated_conjecture,
% 7.82/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.82/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_139,negated_conjecture,
% 7.82/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.82/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_6985,plain,
% 7.82/1.50      ( v2_tex_2(X0_41,sK0)
% 7.82/1.50      | ~ v2_tex_2(sK2,sK0)
% 7.82/1.50      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.82/1.50      | ~ r1_tarski(X0_41,sK2)
% 7.82/1.50      | ~ l1_pre_topc(sK0) ),
% 7.82/1.50      inference(resolution,[status(thm)],[c_142,c_139]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_12,negated_conjecture,
% 7.82/1.50      ( l1_pre_topc(sK0) ),
% 7.82/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_7362,plain,
% 7.82/1.50      ( ~ r1_tarski(X0_41,sK2)
% 7.82/1.50      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.82/1.50      | ~ v2_tex_2(sK2,sK0)
% 7.82/1.50      | v2_tex_2(X0_41,sK0) ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_6985,c_12]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_7363,plain,
% 7.82/1.50      ( v2_tex_2(X0_41,sK0)
% 7.82/1.50      | ~ v2_tex_2(sK2,sK0)
% 7.82/1.50      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.82/1.50      | ~ r1_tarski(X0_41,sK2) ),
% 7.82/1.50      inference(renaming,[status(thm)],[c_7362]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_5,plain,
% 7.82/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.82/1.50      inference(cnf_transformation,[],[f31]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_144,plain,
% 7.82/1.50      ( m1_subset_1(X0_41,k1_zfmisc_1(X1_41))
% 7.82/1.50      | ~ r1_tarski(X0_41,X1_41) ),
% 7.82/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_7773,plain,
% 7.82/1.50      ( v2_tex_2(X0_41,sK0)
% 7.82/1.50      | ~ v2_tex_2(sK2,sK0)
% 7.82/1.50      | ~ r1_tarski(X0_41,u1_struct_0(sK0))
% 7.82/1.50      | ~ r1_tarski(X0_41,sK2) ),
% 7.82/1.50      inference(resolution,[status(thm)],[c_7363,c_144]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_13865,plain,
% 7.82/1.50      ( v2_tex_2(k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)),sK0)
% 7.82/1.50      | ~ v2_tex_2(sK2,sK0)
% 7.82/1.50      | ~ r1_tarski(k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)),u1_struct_0(sK0))
% 7.82/1.50      | ~ r1_tarski(k1_setfam_1(k2_enumset1(X0_41,X0_41,X0_41,X1_41)),sK2) ),
% 7.82/1.50      inference(resolution,[status(thm)],[c_4314,c_7773]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_473,plain,
% 7.82/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_139]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_6,plain,
% 7.82/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.82/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_143,plain,
% 7.82/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X1_41))
% 7.82/1.50      | r1_tarski(X0_41,X1_41) ),
% 7.82/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_469,plain,
% 7.82/1.50      ( m1_subset_1(X0_41,k1_zfmisc_1(X1_41)) != iProver_top
% 7.82/1.50      | r1_tarski(X0_41,X1_41) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_143]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1036,plain,
% 7.82/1.50      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_473,c_469]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_3,plain,
% 7.82/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.82/1.50      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 7.82/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_74,plain,
% 7.82/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.82/1.50      inference(prop_impl,[status(thm)],[c_5]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_75,plain,
% 7.82/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.82/1.50      inference(renaming,[status(thm)],[c_74]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_97,plain,
% 7.82/1.50      ( ~ r1_tarski(X0,X1)
% 7.82/1.50      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 7.82/1.50      inference(bin_hyper_res,[status(thm)],[c_3,c_75]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_136,plain,
% 7.82/1.50      ( ~ r1_tarski(X0_41,X1_41)
% 7.82/1.50      | k4_xboole_0(X2_41,k4_xboole_0(X2_41,X0_41)) = k9_subset_1(X1_41,X2_41,X0_41) ),
% 7.82/1.50      inference(subtyping,[status(esa)],[c_97]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_476,plain,
% 7.82/1.50      ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = k9_subset_1(X2_41,X0_41,X1_41)
% 7.82/1.50      | r1_tarski(X1_41,X2_41) != iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_136]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1334,plain,
% 7.82/1.50      ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)) = k9_subset_1(u1_struct_0(sK0),X0_41,sK2) ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1036,c_476]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_8,negated_conjecture,
% 7.82/1.50      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 7.82/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_141,negated_conjecture,
% 7.82/1.50      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 7.82/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_471,plain,
% 7.82/1.50      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_141]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1367,plain,
% 7.82/1.50      ( v2_tex_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) != iProver_top ),
% 7.82/1.50      inference(demodulation,[status(thm)],[c_1334,c_471]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1368,plain,
% 7.82/1.50      ( ~ v2_tex_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) ),
% 7.82/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_1367]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_0,plain,
% 7.82/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.82/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_148,plain,
% 7.82/1.50      ( k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)) = k4_xboole_0(X1_41,k4_xboole_0(X1_41,X0_41)) ),
% 7.82/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_160,plain,
% 7.82/1.50      ( ~ v2_tex_2(X0_41,X0_42)
% 7.82/1.50      | v2_tex_2(X1_41,X0_42)
% 7.82/1.50      | X1_41 != X0_41 ),
% 7.82/1.50      theory(equality) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_3787,plain,
% 7.82/1.50      ( ~ v2_tex_2(k4_xboole_0(X0_41,k4_xboole_0(X0_41,X1_41)),X0_42)
% 7.82/1.50      | v2_tex_2(k4_xboole_0(X1_41,k4_xboole_0(X1_41,X0_41)),X0_42) ),
% 7.82/1.50      inference(resolution,[status(thm)],[c_148,c_160]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_154,plain,
% 7.82/1.50      ( X0_41 != X1_41
% 7.82/1.50      | k4_xboole_0(X2_41,X0_41) = k4_xboole_0(X2_41,X1_41) ),
% 7.82/1.50      theory(equality) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1819,plain,
% 7.82/1.50      ( ~ v2_tex_2(k4_xboole_0(X0_41,X1_41),X0_42)
% 7.82/1.50      | v2_tex_2(k4_xboole_0(X0_41,X2_41),X0_42)
% 7.82/1.50      | X2_41 != X1_41 ),
% 7.82/1.50      inference(resolution,[status(thm)],[c_154,c_160]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1,plain,
% 7.82/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1) ),
% 7.82/1.50      inference(cnf_transformation,[],[f24]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_147,plain,
% 7.82/1.50      ( ~ r1_tarski(X0_41,X1_41)
% 7.82/1.50      | r1_tarski(k4_xboole_0(X0_41,X2_41),X1_41) ),
% 7.82/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_8609,plain,
% 7.82/1.50      ( v2_tex_2(k4_xboole_0(X0_41,X1_41),sK0)
% 7.82/1.50      | ~ v2_tex_2(sK2,sK0)
% 7.82/1.50      | ~ r1_tarski(X0_41,u1_struct_0(sK0))
% 7.82/1.50      | ~ r1_tarski(k4_xboole_0(X0_41,X1_41),sK2) ),
% 7.82/1.50      inference(resolution,[status(thm)],[c_7773,c_147]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_10060,plain,
% 7.82/1.50      ( v2_tex_2(k4_xboole_0(X0_41,X1_41),sK0)
% 7.82/1.50      | ~ v2_tex_2(sK2,sK0)
% 7.82/1.50      | ~ r1_tarski(X0_41,u1_struct_0(sK0))
% 7.82/1.50      | ~ r1_tarski(k4_xboole_0(X0_41,X2_41),sK2)
% 7.82/1.50      | X1_41 != X2_41 ),
% 7.82/1.50      inference(resolution,[status(thm)],[c_1819,c_8609]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2,plain,
% 7.82/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.82/1.50      inference(cnf_transformation,[],[f25]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_146,plain,
% 7.82/1.50      ( r1_tarski(k4_xboole_0(X0_41,X1_41),X0_41) ),
% 7.82/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_10977,plain,
% 7.82/1.50      ( v2_tex_2(k4_xboole_0(sK2,X0_41),sK0)
% 7.82/1.50      | ~ v2_tex_2(sK2,sK0)
% 7.82/1.50      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 7.82/1.50      | X0_41 != X1_41 ),
% 7.82/1.50      inference(resolution,[status(thm)],[c_10060,c_146]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_560,plain,
% 7.82/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.82/1.50      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 7.82/1.50      inference(instantiation,[status(thm)],[c_143]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_650,plain,
% 7.82/1.50      ( r1_tarski(k4_xboole_0(sK2,X0_41),u1_struct_0(sK0))
% 7.82/1.50      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 7.82/1.50      inference(instantiation,[status(thm)],[c_147]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_615,plain,
% 7.82/1.50      ( ~ v2_tex_2(X0_41,X0_42)
% 7.82/1.50      | v2_tex_2(k4_xboole_0(X0_41,X1_41),X0_42)
% 7.82/1.50      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.82/1.50      | ~ m1_subset_1(k4_xboole_0(X0_41,X1_41),k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.82/1.50      | ~ r1_tarski(k4_xboole_0(X0_41,X1_41),X0_41)
% 7.82/1.50      | ~ l1_pre_topc(X0_42) ),
% 7.82/1.50      inference(instantiation,[status(thm)],[c_142]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_734,plain,
% 7.82/1.50      ( v2_tex_2(k4_xboole_0(sK2,X0_41),sK0)
% 7.82/1.50      | ~ v2_tex_2(sK2,sK0)
% 7.82/1.50      | ~ m1_subset_1(k4_xboole_0(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.82/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.82/1.50      | ~ r1_tarski(k4_xboole_0(sK2,X0_41),sK2)
% 7.82/1.50      | ~ l1_pre_topc(sK0) ),
% 7.82/1.50      inference(instantiation,[status(thm)],[c_615]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_781,plain,
% 7.82/1.50      ( r1_tarski(k4_xboole_0(sK2,X0_41),sK2) ),
% 7.82/1.50      inference(instantiation,[status(thm)],[c_146]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_793,plain,
% 7.82/1.50      ( m1_subset_1(k4_xboole_0(sK2,X0_41),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.82/1.50      | ~ r1_tarski(k4_xboole_0(sK2,X0_41),u1_struct_0(sK0)) ),
% 7.82/1.50      inference(instantiation,[status(thm)],[c_144]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_11523,plain,
% 7.82/1.50      ( v2_tex_2(k4_xboole_0(sK2,X0_41),sK0) | ~ v2_tex_2(sK2,sK0) ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_10977,c_12,c_10,c_560,c_650,c_734,c_781,c_793]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_13843,plain,
% 7.82/1.50      ( v2_tex_2(k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)),sK0)
% 7.82/1.50      | ~ v2_tex_2(sK2,sK0) ),
% 7.82/1.50      inference(resolution,[status(thm)],[c_3787,c_11523]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_13845,plain,
% 7.82/1.50      ( v2_tex_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
% 7.82/1.50      | ~ v2_tex_2(sK2,sK0) ),
% 7.82/1.50      inference(instantiation,[status(thm)],[c_13843]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_14160,plain,
% 7.82/1.50      ( ~ v2_tex_2(sK2,sK0) ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_13865,c_1368,c_13845]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_9,negated_conjecture,
% 7.82/1.50      ( v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0) ),
% 7.82/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_140,negated_conjecture,
% 7.82/1.50      ( v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0) ),
% 7.82/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_14171,plain,
% 7.82/1.50      ( v2_tex_2(sK1,sK0) ),
% 7.82/1.50      inference(backward_subsumption_resolution,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_14160,c_140]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_11,negated_conjecture,
% 7.82/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.82/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_138,negated_conjecture,
% 7.82/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.82/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_6988,plain,
% 7.82/1.50      ( v2_tex_2(X0_41,sK0)
% 7.82/1.50      | ~ v2_tex_2(sK1,sK0)
% 7.82/1.50      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.82/1.50      | ~ r1_tarski(X0_41,sK1)
% 7.82/1.50      | ~ l1_pre_topc(sK0) ),
% 7.82/1.50      inference(resolution,[status(thm)],[c_142,c_138]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_8569,plain,
% 7.82/1.50      ( ~ r1_tarski(X0_41,sK1)
% 7.82/1.50      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.82/1.50      | ~ v2_tex_2(sK1,sK0)
% 7.82/1.50      | v2_tex_2(X0_41,sK0) ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.51                [status(thm)],
% 7.82/1.51                [c_6988,c_12]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_8570,plain,
% 7.82/1.51      ( v2_tex_2(X0_41,sK0)
% 7.82/1.51      | ~ v2_tex_2(sK1,sK0)
% 7.82/1.51      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.82/1.51      | ~ r1_tarski(X0_41,sK1) ),
% 7.82/1.51      inference(renaming,[status(thm)],[c_8569]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_14177,plain,
% 7.82/1.51      ( v2_tex_2(X0_41,sK0)
% 7.82/1.51      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.82/1.51      | ~ r1_tarski(X0_41,sK1) ),
% 7.82/1.51      inference(backward_subsumption_resolution,
% 7.82/1.51                [status(thm)],
% 7.82/1.51                [c_14171,c_8570]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_15213,plain,
% 7.82/1.51      ( v2_tex_2(X0_41,sK0)
% 7.82/1.51      | ~ r1_tarski(X0_41,u1_struct_0(sK0))
% 7.82/1.51      | ~ r1_tarski(X0_41,sK1) ),
% 7.82/1.51      inference(resolution,[status(thm)],[c_14177,c_144]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_153,plain,
% 7.82/1.51      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 7.82/1.51      theory(equality) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_150,plain,( X0_41 = X0_41 ),theory(equality) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_2038,plain,
% 7.82/1.51      ( X0_41 != X1_41 | X1_41 = X0_41 ),
% 7.82/1.51      inference(resolution,[status(thm)],[c_153,c_150]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_3770,plain,
% 7.82/1.51      ( ~ r1_tarski(X0_41,X1_41)
% 7.82/1.51      | k9_subset_1(X1_41,X2_41,X0_41) = k4_xboole_0(X2_41,k4_xboole_0(X2_41,X0_41)) ),
% 7.82/1.51      inference(resolution,[status(thm)],[c_2038,c_136]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_4899,plain,
% 7.82/1.51      ( ~ r1_tarski(X0_41,X1_41)
% 7.82/1.51      | r1_tarski(k9_subset_1(X1_41,X2_41,X0_41),X3_41)
% 7.82/1.51      | ~ r1_tarski(k4_xboole_0(X2_41,k4_xboole_0(X2_41,X0_41)),X3_41) ),
% 7.82/1.51      inference(resolution,[status(thm)],[c_3770,c_155]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_6582,plain,
% 7.82/1.51      ( ~ r1_tarski(X0_41,X1_41)
% 7.82/1.51      | ~ r1_tarski(X2_41,X3_41)
% 7.82/1.51      | r1_tarski(k9_subset_1(X1_41,X2_41,X0_41),X3_41) ),
% 7.82/1.51      inference(resolution,[status(thm)],[c_4899,c_147]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_16870,plain,
% 7.82/1.51      ( v2_tex_2(k9_subset_1(X0_41,X1_41,X2_41),sK0)
% 7.82/1.51      | ~ r1_tarski(X2_41,X0_41)
% 7.82/1.51      | ~ r1_tarski(X1_41,u1_struct_0(sK0))
% 7.82/1.51      | ~ r1_tarski(k9_subset_1(X0_41,X1_41,X2_41),sK1) ),
% 7.82/1.51      inference(resolution,[status(thm)],[c_15213,c_6582]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_17241,plain,
% 7.82/1.51      ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 7.82/1.51      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 7.82/1.51      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.82/1.51      inference(resolution,[status(thm)],[c_16870,c_141]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_11120,plain,
% 7.82/1.51      ( r1_tarski(k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)),X0_41) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_146]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_11122,plain,
% 7.82/1.51      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_11120]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_644,plain,
% 7.82/1.51      ( r1_tarski(X0_41,X1_41)
% 7.82/1.51      | ~ r1_tarski(k4_xboole_0(X1_41,X2_41),X1_41)
% 7.82/1.51      | X0_41 != k4_xboole_0(X1_41,X2_41) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_155]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_3254,plain,
% 7.82/1.51      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_41,sK2),X0_41)
% 7.82/1.51      | ~ r1_tarski(k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)),X0_41)
% 7.82/1.51      | k9_subset_1(u1_struct_0(sK0),X0_41,sK2) != k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_644]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_3256,plain,
% 7.82/1.51      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 7.82/1.51      | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
% 7.82/1.51      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_3254]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_2248,plain,
% 7.82/1.51      ( k9_subset_1(u1_struct_0(sK0),X0_41,sK2) = k9_subset_1(u1_struct_0(sK0),X0_41,sK2) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_150]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_2250,plain,
% 7.82/1.51      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_2248]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_962,plain,
% 7.82/1.51      ( X0_41 != X1_41
% 7.82/1.51      | X0_41 = k4_xboole_0(X2_41,X3_41)
% 7.82/1.51      | k4_xboole_0(X2_41,X3_41) != X1_41 ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_153]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_1680,plain,
% 7.82/1.51      ( X0_41 != k9_subset_1(u1_struct_0(sK0),X1_41,sK2)
% 7.82/1.51      | X0_41 = k4_xboole_0(X1_41,k4_xboole_0(X1_41,sK2))
% 7.82/1.51      | k4_xboole_0(X1_41,k4_xboole_0(X1_41,sK2)) != k9_subset_1(u1_struct_0(sK0),X1_41,sK2) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_962]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_2247,plain,
% 7.82/1.51      ( k9_subset_1(u1_struct_0(sK0),X0_41,sK2) != k9_subset_1(u1_struct_0(sK0),X0_41,sK2)
% 7.82/1.51      | k9_subset_1(u1_struct_0(sK0),X0_41,sK2) = k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2))
% 7.82/1.51      | k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)) != k9_subset_1(u1_struct_0(sK0),X0_41,sK2) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_1680]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_2249,plain,
% 7.82/1.51      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
% 7.82/1.51      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 7.82/1.51      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_2247]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_651,plain,
% 7.82/1.51      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 7.82/1.51      | k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)) = k9_subset_1(u1_struct_0(sK0),X0_41,sK2) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_136]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_654,plain,
% 7.82/1.51      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 7.82/1.51      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_651]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(c_563,plain,
% 7.82/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.82/1.51      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.82/1.51      inference(instantiation,[status(thm)],[c_143]) ).
% 7.82/1.51  
% 7.82/1.51  cnf(contradiction,plain,
% 7.82/1.51      ( $false ),
% 7.82/1.51      inference(minisat,
% 7.82/1.51                [status(thm)],
% 7.82/1.51                [c_17241,c_11122,c_3256,c_2250,c_2249,c_654,c_563,c_560,
% 7.82/1.51                 c_10,c_11]) ).
% 7.82/1.51  
% 7.82/1.51  
% 7.82/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.82/1.51  
% 7.82/1.51  ------                               Statistics
% 7.82/1.51  
% 7.82/1.51  ------ Selected
% 7.82/1.51  
% 7.82/1.51  total_time:                             0.847
% 7.82/1.51  
%------------------------------------------------------------------------------
