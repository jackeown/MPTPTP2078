%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:53 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 348 expanded)
%              Number of clauses        :   80 ( 136 expanded)
%              Number of leaves         :   18 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  308 (1195 expanded)
%              Number of equality atoms :  117 ( 191 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24,f23])).

fof(f42,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f34,f29])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f29,f30])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_101,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_102,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_101])).

cnf(c_126,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_102])).

cnf(c_657,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_126])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_662,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1732,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_662])).

cnf(c_11,negated_conjecture,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_660,plain,
    ( v2_tex_2(sK2,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_663,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_659,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_185,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_186,plain,
    ( ~ v2_tex_2(X0,sK0)
    | v2_tex_2(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_655,plain,
    ( v2_tex_2(X0,sK0) != iProver_top
    | v2_tex_2(X1,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_850,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_655])).

cnf(c_1813,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_850])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_933,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1241,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_1242,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1241])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_928,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1577,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_928])).

cnf(c_1578,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1577])).

cnf(c_3211,plain,
    ( v2_tex_2(sK2,sK0) != iProver_top
    | v2_tex_2(X0,sK0) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1813,c_17,c_1242,c_1578])).

cnf(c_3212,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3211])).

cnf(c_3220,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_660,c_3212])).

cnf(c_3660,plain,
    ( v2_tex_2(k9_subset_1(sK2,X0,X1),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top
    | r1_tarski(X1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_3220])).

cnf(c_10,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1730,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_662])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_127,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_102])).

cnf(c_656,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127])).

cnf(c_6,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_698,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_656,c_6])).

cnf(c_2096,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(superposition,[status(thm)],[c_1730,c_698])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_665,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1333,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_665])).

cnf(c_2238,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2096,c_1333])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_658,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_851,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_658,c_655])).

cnf(c_1036,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0,X1),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,X1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_851])).

cnf(c_3770,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2238,c_1036])).

cnf(c_5899,plain,
    ( v2_tex_2(k9_subset_1(sK2,X0,X1),sK0) = iProver_top
    | r1_tarski(X1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3660,c_17,c_19,c_1242,c_3770])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_664,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_673,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_664,c_2])).

cnf(c_1733,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_662])).

cnf(c_3070,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_1733,c_698])).

cnf(c_661,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2235,plain,
    ( v2_tex_2(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2096,c_661])).

cnf(c_4049,plain,
    ( v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3070,c_2235])).

cnf(c_5907,plain,
    ( r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5899,c_4049])).

cnf(c_329,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_978,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(X1,sK2)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_1640,plain,
    ( r1_tarski(X0,sK2)
    | ~ r1_tarski(k2_subset_1(sK2),sK2)
    | X0 != k2_subset_1(sK2) ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_3083,plain,
    ( ~ r1_tarski(k2_subset_1(sK2),sK2)
    | r1_tarski(sK2,sK2)
    | sK2 != k2_subset_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_3084,plain,
    ( sK2 != k2_subset_1(sK2)
    | r1_tarski(k2_subset_1(sK2),sK2) != iProver_top
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3083])).

cnf(c_328,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1010,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_1426,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_2048,plain,
    ( k2_subset_1(sK2) != sK2
    | sK2 = k2_subset_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1426])).

cnf(c_1262,plain,
    ( m1_subset_1(k2_subset_1(sK2),k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1265,plain,
    ( m1_subset_1(k2_subset_1(sK2),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1262])).

cnf(c_984,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1261,plain,
    ( ~ m1_subset_1(k2_subset_1(sK2),k1_zfmisc_1(sK2))
    | r1_tarski(k2_subset_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_1263,plain,
    ( m1_subset_1(k2_subset_1(sK2),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k2_subset_1(sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1261])).

cnf(c_327,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_814,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_808,plain,
    ( k2_subset_1(sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5907,c_3084,c_2048,c_1265,c_1263,c_814,c_808])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.10/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.00  
% 3.10/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/1.00  
% 3.10/1.00  ------  iProver source info
% 3.10/1.00  
% 3.10/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.10/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/1.00  git: non_committed_changes: false
% 3.10/1.00  git: last_make_outside_of_git: false
% 3.10/1.00  
% 3.10/1.00  ------ 
% 3.10/1.00  
% 3.10/1.00  ------ Input Options
% 3.10/1.00  
% 3.10/1.00  --out_options                           all
% 3.10/1.00  --tptp_safe_out                         true
% 3.10/1.00  --problem_path                          ""
% 3.10/1.00  --include_path                          ""
% 3.10/1.00  --clausifier                            res/vclausify_rel
% 3.10/1.00  --clausifier_options                    --mode clausify
% 3.10/1.00  --stdin                                 false
% 3.10/1.00  --stats_out                             all
% 3.10/1.00  
% 3.10/1.00  ------ General Options
% 3.10/1.00  
% 3.10/1.00  --fof                                   false
% 3.10/1.00  --time_out_real                         305.
% 3.10/1.00  --time_out_virtual                      -1.
% 3.10/1.00  --symbol_type_check                     false
% 3.10/1.00  --clausify_out                          false
% 3.10/1.00  --sig_cnt_out                           false
% 3.10/1.01  --trig_cnt_out                          false
% 3.10/1.01  --trig_cnt_out_tolerance                1.
% 3.10/1.01  --trig_cnt_out_sk_spl                   false
% 3.10/1.01  --abstr_cl_out                          false
% 3.10/1.01  
% 3.10/1.01  ------ Global Options
% 3.10/1.01  
% 3.10/1.01  --schedule                              default
% 3.10/1.01  --add_important_lit                     false
% 3.10/1.01  --prop_solver_per_cl                    1000
% 3.10/1.01  --min_unsat_core                        false
% 3.10/1.01  --soft_assumptions                      false
% 3.10/1.01  --soft_lemma_size                       3
% 3.10/1.01  --prop_impl_unit_size                   0
% 3.10/1.01  --prop_impl_unit                        []
% 3.10/1.01  --share_sel_clauses                     true
% 3.10/1.01  --reset_solvers                         false
% 3.10/1.01  --bc_imp_inh                            [conj_cone]
% 3.10/1.01  --conj_cone_tolerance                   3.
% 3.10/1.01  --extra_neg_conj                        none
% 3.10/1.01  --large_theory_mode                     true
% 3.10/1.01  --prolific_symb_bound                   200
% 3.10/1.01  --lt_threshold                          2000
% 3.10/1.01  --clause_weak_htbl                      true
% 3.10/1.01  --gc_record_bc_elim                     false
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing Options
% 3.10/1.01  
% 3.10/1.01  --preprocessing_flag                    true
% 3.10/1.01  --time_out_prep_mult                    0.1
% 3.10/1.01  --splitting_mode                        input
% 3.10/1.01  --splitting_grd                         true
% 3.10/1.01  --splitting_cvd                         false
% 3.10/1.01  --splitting_cvd_svl                     false
% 3.10/1.01  --splitting_nvd                         32
% 3.10/1.01  --sub_typing                            true
% 3.10/1.01  --prep_gs_sim                           true
% 3.10/1.01  --prep_unflatten                        true
% 3.10/1.01  --prep_res_sim                          true
% 3.10/1.01  --prep_upred                            true
% 3.10/1.01  --prep_sem_filter                       exhaustive
% 3.10/1.01  --prep_sem_filter_out                   false
% 3.10/1.01  --pred_elim                             true
% 3.10/1.01  --res_sim_input                         true
% 3.10/1.01  --eq_ax_congr_red                       true
% 3.10/1.01  --pure_diseq_elim                       true
% 3.10/1.01  --brand_transform                       false
% 3.10/1.01  --non_eq_to_eq                          false
% 3.10/1.01  --prep_def_merge                        true
% 3.10/1.01  --prep_def_merge_prop_impl              false
% 3.10/1.01  --prep_def_merge_mbd                    true
% 3.10/1.01  --prep_def_merge_tr_red                 false
% 3.10/1.01  --prep_def_merge_tr_cl                  false
% 3.10/1.01  --smt_preprocessing                     true
% 3.10/1.01  --smt_ac_axioms                         fast
% 3.10/1.01  --preprocessed_out                      false
% 3.10/1.01  --preprocessed_stats                    false
% 3.10/1.01  
% 3.10/1.01  ------ Abstraction refinement Options
% 3.10/1.01  
% 3.10/1.01  --abstr_ref                             []
% 3.10/1.01  --abstr_ref_prep                        false
% 3.10/1.01  --abstr_ref_until_sat                   false
% 3.10/1.01  --abstr_ref_sig_restrict                funpre
% 3.10/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/1.01  --abstr_ref_under                       []
% 3.10/1.01  
% 3.10/1.01  ------ SAT Options
% 3.10/1.01  
% 3.10/1.01  --sat_mode                              false
% 3.10/1.01  --sat_fm_restart_options                ""
% 3.10/1.01  --sat_gr_def                            false
% 3.10/1.01  --sat_epr_types                         true
% 3.10/1.01  --sat_non_cyclic_types                  false
% 3.10/1.01  --sat_finite_models                     false
% 3.10/1.01  --sat_fm_lemmas                         false
% 3.10/1.01  --sat_fm_prep                           false
% 3.10/1.01  --sat_fm_uc_incr                        true
% 3.10/1.01  --sat_out_model                         small
% 3.10/1.01  --sat_out_clauses                       false
% 3.10/1.01  
% 3.10/1.01  ------ QBF Options
% 3.10/1.01  
% 3.10/1.01  --qbf_mode                              false
% 3.10/1.01  --qbf_elim_univ                         false
% 3.10/1.01  --qbf_dom_inst                          none
% 3.10/1.01  --qbf_dom_pre_inst                      false
% 3.10/1.01  --qbf_sk_in                             false
% 3.10/1.01  --qbf_pred_elim                         true
% 3.10/1.01  --qbf_split                             512
% 3.10/1.01  
% 3.10/1.01  ------ BMC1 Options
% 3.10/1.01  
% 3.10/1.01  --bmc1_incremental                      false
% 3.10/1.01  --bmc1_axioms                           reachable_all
% 3.10/1.01  --bmc1_min_bound                        0
% 3.10/1.01  --bmc1_max_bound                        -1
% 3.10/1.01  --bmc1_max_bound_default                -1
% 3.10/1.01  --bmc1_symbol_reachability              true
% 3.10/1.01  --bmc1_property_lemmas                  false
% 3.10/1.01  --bmc1_k_induction                      false
% 3.10/1.01  --bmc1_non_equiv_states                 false
% 3.10/1.01  --bmc1_deadlock                         false
% 3.10/1.01  --bmc1_ucm                              false
% 3.10/1.01  --bmc1_add_unsat_core                   none
% 3.10/1.01  --bmc1_unsat_core_children              false
% 3.10/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/1.01  --bmc1_out_stat                         full
% 3.10/1.01  --bmc1_ground_init                      false
% 3.10/1.01  --bmc1_pre_inst_next_state              false
% 3.10/1.01  --bmc1_pre_inst_state                   false
% 3.10/1.01  --bmc1_pre_inst_reach_state             false
% 3.10/1.01  --bmc1_out_unsat_core                   false
% 3.10/1.01  --bmc1_aig_witness_out                  false
% 3.10/1.01  --bmc1_verbose                          false
% 3.10/1.01  --bmc1_dump_clauses_tptp                false
% 3.10/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.10/1.01  --bmc1_dump_file                        -
% 3.10/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.10/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.10/1.01  --bmc1_ucm_extend_mode                  1
% 3.10/1.01  --bmc1_ucm_init_mode                    2
% 3.10/1.01  --bmc1_ucm_cone_mode                    none
% 3.10/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.10/1.01  --bmc1_ucm_relax_model                  4
% 3.10/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.10/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/1.01  --bmc1_ucm_layered_model                none
% 3.10/1.01  --bmc1_ucm_max_lemma_size               10
% 3.10/1.01  
% 3.10/1.01  ------ AIG Options
% 3.10/1.01  
% 3.10/1.01  --aig_mode                              false
% 3.10/1.01  
% 3.10/1.01  ------ Instantiation Options
% 3.10/1.01  
% 3.10/1.01  --instantiation_flag                    true
% 3.10/1.01  --inst_sos_flag                         false
% 3.10/1.01  --inst_sos_phase                        true
% 3.10/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/1.01  --inst_lit_sel_side                     num_symb
% 3.10/1.01  --inst_solver_per_active                1400
% 3.10/1.01  --inst_solver_calls_frac                1.
% 3.10/1.01  --inst_passive_queue_type               priority_queues
% 3.10/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/1.01  --inst_passive_queues_freq              [25;2]
% 3.10/1.01  --inst_dismatching                      true
% 3.10/1.01  --inst_eager_unprocessed_to_passive     true
% 3.10/1.01  --inst_prop_sim_given                   true
% 3.10/1.01  --inst_prop_sim_new                     false
% 3.10/1.01  --inst_subs_new                         false
% 3.10/1.01  --inst_eq_res_simp                      false
% 3.10/1.01  --inst_subs_given                       false
% 3.10/1.01  --inst_orphan_elimination               true
% 3.10/1.01  --inst_learning_loop_flag               true
% 3.10/1.01  --inst_learning_start                   3000
% 3.10/1.01  --inst_learning_factor                  2
% 3.10/1.01  --inst_start_prop_sim_after_learn       3
% 3.10/1.01  --inst_sel_renew                        solver
% 3.10/1.01  --inst_lit_activity_flag                true
% 3.10/1.01  --inst_restr_to_given                   false
% 3.10/1.01  --inst_activity_threshold               500
% 3.10/1.01  --inst_out_proof                        true
% 3.10/1.01  
% 3.10/1.01  ------ Resolution Options
% 3.10/1.01  
% 3.10/1.01  --resolution_flag                       true
% 3.10/1.01  --res_lit_sel                           adaptive
% 3.10/1.01  --res_lit_sel_side                      none
% 3.10/1.01  --res_ordering                          kbo
% 3.10/1.01  --res_to_prop_solver                    active
% 3.10/1.01  --res_prop_simpl_new                    false
% 3.10/1.01  --res_prop_simpl_given                  true
% 3.10/1.01  --res_passive_queue_type                priority_queues
% 3.10/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/1.01  --res_passive_queues_freq               [15;5]
% 3.10/1.01  --res_forward_subs                      full
% 3.10/1.01  --res_backward_subs                     full
% 3.10/1.01  --res_forward_subs_resolution           true
% 3.10/1.01  --res_backward_subs_resolution          true
% 3.10/1.01  --res_orphan_elimination                true
% 3.10/1.01  --res_time_limit                        2.
% 3.10/1.01  --res_out_proof                         true
% 3.10/1.01  
% 3.10/1.01  ------ Superposition Options
% 3.10/1.01  
% 3.10/1.01  --superposition_flag                    true
% 3.10/1.01  --sup_passive_queue_type                priority_queues
% 3.10/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.10/1.01  --demod_completeness_check              fast
% 3.10/1.01  --demod_use_ground                      true
% 3.10/1.01  --sup_to_prop_solver                    passive
% 3.10/1.01  --sup_prop_simpl_new                    true
% 3.10/1.01  --sup_prop_simpl_given                  true
% 3.10/1.01  --sup_fun_splitting                     false
% 3.10/1.01  --sup_smt_interval                      50000
% 3.10/1.01  
% 3.10/1.01  ------ Superposition Simplification Setup
% 3.10/1.01  
% 3.10/1.01  --sup_indices_passive                   []
% 3.10/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.01  --sup_full_bw                           [BwDemod]
% 3.10/1.01  --sup_immed_triv                        [TrivRules]
% 3.10/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.01  --sup_immed_bw_main                     []
% 3.10/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.01  
% 3.10/1.01  ------ Combination Options
% 3.10/1.01  
% 3.10/1.01  --comb_res_mult                         3
% 3.10/1.01  --comb_sup_mult                         2
% 3.10/1.01  --comb_inst_mult                        10
% 3.10/1.01  
% 3.10/1.01  ------ Debug Options
% 3.10/1.01  
% 3.10/1.01  --dbg_backtrace                         false
% 3.10/1.01  --dbg_dump_prop_clauses                 false
% 3.10/1.01  --dbg_dump_prop_clauses_file            -
% 3.10/1.01  --dbg_out_stat                          false
% 3.10/1.01  ------ Parsing...
% 3.10/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/1.01  ------ Proving...
% 3.10/1.01  ------ Problem Properties 
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  clauses                                 14
% 3.10/1.01  conjectures                             4
% 3.10/1.01  EPR                                     2
% 3.10/1.01  Horn                                    13
% 3.10/1.01  unary                                   7
% 3.10/1.01  binary                                  5
% 3.10/1.01  lits                                    25
% 3.10/1.01  lits eq                                 3
% 3.10/1.01  fd_pure                                 0
% 3.10/1.01  fd_pseudo                               0
% 3.10/1.01  fd_cond                                 0
% 3.10/1.01  fd_pseudo_cond                          0
% 3.10/1.01  AC symbols                              0
% 3.10/1.01  
% 3.10/1.01  ------ Schedule dynamic 5 is on 
% 3.10/1.01  
% 3.10/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  ------ 
% 3.10/1.01  Current options:
% 3.10/1.01  ------ 
% 3.10/1.01  
% 3.10/1.01  ------ Input Options
% 3.10/1.01  
% 3.10/1.01  --out_options                           all
% 3.10/1.01  --tptp_safe_out                         true
% 3.10/1.01  --problem_path                          ""
% 3.10/1.01  --include_path                          ""
% 3.10/1.01  --clausifier                            res/vclausify_rel
% 3.10/1.01  --clausifier_options                    --mode clausify
% 3.10/1.01  --stdin                                 false
% 3.10/1.01  --stats_out                             all
% 3.10/1.01  
% 3.10/1.01  ------ General Options
% 3.10/1.01  
% 3.10/1.01  --fof                                   false
% 3.10/1.01  --time_out_real                         305.
% 3.10/1.01  --time_out_virtual                      -1.
% 3.10/1.01  --symbol_type_check                     false
% 3.10/1.01  --clausify_out                          false
% 3.10/1.01  --sig_cnt_out                           false
% 3.10/1.01  --trig_cnt_out                          false
% 3.10/1.01  --trig_cnt_out_tolerance                1.
% 3.10/1.01  --trig_cnt_out_sk_spl                   false
% 3.10/1.01  --abstr_cl_out                          false
% 3.10/1.01  
% 3.10/1.01  ------ Global Options
% 3.10/1.01  
% 3.10/1.01  --schedule                              default
% 3.10/1.01  --add_important_lit                     false
% 3.10/1.01  --prop_solver_per_cl                    1000
% 3.10/1.01  --min_unsat_core                        false
% 3.10/1.01  --soft_assumptions                      false
% 3.10/1.01  --soft_lemma_size                       3
% 3.10/1.01  --prop_impl_unit_size                   0
% 3.10/1.01  --prop_impl_unit                        []
% 3.10/1.01  --share_sel_clauses                     true
% 3.10/1.01  --reset_solvers                         false
% 3.10/1.01  --bc_imp_inh                            [conj_cone]
% 3.10/1.01  --conj_cone_tolerance                   3.
% 3.10/1.01  --extra_neg_conj                        none
% 3.10/1.01  --large_theory_mode                     true
% 3.10/1.01  --prolific_symb_bound                   200
% 3.10/1.01  --lt_threshold                          2000
% 3.10/1.01  --clause_weak_htbl                      true
% 3.10/1.01  --gc_record_bc_elim                     false
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing Options
% 3.10/1.01  
% 3.10/1.01  --preprocessing_flag                    true
% 3.10/1.01  --time_out_prep_mult                    0.1
% 3.10/1.01  --splitting_mode                        input
% 3.10/1.01  --splitting_grd                         true
% 3.10/1.01  --splitting_cvd                         false
% 3.10/1.01  --splitting_cvd_svl                     false
% 3.10/1.01  --splitting_nvd                         32
% 3.10/1.01  --sub_typing                            true
% 3.10/1.01  --prep_gs_sim                           true
% 3.10/1.01  --prep_unflatten                        true
% 3.10/1.01  --prep_res_sim                          true
% 3.10/1.01  --prep_upred                            true
% 3.10/1.01  --prep_sem_filter                       exhaustive
% 3.10/1.01  --prep_sem_filter_out                   false
% 3.10/1.01  --pred_elim                             true
% 3.10/1.01  --res_sim_input                         true
% 3.10/1.01  --eq_ax_congr_red                       true
% 3.10/1.01  --pure_diseq_elim                       true
% 3.10/1.01  --brand_transform                       false
% 3.10/1.01  --non_eq_to_eq                          false
% 3.10/1.01  --prep_def_merge                        true
% 3.10/1.01  --prep_def_merge_prop_impl              false
% 3.10/1.01  --prep_def_merge_mbd                    true
% 3.10/1.01  --prep_def_merge_tr_red                 false
% 3.10/1.01  --prep_def_merge_tr_cl                  false
% 3.10/1.01  --smt_preprocessing                     true
% 3.10/1.01  --smt_ac_axioms                         fast
% 3.10/1.01  --preprocessed_out                      false
% 3.10/1.01  --preprocessed_stats                    false
% 3.10/1.01  
% 3.10/1.01  ------ Abstraction refinement Options
% 3.10/1.01  
% 3.10/1.01  --abstr_ref                             []
% 3.10/1.01  --abstr_ref_prep                        false
% 3.10/1.01  --abstr_ref_until_sat                   false
% 3.10/1.01  --abstr_ref_sig_restrict                funpre
% 3.10/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/1.01  --abstr_ref_under                       []
% 3.10/1.01  
% 3.10/1.01  ------ SAT Options
% 3.10/1.01  
% 3.10/1.01  --sat_mode                              false
% 3.10/1.01  --sat_fm_restart_options                ""
% 3.10/1.01  --sat_gr_def                            false
% 3.10/1.01  --sat_epr_types                         true
% 3.10/1.01  --sat_non_cyclic_types                  false
% 3.10/1.01  --sat_finite_models                     false
% 3.10/1.01  --sat_fm_lemmas                         false
% 3.10/1.01  --sat_fm_prep                           false
% 3.10/1.01  --sat_fm_uc_incr                        true
% 3.10/1.01  --sat_out_model                         small
% 3.10/1.01  --sat_out_clauses                       false
% 3.10/1.01  
% 3.10/1.01  ------ QBF Options
% 3.10/1.01  
% 3.10/1.01  --qbf_mode                              false
% 3.10/1.01  --qbf_elim_univ                         false
% 3.10/1.01  --qbf_dom_inst                          none
% 3.10/1.01  --qbf_dom_pre_inst                      false
% 3.10/1.01  --qbf_sk_in                             false
% 3.10/1.01  --qbf_pred_elim                         true
% 3.10/1.01  --qbf_split                             512
% 3.10/1.01  
% 3.10/1.01  ------ BMC1 Options
% 3.10/1.01  
% 3.10/1.01  --bmc1_incremental                      false
% 3.10/1.01  --bmc1_axioms                           reachable_all
% 3.10/1.01  --bmc1_min_bound                        0
% 3.10/1.01  --bmc1_max_bound                        -1
% 3.10/1.01  --bmc1_max_bound_default                -1
% 3.10/1.01  --bmc1_symbol_reachability              true
% 3.10/1.01  --bmc1_property_lemmas                  false
% 3.10/1.01  --bmc1_k_induction                      false
% 3.10/1.01  --bmc1_non_equiv_states                 false
% 3.10/1.01  --bmc1_deadlock                         false
% 3.10/1.01  --bmc1_ucm                              false
% 3.10/1.01  --bmc1_add_unsat_core                   none
% 3.10/1.01  --bmc1_unsat_core_children              false
% 3.10/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/1.01  --bmc1_out_stat                         full
% 3.10/1.01  --bmc1_ground_init                      false
% 3.10/1.01  --bmc1_pre_inst_next_state              false
% 3.10/1.01  --bmc1_pre_inst_state                   false
% 3.10/1.01  --bmc1_pre_inst_reach_state             false
% 3.10/1.01  --bmc1_out_unsat_core                   false
% 3.10/1.01  --bmc1_aig_witness_out                  false
% 3.10/1.01  --bmc1_verbose                          false
% 3.10/1.01  --bmc1_dump_clauses_tptp                false
% 3.10/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.10/1.01  --bmc1_dump_file                        -
% 3.10/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.10/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.10/1.01  --bmc1_ucm_extend_mode                  1
% 3.10/1.01  --bmc1_ucm_init_mode                    2
% 3.10/1.01  --bmc1_ucm_cone_mode                    none
% 3.10/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.10/1.01  --bmc1_ucm_relax_model                  4
% 3.10/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.10/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/1.01  --bmc1_ucm_layered_model                none
% 3.10/1.01  --bmc1_ucm_max_lemma_size               10
% 3.10/1.01  
% 3.10/1.01  ------ AIG Options
% 3.10/1.01  
% 3.10/1.01  --aig_mode                              false
% 3.10/1.01  
% 3.10/1.01  ------ Instantiation Options
% 3.10/1.01  
% 3.10/1.01  --instantiation_flag                    true
% 3.10/1.01  --inst_sos_flag                         false
% 3.10/1.01  --inst_sos_phase                        true
% 3.10/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/1.01  --inst_lit_sel_side                     none
% 3.10/1.01  --inst_solver_per_active                1400
% 3.10/1.01  --inst_solver_calls_frac                1.
% 3.10/1.01  --inst_passive_queue_type               priority_queues
% 3.10/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/1.01  --inst_passive_queues_freq              [25;2]
% 3.10/1.01  --inst_dismatching                      true
% 3.10/1.01  --inst_eager_unprocessed_to_passive     true
% 3.10/1.01  --inst_prop_sim_given                   true
% 3.10/1.01  --inst_prop_sim_new                     false
% 3.10/1.01  --inst_subs_new                         false
% 3.10/1.01  --inst_eq_res_simp                      false
% 3.10/1.01  --inst_subs_given                       false
% 3.10/1.01  --inst_orphan_elimination               true
% 3.10/1.01  --inst_learning_loop_flag               true
% 3.10/1.01  --inst_learning_start                   3000
% 3.10/1.01  --inst_learning_factor                  2
% 3.10/1.01  --inst_start_prop_sim_after_learn       3
% 3.10/1.01  --inst_sel_renew                        solver
% 3.10/1.01  --inst_lit_activity_flag                true
% 3.10/1.01  --inst_restr_to_given                   false
% 3.10/1.01  --inst_activity_threshold               500
% 3.10/1.01  --inst_out_proof                        true
% 3.10/1.01  
% 3.10/1.01  ------ Resolution Options
% 3.10/1.01  
% 3.10/1.01  --resolution_flag                       false
% 3.10/1.01  --res_lit_sel                           adaptive
% 3.10/1.01  --res_lit_sel_side                      none
% 3.10/1.01  --res_ordering                          kbo
% 3.10/1.01  --res_to_prop_solver                    active
% 3.10/1.01  --res_prop_simpl_new                    false
% 3.10/1.01  --res_prop_simpl_given                  true
% 3.10/1.01  --res_passive_queue_type                priority_queues
% 3.10/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/1.01  --res_passive_queues_freq               [15;5]
% 3.10/1.01  --res_forward_subs                      full
% 3.10/1.01  --res_backward_subs                     full
% 3.10/1.01  --res_forward_subs_resolution           true
% 3.10/1.01  --res_backward_subs_resolution          true
% 3.10/1.01  --res_orphan_elimination                true
% 3.10/1.01  --res_time_limit                        2.
% 3.10/1.01  --res_out_proof                         true
% 3.10/1.01  
% 3.10/1.01  ------ Superposition Options
% 3.10/1.01  
% 3.10/1.01  --superposition_flag                    true
% 3.10/1.01  --sup_passive_queue_type                priority_queues
% 3.10/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.10/1.01  --demod_completeness_check              fast
% 3.10/1.01  --demod_use_ground                      true
% 3.10/1.01  --sup_to_prop_solver                    passive
% 3.10/1.01  --sup_prop_simpl_new                    true
% 3.10/1.01  --sup_prop_simpl_given                  true
% 3.10/1.01  --sup_fun_splitting                     false
% 3.10/1.01  --sup_smt_interval                      50000
% 3.10/1.01  
% 3.10/1.01  ------ Superposition Simplification Setup
% 3.10/1.01  
% 3.10/1.01  --sup_indices_passive                   []
% 3.10/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.01  --sup_full_bw                           [BwDemod]
% 3.10/1.01  --sup_immed_triv                        [TrivRules]
% 3.10/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.01  --sup_immed_bw_main                     []
% 3.10/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.01  
% 3.10/1.01  ------ Combination Options
% 3.10/1.01  
% 3.10/1.01  --comb_res_mult                         3
% 3.10/1.01  --comb_sup_mult                         2
% 3.10/1.01  --comb_inst_mult                        10
% 3.10/1.01  
% 3.10/1.01  ------ Debug Options
% 3.10/1.01  
% 3.10/1.01  --dbg_backtrace                         false
% 3.10/1.01  --dbg_dump_prop_clauses                 false
% 3.10/1.01  --dbg_dump_prop_clauses_file            -
% 3.10/1.01  --dbg_out_stat                          false
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  ------ Proving...
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  % SZS status Theorem for theBenchmark.p
% 3.10/1.01  
% 3.10/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/1.01  
% 3.10/1.01  fof(f7,axiom,(
% 3.10/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f16,plain,(
% 3.10/1.01    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.10/1.01    inference(ennf_transformation,[],[f7])).
% 3.10/1.01  
% 3.10/1.01  fof(f33,plain,(
% 3.10/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.10/1.01    inference(cnf_transformation,[],[f16])).
% 3.10/1.01  
% 3.10/1.01  fof(f10,axiom,(
% 3.10/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f22,plain,(
% 3.10/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.10/1.01    inference(nnf_transformation,[],[f10])).
% 3.10/1.01  
% 3.10/1.01  fof(f37,plain,(
% 3.10/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f22])).
% 3.10/1.01  
% 3.10/1.01  fof(f36,plain,(
% 3.10/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.10/1.01    inference(cnf_transformation,[],[f22])).
% 3.10/1.01  
% 3.10/1.01  fof(f12,conjecture,(
% 3.10/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f13,negated_conjecture,(
% 3.10/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.10/1.01    inference(negated_conjecture,[],[f12])).
% 3.10/1.01  
% 3.10/1.01  fof(f20,plain,(
% 3.10/1.01    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.10/1.01    inference(ennf_transformation,[],[f13])).
% 3.10/1.01  
% 3.10/1.01  fof(f21,plain,(
% 3.10/1.01    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.10/1.01    inference(flattening,[],[f20])).
% 3.10/1.01  
% 3.10/1.01  fof(f25,plain,(
% 3.10/1.01    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & (v2_tex_2(sK2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.10/1.01    introduced(choice_axiom,[])).
% 3.10/1.01  
% 3.10/1.01  fof(f24,plain,(
% 3.10/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.10/1.01    introduced(choice_axiom,[])).
% 3.10/1.01  
% 3.10/1.01  fof(f23,plain,(
% 3.10/1.01    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.10/1.01    introduced(choice_axiom,[])).
% 3.10/1.01  
% 3.10/1.01  fof(f26,plain,(
% 3.10/1.01    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.10/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24,f23])).
% 3.10/1.01  
% 3.10/1.01  fof(f42,plain,(
% 3.10/1.01    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 3.10/1.01    inference(cnf_transformation,[],[f26])).
% 3.10/1.01  
% 3.10/1.01  fof(f41,plain,(
% 3.10/1.01    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.10/1.01    inference(cnf_transformation,[],[f26])).
% 3.10/1.01  
% 3.10/1.01  fof(f11,axiom,(
% 3.10/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f18,plain,(
% 3.10/1.01    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.10/1.01    inference(ennf_transformation,[],[f11])).
% 3.10/1.01  
% 3.10/1.01  fof(f19,plain,(
% 3.10/1.01    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.10/1.01    inference(flattening,[],[f18])).
% 3.10/1.01  
% 3.10/1.01  fof(f38,plain,(
% 3.10/1.01    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f19])).
% 3.10/1.01  
% 3.10/1.01  fof(f39,plain,(
% 3.10/1.01    l1_pre_topc(sK0)),
% 3.10/1.01    inference(cnf_transformation,[],[f26])).
% 3.10/1.01  
% 3.10/1.01  fof(f1,axiom,(
% 3.10/1.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f14,plain,(
% 3.10/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.10/1.01    inference(ennf_transformation,[],[f1])).
% 3.10/1.01  
% 3.10/1.01  fof(f15,plain,(
% 3.10/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.10/1.01    inference(flattening,[],[f14])).
% 3.10/1.01  
% 3.10/1.01  fof(f27,plain,(
% 3.10/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f15])).
% 3.10/1.01  
% 3.10/1.01  fof(f43,plain,(
% 3.10/1.01    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 3.10/1.01    inference(cnf_transformation,[],[f26])).
% 3.10/1.01  
% 3.10/1.01  fof(f8,axiom,(
% 3.10/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f17,plain,(
% 3.10/1.01    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.10/1.01    inference(ennf_transformation,[],[f8])).
% 3.10/1.01  
% 3.10/1.01  fof(f34,plain,(
% 3.10/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.10/1.01    inference(cnf_transformation,[],[f17])).
% 3.10/1.01  
% 3.10/1.01  fof(f3,axiom,(
% 3.10/1.01    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f29,plain,(
% 3.10/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f3])).
% 3.10/1.01  
% 3.10/1.01  fof(f44,plain,(
% 3.10/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.10/1.01    inference(definition_unfolding,[],[f34,f29])).
% 3.10/1.01  
% 3.10/1.01  fof(f9,axiom,(
% 3.10/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f35,plain,(
% 3.10/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.10/1.01    inference(cnf_transformation,[],[f9])).
% 3.10/1.01  
% 3.10/1.01  fof(f4,axiom,(
% 3.10/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f30,plain,(
% 3.10/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f4])).
% 3.10/1.01  
% 3.10/1.01  fof(f45,plain,(
% 3.10/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.10/1.01    inference(definition_unfolding,[],[f35,f29,f30])).
% 3.10/1.01  
% 3.10/1.01  fof(f2,axiom,(
% 3.10/1.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f28,plain,(
% 3.10/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.10/1.01    inference(cnf_transformation,[],[f2])).
% 3.10/1.01  
% 3.10/1.01  fof(f40,plain,(
% 3.10/1.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.10/1.01    inference(cnf_transformation,[],[f26])).
% 3.10/1.01  
% 3.10/1.01  fof(f6,axiom,(
% 3.10/1.01    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f32,plain,(
% 3.10/1.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.10/1.01    inference(cnf_transformation,[],[f6])).
% 3.10/1.01  
% 3.10/1.01  fof(f5,axiom,(
% 3.10/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 3.10/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.01  
% 3.10/1.01  fof(f31,plain,(
% 3.10/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.10/1.01    inference(cnf_transformation,[],[f5])).
% 3.10/1.01  
% 3.10/1.01  cnf(c_4,plain,
% 3.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.10/1.01      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.10/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_7,plain,
% 3.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.10/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_101,plain,
% 3.10/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.10/1.01      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_102,plain,
% 3.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.10/1.01      inference(renaming,[status(thm)],[c_101]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_126,plain,
% 3.10/1.01      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 3.10/1.01      | ~ r1_tarski(X2,X0) ),
% 3.10/1.01      inference(bin_hyper_res,[status(thm)],[c_4,c_102]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_657,plain,
% 3.10/1.01      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 3.10/1.01      | r1_tarski(X2,X0) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_126]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_8,plain,
% 3.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.10/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_662,plain,
% 3.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.10/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1732,plain,
% 3.10/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.10/1.01      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_657,c_662]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_11,negated_conjecture,
% 3.10/1.01      ( v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0) ),
% 3.10/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_660,plain,
% 3.10/1.01      ( v2_tex_2(sK2,sK0) = iProver_top
% 3.10/1.01      | v2_tex_2(sK1,sK0) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_663,plain,
% 3.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.10/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_12,negated_conjecture,
% 3.10/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.10/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_659,plain,
% 3.10/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_9,plain,
% 3.10/1.01      ( ~ v2_tex_2(X0,X1)
% 3.10/1.01      | v2_tex_2(X2,X1)
% 3.10/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/1.01      | ~ r1_tarski(X2,X0)
% 3.10/1.01      | ~ l1_pre_topc(X1) ),
% 3.10/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_14,negated_conjecture,
% 3.10/1.01      ( l1_pre_topc(sK0) ),
% 3.10/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_185,plain,
% 3.10/1.01      ( ~ v2_tex_2(X0,X1)
% 3.10/1.01      | v2_tex_2(X2,X1)
% 3.10/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/1.01      | ~ r1_tarski(X2,X0)
% 3.10/1.01      | sK0 != X1 ),
% 3.10/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_186,plain,
% 3.10/1.01      ( ~ v2_tex_2(X0,sK0)
% 3.10/1.01      | v2_tex_2(X1,sK0)
% 3.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.10/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.10/1.01      | ~ r1_tarski(X1,X0) ),
% 3.10/1.01      inference(unflattening,[status(thm)],[c_185]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_655,plain,
% 3.10/1.01      ( v2_tex_2(X0,sK0) != iProver_top
% 3.10/1.01      | v2_tex_2(X1,sK0) = iProver_top
% 3.10/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.10/1.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.10/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_850,plain,
% 3.10/1.01      ( v2_tex_2(X0,sK0) = iProver_top
% 3.10/1.01      | v2_tex_2(sK2,sK0) != iProver_top
% 3.10/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.10/1.01      | r1_tarski(X0,sK2) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_659,c_655]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1813,plain,
% 3.10/1.01      ( v2_tex_2(X0,sK0) = iProver_top
% 3.10/1.01      | v2_tex_2(sK2,sK0) != iProver_top
% 3.10/1.01      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 3.10/1.01      | r1_tarski(X0,sK2) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_663,c_850]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_17,plain,
% 3.10/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_933,plain,
% 3.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.10/1.01      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1241,plain,
% 3.10/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.10/1.01      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_933]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1242,plain,
% 3.10/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.10/1.01      | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1241]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_0,plain,
% 3.10/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.10/1.01      inference(cnf_transformation,[],[f27]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_928,plain,
% 3.10/1.01      ( ~ r1_tarski(X0,X1)
% 3.10/1.01      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 3.10/1.01      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1577,plain,
% 3.10/1.01      ( r1_tarski(X0,u1_struct_0(sK0))
% 3.10/1.01      | ~ r1_tarski(X0,sK2)
% 3.10/1.01      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_928]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1578,plain,
% 3.10/1.01      ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 3.10/1.01      | r1_tarski(X0,sK2) != iProver_top
% 3.10/1.01      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1577]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3211,plain,
% 3.10/1.01      ( v2_tex_2(sK2,sK0) != iProver_top
% 3.10/1.01      | v2_tex_2(X0,sK0) = iProver_top
% 3.10/1.01      | r1_tarski(X0,sK2) != iProver_top ),
% 3.10/1.01      inference(global_propositional_subsumption,
% 3.10/1.01                [status(thm)],
% 3.10/1.01                [c_1813,c_17,c_1242,c_1578]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3212,plain,
% 3.10/1.01      ( v2_tex_2(X0,sK0) = iProver_top
% 3.10/1.01      | v2_tex_2(sK2,sK0) != iProver_top
% 3.10/1.01      | r1_tarski(X0,sK2) != iProver_top ),
% 3.10/1.01      inference(renaming,[status(thm)],[c_3211]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3220,plain,
% 3.10/1.01      ( v2_tex_2(X0,sK0) = iProver_top
% 3.10/1.01      | v2_tex_2(sK1,sK0) = iProver_top
% 3.10/1.01      | r1_tarski(X0,sK2) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_660,c_3212]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3660,plain,
% 3.10/1.01      ( v2_tex_2(k9_subset_1(sK2,X0,X1),sK0) = iProver_top
% 3.10/1.01      | v2_tex_2(sK1,sK0) = iProver_top
% 3.10/1.01      | r1_tarski(X1,sK2) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_1732,c_3220]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_10,negated_conjecture,
% 3.10/1.01      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 3.10/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_19,plain,
% 3.10/1.01      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1730,plain,
% 3.10/1.01      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_659,c_662]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_5,plain,
% 3.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.10/1.01      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.10/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_127,plain,
% 3.10/1.01      ( ~ r1_tarski(X0,X1)
% 3.10/1.01      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.10/1.01      inference(bin_hyper_res,[status(thm)],[c_5,c_102]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_656,plain,
% 3.10/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.10/1.01      | r1_tarski(X1,X2) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_127]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_6,plain,
% 3.10/1.01      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.10/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_698,plain,
% 3.10/1.01      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.10/1.01      | r1_tarski(X1,X2) != iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_656,c_6]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2096,plain,
% 3.10/1.01      ( k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_1730,c_698]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1,plain,
% 3.10/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.10/1.01      inference(cnf_transformation,[],[f28]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_665,plain,
% 3.10/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1333,plain,
% 3.10/1.01      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_6,c_665]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2238,plain,
% 3.10/1.01      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,sK2),X0) = iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_2096,c_1333]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_13,negated_conjecture,
% 3.10/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.10/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_658,plain,
% 3.10/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_851,plain,
% 3.10/1.01      ( v2_tex_2(X0,sK0) = iProver_top
% 3.10/1.01      | v2_tex_2(sK1,sK0) != iProver_top
% 3.10/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.10/1.01      | r1_tarski(X0,sK1) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_658,c_655]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1036,plain,
% 3.10/1.01      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0,X1),sK0) = iProver_top
% 3.10/1.01      | v2_tex_2(sK1,sK0) != iProver_top
% 3.10/1.01      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
% 3.10/1.01      | r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,X1),sK1) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_657,c_851]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3770,plain,
% 3.10/1.01      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
% 3.10/1.01      | v2_tex_2(sK1,sK0) != iProver_top
% 3.10/1.01      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_2238,c_1036]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_5899,plain,
% 3.10/1.01      ( v2_tex_2(k9_subset_1(sK2,X0,X1),sK0) = iProver_top
% 3.10/1.01      | r1_tarski(X1,sK2) != iProver_top ),
% 3.10/1.01      inference(global_propositional_subsumption,
% 3.10/1.01                [status(thm)],
% 3.10/1.01                [c_3660,c_17,c_19,c_1242,c_3770]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3,plain,
% 3.10/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.10/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_664,plain,
% 3.10/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2,plain,
% 3.10/1.01      ( k2_subset_1(X0) = X0 ),
% 3.10/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_673,plain,
% 3.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.10/1.01      inference(light_normalisation,[status(thm)],[c_664,c_2]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1733,plain,
% 3.10/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_673,c_662]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3070,plain,
% 3.10/1.01      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_1733,c_698]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_661,plain,
% 3.10/1.01      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2235,plain,
% 3.10/1.01      ( v2_tex_2(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK0) != iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_2096,c_661]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_4049,plain,
% 3.10/1.01      ( v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
% 3.10/1.01      inference(demodulation,[status(thm)],[c_3070,c_2235]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_5907,plain,
% 3.10/1.01      ( r1_tarski(sK2,sK2) != iProver_top ),
% 3.10/1.01      inference(superposition,[status(thm)],[c_5899,c_4049]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_329,plain,
% 3.10/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.10/1.01      theory(equality) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_978,plain,
% 3.10/1.01      ( ~ r1_tarski(X0,sK2) | r1_tarski(X1,sK2) | X1 != X0 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_329]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1640,plain,
% 3.10/1.01      ( r1_tarski(X0,sK2)
% 3.10/1.01      | ~ r1_tarski(k2_subset_1(sK2),sK2)
% 3.10/1.01      | X0 != k2_subset_1(sK2) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_978]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3083,plain,
% 3.10/1.01      ( ~ r1_tarski(k2_subset_1(sK2),sK2)
% 3.10/1.01      | r1_tarski(sK2,sK2)
% 3.10/1.01      | sK2 != k2_subset_1(sK2) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_1640]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_3084,plain,
% 3.10/1.01      ( sK2 != k2_subset_1(sK2)
% 3.10/1.01      | r1_tarski(k2_subset_1(sK2),sK2) != iProver_top
% 3.10/1.01      | r1_tarski(sK2,sK2) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_3083]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_328,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1010,plain,
% 3.10/1.01      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_328]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1426,plain,
% 3.10/1.01      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_1010]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_2048,plain,
% 3.10/1.01      ( k2_subset_1(sK2) != sK2 | sK2 = k2_subset_1(sK2) | sK2 != sK2 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_1426]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1262,plain,
% 3.10/1.01      ( m1_subset_1(k2_subset_1(sK2),k1_zfmisc_1(sK2)) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1265,plain,
% 3.10/1.01      ( m1_subset_1(k2_subset_1(sK2),k1_zfmisc_1(sK2)) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1262]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_984,plain,
% 3.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | r1_tarski(X0,sK2) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1261,plain,
% 3.10/1.01      ( ~ m1_subset_1(k2_subset_1(sK2),k1_zfmisc_1(sK2))
% 3.10/1.01      | r1_tarski(k2_subset_1(sK2),sK2) ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_984]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_1263,plain,
% 3.10/1.01      ( m1_subset_1(k2_subset_1(sK2),k1_zfmisc_1(sK2)) != iProver_top
% 3.10/1.01      | r1_tarski(k2_subset_1(sK2),sK2) = iProver_top ),
% 3.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1261]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_327,plain,( X0 = X0 ),theory(equality) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_814,plain,
% 3.10/1.01      ( sK2 = sK2 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_327]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(c_808,plain,
% 3.10/1.01      ( k2_subset_1(sK2) = sK2 ),
% 3.10/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.10/1.01  
% 3.10/1.01  cnf(contradiction,plain,
% 3.10/1.01      ( $false ),
% 3.10/1.01      inference(minisat,
% 3.10/1.01                [status(thm)],
% 3.10/1.01                [c_5907,c_3084,c_2048,c_1265,c_1263,c_814,c_808]) ).
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/1.01  
% 3.10/1.01  ------                               Statistics
% 3.10/1.01  
% 3.10/1.01  ------ General
% 3.10/1.01  
% 3.10/1.01  abstr_ref_over_cycles:                  0
% 3.10/1.01  abstr_ref_under_cycles:                 0
% 3.10/1.01  gc_basic_clause_elim:                   0
% 3.10/1.01  forced_gc_time:                         0
% 3.10/1.01  parsing_time:                           0.011
% 3.10/1.01  unif_index_cands_time:                  0.
% 3.10/1.01  unif_index_add_time:                    0.
% 3.10/1.01  orderings_time:                         0.
% 3.10/1.01  out_proof_time:                         0.008
% 3.10/1.01  total_time:                             0.217
% 3.10/1.01  num_of_symbols:                         45
% 3.10/1.01  num_of_terms:                           5556
% 3.10/1.01  
% 3.10/1.01  ------ Preprocessing
% 3.10/1.01  
% 3.10/1.01  num_of_splits:                          0
% 3.10/1.01  num_of_split_atoms:                     0
% 3.10/1.01  num_of_reused_defs:                     0
% 3.10/1.01  num_eq_ax_congr_red:                    18
% 3.10/1.01  num_of_sem_filtered_clauses:            1
% 3.10/1.01  num_of_subtypes:                        0
% 3.10/1.01  monotx_restored_types:                  0
% 3.10/1.01  sat_num_of_epr_types:                   0
% 3.10/1.01  sat_num_of_non_cyclic_types:            0
% 3.10/1.01  sat_guarded_non_collapsed_types:        0
% 3.10/1.01  num_pure_diseq_elim:                    0
% 3.10/1.01  simp_replaced_by:                       0
% 3.10/1.01  res_preprocessed:                       78
% 3.10/1.01  prep_upred:                             0
% 3.10/1.01  prep_unflattend:                        1
% 3.10/1.01  smt_new_axioms:                         0
% 3.10/1.01  pred_elim_cands:                        3
% 3.10/1.01  pred_elim:                              1
% 3.10/1.01  pred_elim_cl:                           1
% 3.10/1.01  pred_elim_cycles:                       3
% 3.10/1.01  merged_defs:                            8
% 3.10/1.01  merged_defs_ncl:                        0
% 3.10/1.01  bin_hyper_res:                          10
% 3.10/1.01  prep_cycles:                            4
% 3.10/1.01  pred_elim_time:                         0.001
% 3.10/1.01  splitting_time:                         0.
% 3.10/1.01  sem_filter_time:                        0.
% 3.10/1.01  monotx_time:                            0.001
% 3.10/1.01  subtype_inf_time:                       0.
% 3.10/1.01  
% 3.10/1.01  ------ Problem properties
% 3.10/1.01  
% 3.10/1.01  clauses:                                14
% 3.10/1.01  conjectures:                            4
% 3.10/1.01  epr:                                    2
% 3.10/1.01  horn:                                   13
% 3.10/1.01  ground:                                 4
% 3.10/1.01  unary:                                  7
% 3.10/1.01  binary:                                 5
% 3.10/1.01  lits:                                   25
% 3.10/1.01  lits_eq:                                3
% 3.10/1.01  fd_pure:                                0
% 3.10/1.01  fd_pseudo:                              0
% 3.10/1.01  fd_cond:                                0
% 3.10/1.01  fd_pseudo_cond:                         0
% 3.10/1.01  ac_symbols:                             0
% 3.10/1.01  
% 3.10/1.01  ------ Propositional Solver
% 3.10/1.01  
% 3.10/1.01  prop_solver_calls:                      30
% 3.10/1.01  prop_fast_solver_calls:                 539
% 3.10/1.01  smt_solver_calls:                       0
% 3.10/1.01  smt_fast_solver_calls:                  0
% 3.10/1.01  prop_num_of_clauses:                    2612
% 3.10/1.01  prop_preprocess_simplified:             4734
% 3.10/1.01  prop_fo_subsumed:                       29
% 3.10/1.01  prop_solver_time:                       0.
% 3.10/1.01  smt_solver_time:                        0.
% 3.10/1.01  smt_fast_solver_time:                   0.
% 3.10/1.01  prop_fast_solver_time:                  0.
% 3.10/1.01  prop_unsat_core_time:                   0.
% 3.10/1.01  
% 3.10/1.01  ------ QBF
% 3.10/1.01  
% 3.10/1.01  qbf_q_res:                              0
% 3.10/1.01  qbf_num_tautologies:                    0
% 3.10/1.01  qbf_prep_cycles:                        0
% 3.10/1.01  
% 3.10/1.01  ------ BMC1
% 3.10/1.01  
% 3.10/1.01  bmc1_current_bound:                     -1
% 3.10/1.01  bmc1_last_solved_bound:                 -1
% 3.10/1.01  bmc1_unsat_core_size:                   -1
% 3.10/1.01  bmc1_unsat_core_parents_size:           -1
% 3.10/1.01  bmc1_merge_next_fun:                    0
% 3.10/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.10/1.01  
% 3.10/1.01  ------ Instantiation
% 3.10/1.01  
% 3.10/1.01  inst_num_of_clauses:                    658
% 3.10/1.01  inst_num_in_passive:                    111
% 3.10/1.01  inst_num_in_active:                     335
% 3.10/1.01  inst_num_in_unprocessed:                212
% 3.10/1.01  inst_num_of_loops:                      370
% 3.10/1.01  inst_num_of_learning_restarts:          0
% 3.10/1.01  inst_num_moves_active_passive:          30
% 3.10/1.01  inst_lit_activity:                      0
% 3.10/1.01  inst_lit_activity_moves:                0
% 3.10/1.01  inst_num_tautologies:                   0
% 3.10/1.01  inst_num_prop_implied:                  0
% 3.10/1.01  inst_num_existing_simplified:           0
% 3.10/1.01  inst_num_eq_res_simplified:             0
% 3.10/1.01  inst_num_child_elim:                    0
% 3.10/1.01  inst_num_of_dismatching_blockings:      161
% 3.10/1.01  inst_num_of_non_proper_insts:           731
% 3.10/1.01  inst_num_of_duplicates:                 0
% 3.10/1.01  inst_inst_num_from_inst_to_res:         0
% 3.10/1.01  inst_dismatching_checking_time:         0.
% 3.10/1.01  
% 3.10/1.01  ------ Resolution
% 3.10/1.01  
% 3.10/1.01  res_num_of_clauses:                     0
% 3.10/1.01  res_num_in_passive:                     0
% 3.10/1.01  res_num_in_active:                      0
% 3.10/1.01  res_num_of_loops:                       82
% 3.10/1.01  res_forward_subset_subsumed:            33
% 3.10/1.01  res_backward_subset_subsumed:           4
% 3.10/1.01  res_forward_subsumed:                   0
% 3.10/1.01  res_backward_subsumed:                  0
% 3.10/1.01  res_forward_subsumption_resolution:     0
% 3.10/1.01  res_backward_subsumption_resolution:    0
% 3.10/1.01  res_clause_to_clause_subsumption:       475
% 3.10/1.01  res_orphan_elimination:                 0
% 3.10/1.01  res_tautology_del:                      84
% 3.10/1.01  res_num_eq_res_simplified:              0
% 3.10/1.01  res_num_sel_changes:                    0
% 3.10/1.01  res_moves_from_active_to_pass:          0
% 3.10/1.01  
% 3.10/1.01  ------ Superposition
% 3.10/1.01  
% 3.10/1.01  sup_time_total:                         0.
% 3.10/1.01  sup_time_generating:                    0.
% 3.10/1.01  sup_time_sim_full:                      0.
% 3.10/1.01  sup_time_sim_immed:                     0.
% 3.10/1.01  
% 3.10/1.01  sup_num_of_clauses:                     150
% 3.10/1.01  sup_num_in_active:                      61
% 3.10/1.01  sup_num_in_passive:                     89
% 3.10/1.01  sup_num_of_loops:                       72
% 3.10/1.01  sup_fw_superposition:                   88
% 3.10/1.01  sup_bw_superposition:                   122
% 3.10/1.01  sup_immediate_simplified:               39
% 3.10/1.01  sup_given_eliminated:                   0
% 3.10/1.01  comparisons_done:                       0
% 3.10/1.01  comparisons_avoided:                    0
% 3.10/1.01  
% 3.10/1.01  ------ Simplifications
% 3.10/1.01  
% 3.10/1.01  
% 3.10/1.01  sim_fw_subset_subsumed:                 8
% 3.10/1.01  sim_bw_subset_subsumed:                 12
% 3.10/1.01  sim_fw_subsumed:                        10
% 3.10/1.01  sim_bw_subsumed:                        7
% 3.10/1.01  sim_fw_subsumption_res:                 0
% 3.10/1.01  sim_bw_subsumption_res:                 0
% 3.10/1.01  sim_tautology_del:                      7
% 3.10/1.01  sim_eq_tautology_del:                   2
% 3.10/1.01  sim_eq_res_simp:                        0
% 3.10/1.01  sim_fw_demodulated:                     11
% 3.10/1.01  sim_bw_demodulated:                     7
% 3.10/1.01  sim_light_normalised:                   5
% 3.10/1.01  sim_joinable_taut:                      0
% 3.10/1.01  sim_joinable_simp:                      0
% 3.10/1.01  sim_ac_normalised:                      0
% 3.10/1.01  sim_smt_subsumption:                    0
% 3.10/1.01  
%------------------------------------------------------------------------------
