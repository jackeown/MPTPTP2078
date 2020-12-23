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
% DateTime   : Thu Dec  3 12:25:49 EST 2020

% Result     : Theorem 11.69s
% Output     : CNFRefutation 11.69s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 746 expanded)
%              Number of clauses        :   80 ( 244 expanded)
%              Number of leaves         :   15 ( 197 expanded)
%              Depth                    :   21
%              Number of atoms          :  324 (2119 expanded)
%              Number of equality atoms :  137 ( 500 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f63,f52,f53])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f42,f41,f40])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f21,axiom,(
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

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f59,f52])).

fof(f71,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f44,f52,f52])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_894,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1697,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_894])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_895,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3783,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_895])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_886,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_891,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_889,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3610,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_891,c_889])).

cnf(c_11700,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_886,c_3610])).

cnf(c_5104,plain,
    ( v2_tex_2(X0,sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_20,c_23])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5451,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK2,sK0)
    | v2_tex_2(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5104,c_25])).

cnf(c_5452,plain,
    ( v2_tex_2(X0,sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2) ),
    inference(renaming,[status(thm)],[c_5451])).

cnf(c_5723,plain,
    ( v2_tex_2(X0,sK0)
    | ~ v2_tex_2(sK2,sK0)
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_5452,c_18])).

cnf(c_5724,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5723])).

cnf(c_13066,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | v2_tex_2(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11700,c_5724])).

cnf(c_13067,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_13066])).

cnf(c_13082,plain,
    ( v2_tex_2(k1_setfam_1(k1_enumset1(X0,X0,X1)),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3783,c_13067])).

cnf(c_16726,plain,
    ( v2_tex_2(k1_setfam_1(k1_enumset1(sK2,sK2,X0)),sK0) = iProver_top
    | v2_tex_2(sK2,sK0) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1697,c_13082])).

cnf(c_22,negated_conjecture,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,plain,
    ( v2_tex_2(sK2,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1117,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_19,c_23])).

cnf(c_1118,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1117])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_896,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_150,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_151,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_150])).

cnf(c_190,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_151])).

cnf(c_880,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_953,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_880,c_17])).

cnf(c_4627,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_896,c_953])).

cnf(c_890,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3409,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_886,c_890])).

cnf(c_4631,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(superposition,[status(thm)],[c_3409,c_953])).

cnf(c_4660,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
    inference(demodulation,[status(thm)],[c_4627,c_4631])).

cnf(c_21,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_888,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5703,plain,
    ( v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4660,c_888])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4628,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) = k9_subset_1(X3,X0,k4_xboole_0(X1,X2))
    | r1_tarski(X1,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_895,c_953])).

cnf(c_18325,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(sK2,X1))) = k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_3409,c_4628])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1553,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_17,c_0])).

cnf(c_20474,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(k4_xboole_0(sK2,X0),X1)) = k9_subset_1(u1_struct_0(sK0),X1,k4_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_18325,c_1553])).

cnf(c_4629,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) = k9_subset_1(X1,X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_894,c_953])).

cnf(c_23095,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(sK2,X1)) = k9_subset_1(sK2,X0,k4_xboole_0(sK2,X1)) ),
    inference(demodulation,[status(thm)],[c_4629,c_18325])).

cnf(c_26964,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(k4_xboole_0(sK2,X0),X1)) = k9_subset_1(sK2,X1,k4_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_20474,c_17,c_23095])).

cnf(c_27008,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,X1))) = k9_subset_1(sK2,X0,k4_xboole_0(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_26964,c_0])).

cnf(c_37802,plain,
    ( k9_subset_1(sK2,X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1,c_27008])).

cnf(c_38040,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k9_subset_1(sK2,X0,sK2) ),
    inference(demodulation,[status(thm)],[c_37802,c_1,c_17])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_885,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11701,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_885,c_3610])).

cnf(c_5108,plain,
    ( v2_tex_2(X0,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_20,c_24])).

cnf(c_6075,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_tex_2(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5108,c_25])).

cnf(c_6076,plain,
    ( v2_tex_2(X0,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1) ),
    inference(renaming,[status(thm)],[c_6075])).

cnf(c_6103,plain,
    ( v2_tex_2(X0,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1) ),
    inference(resolution,[status(thm)],[c_6076,c_18])).

cnf(c_6104,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6103])).

cnf(c_13151,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | v2_tex_2(X0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11701,c_6104])).

cnf(c_13152,plain,
    ( v2_tex_2(X0,sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_13151])).

cnf(c_13160,plain,
    ( v2_tex_2(k4_xboole_0(X0,X1),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_895,c_13152])).

cnf(c_16157,plain,
    ( v2_tex_2(k4_xboole_0(sK1,X0),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_894,c_13160])).

cnf(c_1119,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_19,c_24])).

cnf(c_1120,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1119])).

cnf(c_33303,plain,
    ( v2_tex_2(sK1,sK0) != iProver_top
    | v2_tex_2(k4_xboole_0(sK1,X0),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16157,c_1120])).

cnf(c_33304,plain,
    ( v2_tex_2(k4_xboole_0(sK1,X0),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_33303])).

cnf(c_38394,plain,
    ( v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) = iProver_top
    | v2_tex_2(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38040,c_33304])).

cnf(c_38860,plain,
    ( v2_tex_2(k1_setfam_1(k1_enumset1(sK2,sK2,X0)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16726,c_29,c_1118,c_5703,c_38394])).

cnf(c_26995,plain,
    ( k9_subset_1(sK2,X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_26964])).

cnf(c_27085,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,X0)) = k9_subset_1(sK2,X0,sK2) ),
    inference(demodulation,[status(thm)],[c_26995,c_1,c_17])).

cnf(c_38866,plain,
    ( v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38860,c_27085])).

cnf(c_38873,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_38866,c_5703])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:31:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.69/2.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.69/2.02  
% 11.69/2.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.69/2.02  
% 11.69/2.02  ------  iProver source info
% 11.69/2.02  
% 11.69/2.02  git: date: 2020-06-30 10:37:57 +0100
% 11.69/2.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.69/2.02  git: non_committed_changes: false
% 11.69/2.02  git: last_make_outside_of_git: false
% 11.69/2.02  
% 11.69/2.02  ------ 
% 11.69/2.02  ------ Parsing...
% 11.69/2.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.69/2.02  
% 11.69/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.69/2.02  
% 11.69/2.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.69/2.02  
% 11.69/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.69/2.02  ------ Proving...
% 11.69/2.02  ------ Problem Properties 
% 11.69/2.02  
% 11.69/2.02  
% 11.69/2.02  clauses                                 25
% 11.69/2.02  conjectures                             5
% 11.69/2.02  EPR                                     4
% 11.69/2.02  Horn                                    24
% 11.69/2.02  unary                                   13
% 11.69/2.02  binary                                  8
% 11.69/2.02  lits                                    44
% 11.69/2.02  lits eq                                 10
% 11.69/2.02  fd_pure                                 0
% 11.69/2.02  fd_pseudo                               0
% 11.69/2.02  fd_cond                                 0
% 11.69/2.02  fd_pseudo_cond                          1
% 11.69/2.02  AC symbols                              0
% 11.69/2.02  
% 11.69/2.02  ------ Input Options Time Limit: Unbounded
% 11.69/2.02  
% 11.69/2.02  
% 11.69/2.02  ------ 
% 11.69/2.02  Current options:
% 11.69/2.02  ------ 
% 11.69/2.02  
% 11.69/2.02  
% 11.69/2.02  
% 11.69/2.02  
% 11.69/2.02  ------ Proving...
% 11.69/2.02  
% 11.69/2.02  
% 11.69/2.02  % SZS status Theorem for theBenchmark.p
% 11.69/2.02  
% 11.69/2.02   Resolution empty clause
% 11.69/2.02  
% 11.69/2.02  % SZS output start CNFRefutation for theBenchmark.p
% 11.69/2.02  
% 11.69/2.02  fof(f18,axiom,(
% 11.69/2.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.69/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.02  
% 11.69/2.02  fof(f63,plain,(
% 11.69/2.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.69/2.02    inference(cnf_transformation,[],[f18])).
% 11.69/2.02  
% 11.69/2.02  fof(f7,axiom,(
% 11.69/2.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.69/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.02  
% 11.69/2.02  fof(f52,plain,(
% 11.69/2.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.69/2.02    inference(cnf_transformation,[],[f7])).
% 11.69/2.02  
% 11.69/2.02  fof(f8,axiom,(
% 11.69/2.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.69/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.02  
% 11.69/2.02  fof(f53,plain,(
% 11.69/2.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.69/2.02    inference(cnf_transformation,[],[f8])).
% 11.69/2.02  
% 11.69/2.02  fof(f76,plain,(
% 11.69/2.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 11.69/2.02    inference(definition_unfolding,[],[f63,f52,f53])).
% 11.69/2.02  
% 11.69/2.02  fof(f6,axiom,(
% 11.69/2.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.69/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.02  
% 11.69/2.02  fof(f51,plain,(
% 11.69/2.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.69/2.02    inference(cnf_transformation,[],[f6])).
% 11.69/2.02  
% 11.69/2.02  fof(f4,axiom,(
% 11.69/2.02    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 11.69/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.02  
% 11.69/2.02  fof(f26,plain,(
% 11.69/2.02    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 11.69/2.02    inference(ennf_transformation,[],[f4])).
% 11.69/2.02  
% 11.69/2.02  fof(f49,plain,(
% 11.69/2.02    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 11.69/2.02    inference(cnf_transformation,[],[f26])).
% 11.69/2.02  
% 11.69/2.02  fof(f22,conjecture,(
% 11.69/2.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 11.69/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.02  
% 11.69/2.02  fof(f23,negated_conjecture,(
% 11.69/2.02    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 11.69/2.02    inference(negated_conjecture,[],[f22])).
% 11.69/2.02  
% 11.69/2.02  fof(f35,plain,(
% 11.69/2.02    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.69/2.02    inference(ennf_transformation,[],[f23])).
% 11.69/2.02  
% 11.69/2.02  fof(f36,plain,(
% 11.69/2.02    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.69/2.02    inference(flattening,[],[f35])).
% 11.69/2.02  
% 11.69/2.02  fof(f42,plain,(
% 11.69/2.02    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & (v2_tex_2(sK2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.69/2.02    introduced(choice_axiom,[])).
% 11.69/2.02  
% 11.69/2.02  fof(f41,plain,(
% 11.69/2.02    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.69/2.02    introduced(choice_axiom,[])).
% 11.69/2.02  
% 11.69/2.02  fof(f40,plain,(
% 11.69/2.02    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 11.69/2.02    introduced(choice_axiom,[])).
% 11.69/2.02  
% 11.69/2.02  fof(f43,plain,(
% 11.69/2.02    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 11.69/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f42,f41,f40])).
% 11.69/2.02  
% 11.69/2.02  fof(f69,plain,(
% 11.69/2.02    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.69/2.02    inference(cnf_transformation,[],[f43])).
% 11.69/2.02  
% 11.69/2.02  fof(f19,axiom,(
% 11.69/2.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.69/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.02  
% 11.69/2.02  fof(f39,plain,(
% 11.69/2.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.69/2.02    inference(nnf_transformation,[],[f19])).
% 11.69/2.02  
% 11.69/2.02  fof(f65,plain,(
% 11.69/2.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.69/2.02    inference(cnf_transformation,[],[f39])).
% 11.69/2.02  
% 11.69/2.02  fof(f21,axiom,(
% 11.69/2.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 11.69/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.02  
% 11.69/2.02  fof(f33,plain,(
% 11.69/2.02    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.69/2.02    inference(ennf_transformation,[],[f21])).
% 11.69/2.02  
% 11.69/2.02  fof(f34,plain,(
% 11.69/2.02    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.69/2.02    inference(flattening,[],[f33])).
% 11.69/2.02  
% 11.69/2.02  fof(f66,plain,(
% 11.69/2.02    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.69/2.02    inference(cnf_transformation,[],[f34])).
% 11.69/2.02  
% 11.69/2.02  fof(f67,plain,(
% 11.69/2.02    l1_pre_topc(sK0)),
% 11.69/2.02    inference(cnf_transformation,[],[f43])).
% 11.69/2.02  
% 11.69/2.02  fof(f70,plain,(
% 11.69/2.02    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 11.69/2.02    inference(cnf_transformation,[],[f43])).
% 11.69/2.02  
% 11.69/2.02  fof(f64,plain,(
% 11.69/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.69/2.02    inference(cnf_transformation,[],[f39])).
% 11.69/2.02  
% 11.69/2.02  fof(f3,axiom,(
% 11.69/2.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.69/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.02  
% 11.69/2.02  fof(f37,plain,(
% 11.69/2.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.69/2.02    inference(nnf_transformation,[],[f3])).
% 11.69/2.02  
% 11.69/2.02  fof(f38,plain,(
% 11.69/2.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.69/2.02    inference(flattening,[],[f37])).
% 11.69/2.02  
% 11.69/2.02  fof(f46,plain,(
% 11.69/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.69/2.02    inference(cnf_transformation,[],[f38])).
% 11.69/2.02  
% 11.69/2.02  fof(f78,plain,(
% 11.69/2.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.69/2.02    inference(equality_resolution,[],[f46])).
% 11.69/2.02  
% 11.69/2.02  fof(f14,axiom,(
% 11.69/2.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 11.69/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.02  
% 11.69/2.02  fof(f30,plain,(
% 11.69/2.02    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.69/2.02    inference(ennf_transformation,[],[f14])).
% 11.69/2.02  
% 11.69/2.02  fof(f59,plain,(
% 11.69/2.02    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.69/2.02    inference(cnf_transformation,[],[f30])).
% 11.69/2.02  
% 11.69/2.02  fof(f75,plain,(
% 11.69/2.02    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.69/2.02    inference(definition_unfolding,[],[f59,f52])).
% 11.69/2.02  
% 11.69/2.02  fof(f71,plain,(
% 11.69/2.02    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 11.69/2.02    inference(cnf_transformation,[],[f43])).
% 11.69/2.02  
% 11.69/2.02  fof(f2,axiom,(
% 11.69/2.02    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.69/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.02  
% 11.69/2.02  fof(f24,plain,(
% 11.69/2.02    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.69/2.02    inference(rectify,[],[f2])).
% 11.69/2.02  
% 11.69/2.02  fof(f45,plain,(
% 11.69/2.02    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.69/2.02    inference(cnf_transformation,[],[f24])).
% 11.69/2.02  
% 11.69/2.02  fof(f73,plain,(
% 11.69/2.02    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 11.69/2.02    inference(definition_unfolding,[],[f45,f52])).
% 11.69/2.02  
% 11.69/2.02  fof(f1,axiom,(
% 11.69/2.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.69/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.69/2.02  
% 11.69/2.02  fof(f44,plain,(
% 11.69/2.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.69/2.02    inference(cnf_transformation,[],[f1])).
% 11.69/2.02  
% 11.69/2.02  fof(f72,plain,(
% 11.69/2.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.69/2.02    inference(definition_unfolding,[],[f44,f52,f52])).
% 11.69/2.02  
% 11.69/2.02  fof(f68,plain,(
% 11.69/2.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.69/2.02    inference(cnf_transformation,[],[f43])).
% 11.69/2.02  
% 11.69/2.02  cnf(c_17,plain,
% 11.69/2.02      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.69/2.02      inference(cnf_transformation,[],[f76]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_7,plain,
% 11.69/2.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.69/2.02      inference(cnf_transformation,[],[f51]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_894,plain,
% 11.69/2.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_1697,plain,
% 11.69/2.02      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_17,c_894]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_5,plain,
% 11.69/2.02      ( ~ r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1) ),
% 11.69/2.02      inference(cnf_transformation,[],[f49]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_895,plain,
% 11.69/2.02      ( r1_tarski(X0,X1) != iProver_top
% 11.69/2.02      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_3783,plain,
% 11.69/2.02      ( r1_tarski(X0,X1) != iProver_top
% 11.69/2.02      | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_17,c_895]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_23,negated_conjecture,
% 11.69/2.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.69/2.02      inference(cnf_transformation,[],[f69]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_886,plain,
% 11.69/2.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_18,plain,
% 11.69/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.69/2.02      inference(cnf_transformation,[],[f65]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_891,plain,
% 11.69/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.69/2.02      | r1_tarski(X0,X1) != iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_20,plain,
% 11.69/2.02      ( ~ v2_tex_2(X0,X1)
% 11.69/2.02      | v2_tex_2(X2,X1)
% 11.69/2.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.69/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.69/2.02      | ~ r1_tarski(X2,X0)
% 11.69/2.02      | ~ l1_pre_topc(X1) ),
% 11.69/2.02      inference(cnf_transformation,[],[f66]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_889,plain,
% 11.69/2.02      ( v2_tex_2(X0,X1) != iProver_top
% 11.69/2.02      | v2_tex_2(X2,X1) = iProver_top
% 11.69/2.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.69/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.69/2.02      | r1_tarski(X2,X0) != iProver_top
% 11.69/2.02      | l1_pre_topc(X1) != iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_3610,plain,
% 11.69/2.02      ( v2_tex_2(X0,X1) != iProver_top
% 11.69/2.02      | v2_tex_2(X2,X1) = iProver_top
% 11.69/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.69/2.02      | r1_tarski(X2,X0) != iProver_top
% 11.69/2.02      | r1_tarski(X2,u1_struct_0(X1)) != iProver_top
% 11.69/2.02      | l1_pre_topc(X1) != iProver_top ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_891,c_889]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_11700,plain,
% 11.69/2.02      ( v2_tex_2(X0,sK0) = iProver_top
% 11.69/2.02      | v2_tex_2(sK2,sK0) != iProver_top
% 11.69/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.69/2.02      | r1_tarski(X0,sK2) != iProver_top
% 11.69/2.02      | l1_pre_topc(sK0) != iProver_top ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_886,c_3610]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_5104,plain,
% 11.69/2.02      ( v2_tex_2(X0,sK0)
% 11.69/2.02      | ~ v2_tex_2(sK2,sK0)
% 11.69/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.69/2.02      | ~ r1_tarski(X0,sK2)
% 11.69/2.02      | ~ l1_pre_topc(sK0) ),
% 11.69/2.02      inference(resolution,[status(thm)],[c_20,c_23]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_25,negated_conjecture,
% 11.69/2.02      ( l1_pre_topc(sK0) ),
% 11.69/2.02      inference(cnf_transformation,[],[f67]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_5451,plain,
% 11.69/2.02      ( ~ r1_tarski(X0,sK2)
% 11.69/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.69/2.02      | ~ v2_tex_2(sK2,sK0)
% 11.69/2.02      | v2_tex_2(X0,sK0) ),
% 11.69/2.02      inference(global_propositional_subsumption,[status(thm)],[c_5104,c_25]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_5452,plain,
% 11.69/2.02      ( v2_tex_2(X0,sK0)
% 11.69/2.02      | ~ v2_tex_2(sK2,sK0)
% 11.69/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.69/2.02      | ~ r1_tarski(X0,sK2) ),
% 11.69/2.02      inference(renaming,[status(thm)],[c_5451]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_5723,plain,
% 11.69/2.02      ( v2_tex_2(X0,sK0)
% 11.69/2.02      | ~ v2_tex_2(sK2,sK0)
% 11.69/2.02      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 11.69/2.02      | ~ r1_tarski(X0,sK2) ),
% 11.69/2.02      inference(resolution,[status(thm)],[c_5452,c_18]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_5724,plain,
% 11.69/2.02      ( v2_tex_2(X0,sK0) = iProver_top
% 11.69/2.02      | v2_tex_2(sK2,sK0) != iProver_top
% 11.69/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.69/2.02      | r1_tarski(X0,sK2) != iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_5723]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_13066,plain,
% 11.69/2.02      ( r1_tarski(X0,sK2) != iProver_top
% 11.69/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.69/2.02      | v2_tex_2(sK2,sK0) != iProver_top
% 11.69/2.02      | v2_tex_2(X0,sK0) = iProver_top ),
% 11.69/2.02      inference(global_propositional_subsumption,
% 11.69/2.02                [status(thm)],
% 11.69/2.02                [c_11700,c_5724]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_13067,plain,
% 11.69/2.02      ( v2_tex_2(X0,sK0) = iProver_top
% 11.69/2.02      | v2_tex_2(sK2,sK0) != iProver_top
% 11.69/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.69/2.02      | r1_tarski(X0,sK2) != iProver_top ),
% 11.69/2.02      inference(renaming,[status(thm)],[c_13066]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_13082,plain,
% 11.69/2.02      ( v2_tex_2(k1_setfam_1(k1_enumset1(X0,X0,X1)),sK0) = iProver_top
% 11.69/2.02      | v2_tex_2(sK2,sK0) != iProver_top
% 11.69/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.69/2.02      | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),sK2) != iProver_top ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_3783,c_13067]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_16726,plain,
% 11.69/2.02      ( v2_tex_2(k1_setfam_1(k1_enumset1(sK2,sK2,X0)),sK0) = iProver_top
% 11.69/2.02      | v2_tex_2(sK2,sK0) != iProver_top
% 11.69/2.02      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_1697,c_13082]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_22,negated_conjecture,
% 11.69/2.02      ( v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0) ),
% 11.69/2.02      inference(cnf_transformation,[],[f70]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_29,plain,
% 11.69/2.02      ( v2_tex_2(sK2,sK0) = iProver_top | v2_tex_2(sK1,sK0) = iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_19,plain,
% 11.69/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.69/2.02      inference(cnf_transformation,[],[f64]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_1117,plain,
% 11.69/2.02      ( r1_tarski(sK2,u1_struct_0(sK0)) ),
% 11.69/2.02      inference(resolution,[status(thm)],[c_19,c_23]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_1118,plain,
% 11.69/2.02      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_1117]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f78]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_896,plain,
% 11.69/2.02      ( r1_tarski(X0,X0) = iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_13,plain,
% 11.69/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.69/2.02      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 11.69/2.02      inference(cnf_transformation,[],[f75]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_150,plain,
% 11.69/2.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.69/2.02      inference(prop_impl,[status(thm)],[c_18]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_151,plain,
% 11.69/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.69/2.02      inference(renaming,[status(thm)],[c_150]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_190,plain,
% 11.69/2.02      ( ~ r1_tarski(X0,X1)
% 11.69/2.02      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 11.69/2.02      inference(bin_hyper_res,[status(thm)],[c_13,c_151]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_880,plain,
% 11.69/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 11.69/2.02      | r1_tarski(X1,X2) != iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_953,plain,
% 11.69/2.02      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 11.69/2.02      | r1_tarski(X1,X2) != iProver_top ),
% 11.69/2.02      inference(demodulation,[status(thm)],[c_880,c_17]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_4627,plain,
% 11.69/2.02      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_896,c_953]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_890,plain,
% 11.69/2.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.69/2.02      | r1_tarski(X0,X1) = iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_3409,plain,
% 11.69/2.02      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_886,c_890]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_4631,plain,
% 11.69/2.02      ( k1_setfam_1(k1_enumset1(X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_3409,c_953]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_4660,plain,
% 11.69/2.02      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
% 11.69/2.02      inference(demodulation,[status(thm)],[c_4627,c_4631]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_21,negated_conjecture,
% 11.69/2.02      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 11.69/2.02      inference(cnf_transformation,[],[f71]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_888,plain,
% 11.69/2.02      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_5703,plain,
% 11.69/2.02      ( v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
% 11.69/2.02      inference(demodulation,[status(thm)],[c_4660,c_888]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_1,plain,
% 11.69/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 11.69/2.02      inference(cnf_transformation,[],[f73]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_4628,plain,
% 11.69/2.02      ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) = k9_subset_1(X3,X0,k4_xboole_0(X1,X2))
% 11.69/2.02      | r1_tarski(X1,X3) != iProver_top ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_895,c_953]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_18325,plain,
% 11.69/2.02      ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(sK2,X1))) = k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(sK2,X1)) ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_3409,c_4628]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_0,plain,
% 11.69/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.69/2.02      inference(cnf_transformation,[],[f72]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_1553,plain,
% 11.69/2.02      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_17,c_0]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_20474,plain,
% 11.69/2.02      ( k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(k4_xboole_0(sK2,X0),X1)) = k9_subset_1(u1_struct_0(sK0),X1,k4_xboole_0(sK2,X0)) ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_18325,c_1553]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_4629,plain,
% 11.69/2.02      ( k1_setfam_1(k1_enumset1(X0,X0,k4_xboole_0(X1,X2))) = k9_subset_1(X1,X0,k4_xboole_0(X1,X2)) ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_894,c_953]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_23095,plain,
% 11.69/2.02      ( k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(sK2,X1)) = k9_subset_1(sK2,X0,k4_xboole_0(sK2,X1)) ),
% 11.69/2.02      inference(demodulation,[status(thm)],[c_4629,c_18325]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_26964,plain,
% 11.69/2.02      ( k4_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(k4_xboole_0(sK2,X0),X1)) = k9_subset_1(sK2,X1,k4_xboole_0(sK2,X0)) ),
% 11.69/2.02      inference(demodulation,[status(thm)],[c_20474,c_17,c_23095]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_27008,plain,
% 11.69/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,X1))) = k9_subset_1(sK2,X0,k4_xboole_0(sK2,X1)) ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_26964,c_0]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_37802,plain,
% 11.69/2.02      ( k9_subset_1(sK2,X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_1,c_27008]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_38040,plain,
% 11.69/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,sK2)) = k9_subset_1(sK2,X0,sK2) ),
% 11.69/2.02      inference(demodulation,[status(thm)],[c_37802,c_1,c_17]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_24,negated_conjecture,
% 11.69/2.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.69/2.02      inference(cnf_transformation,[],[f68]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_885,plain,
% 11.69/2.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_11701,plain,
% 11.69/2.02      ( v2_tex_2(X0,sK0) = iProver_top
% 11.69/2.02      | v2_tex_2(sK1,sK0) != iProver_top
% 11.69/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.69/2.02      | r1_tarski(X0,sK1) != iProver_top
% 11.69/2.02      | l1_pre_topc(sK0) != iProver_top ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_885,c_3610]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_5108,plain,
% 11.69/2.02      ( v2_tex_2(X0,sK0)
% 11.69/2.02      | ~ v2_tex_2(sK1,sK0)
% 11.69/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.69/2.02      | ~ r1_tarski(X0,sK1)
% 11.69/2.02      | ~ l1_pre_topc(sK0) ),
% 11.69/2.02      inference(resolution,[status(thm)],[c_20,c_24]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_6075,plain,
% 11.69/2.02      ( ~ r1_tarski(X0,sK1)
% 11.69/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.69/2.02      | ~ v2_tex_2(sK1,sK0)
% 11.69/2.02      | v2_tex_2(X0,sK0) ),
% 11.69/2.02      inference(global_propositional_subsumption,[status(thm)],[c_5108,c_25]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_6076,plain,
% 11.69/2.02      ( v2_tex_2(X0,sK0)
% 11.69/2.02      | ~ v2_tex_2(sK1,sK0)
% 11.69/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.69/2.02      | ~ r1_tarski(X0,sK1) ),
% 11.69/2.02      inference(renaming,[status(thm)],[c_6075]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_6103,plain,
% 11.69/2.02      ( v2_tex_2(X0,sK0)
% 11.69/2.02      | ~ v2_tex_2(sK1,sK0)
% 11.69/2.02      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 11.69/2.02      | ~ r1_tarski(X0,sK1) ),
% 11.69/2.02      inference(resolution,[status(thm)],[c_6076,c_18]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_6104,plain,
% 11.69/2.02      ( v2_tex_2(X0,sK0) = iProver_top
% 11.69/2.02      | v2_tex_2(sK1,sK0) != iProver_top
% 11.69/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.69/2.02      | r1_tarski(X0,sK1) != iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_6103]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_13151,plain,
% 11.69/2.02      ( r1_tarski(X0,sK1) != iProver_top
% 11.69/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.69/2.02      | v2_tex_2(sK1,sK0) != iProver_top
% 11.69/2.02      | v2_tex_2(X0,sK0) = iProver_top ),
% 11.69/2.02      inference(global_propositional_subsumption,
% 11.69/2.02                [status(thm)],
% 11.69/2.02                [c_11701,c_6104]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_13152,plain,
% 11.69/2.02      ( v2_tex_2(X0,sK0) = iProver_top
% 11.69/2.02      | v2_tex_2(sK1,sK0) != iProver_top
% 11.69/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.69/2.02      | r1_tarski(X0,sK1) != iProver_top ),
% 11.69/2.02      inference(renaming,[status(thm)],[c_13151]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_13160,plain,
% 11.69/2.02      ( v2_tex_2(k4_xboole_0(X0,X1),sK0) = iProver_top
% 11.69/2.02      | v2_tex_2(sK1,sK0) != iProver_top
% 11.69/2.02      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.69/2.02      | r1_tarski(k4_xboole_0(X0,X1),sK1) != iProver_top ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_895,c_13152]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_16157,plain,
% 11.69/2.02      ( v2_tex_2(k4_xboole_0(sK1,X0),sK0) = iProver_top
% 11.69/2.02      | v2_tex_2(sK1,sK0) != iProver_top
% 11.69/2.02      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_894,c_13160]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_1119,plain,
% 11.69/2.02      ( r1_tarski(sK1,u1_struct_0(sK0)) ),
% 11.69/2.02      inference(resolution,[status(thm)],[c_19,c_24]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_1120,plain,
% 11.69/2.02      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 11.69/2.02      inference(predicate_to_equality,[status(thm)],[c_1119]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_33303,plain,
% 11.69/2.02      ( v2_tex_2(sK1,sK0) != iProver_top
% 11.69/2.02      | v2_tex_2(k4_xboole_0(sK1,X0),sK0) = iProver_top ),
% 11.69/2.02      inference(global_propositional_subsumption,
% 11.69/2.02                [status(thm)],
% 11.69/2.02                [c_16157,c_1120]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_33304,plain,
% 11.69/2.02      ( v2_tex_2(k4_xboole_0(sK1,X0),sK0) = iProver_top
% 11.69/2.02      | v2_tex_2(sK1,sK0) != iProver_top ),
% 11.69/2.02      inference(renaming,[status(thm)],[c_33303]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_38394,plain,
% 11.69/2.02      ( v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) = iProver_top
% 11.69/2.02      | v2_tex_2(sK1,sK0) != iProver_top ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_38040,c_33304]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_38860,plain,
% 11.69/2.02      ( v2_tex_2(k1_setfam_1(k1_enumset1(sK2,sK2,X0)),sK0) = iProver_top ),
% 11.69/2.02      inference(global_propositional_subsumption,
% 11.69/2.02                [status(thm)],
% 11.69/2.02                [c_16726,c_29,c_1118,c_5703,c_38394]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_26995,plain,
% 11.69/2.02      ( k9_subset_1(sK2,X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_1,c_26964]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_27085,plain,
% 11.69/2.02      ( k1_setfam_1(k1_enumset1(sK2,sK2,X0)) = k9_subset_1(sK2,X0,sK2) ),
% 11.69/2.02      inference(demodulation,[status(thm)],[c_26995,c_1,c_17]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_38866,plain,
% 11.69/2.02      ( v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top ),
% 11.69/2.02      inference(light_normalisation,[status(thm)],[c_38860,c_27085]) ).
% 11.69/2.02  
% 11.69/2.02  cnf(c_38873,plain,
% 11.69/2.02      ( $false ),
% 11.69/2.02      inference(superposition,[status(thm)],[c_38866,c_5703]) ).
% 11.69/2.02  
% 11.69/2.02  
% 11.69/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.69/2.02  
% 11.69/2.02  ------                               Statistics
% 11.69/2.02  
% 11.69/2.02  ------ Selected
% 11.69/2.02  
% 11.69/2.02  total_time:                             1.042
% 11.69/2.02  
%------------------------------------------------------------------------------
