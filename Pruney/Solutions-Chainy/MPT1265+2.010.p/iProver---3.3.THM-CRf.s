%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:58 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 549 expanded)
%              Number of clauses        :   88 ( 209 expanded)
%              Number of leaves         :   14 ( 138 expanded)
%              Depth                    :   21
%              Number of atoms          :  384 (2662 expanded)
%              Number of equality atoms :  134 ( 251 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v1_tops_1(X2,X0)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v1_tops_1(X2,X0)
                    & v1_tops_1(X1,X0) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v3_pre_topc(X2,X0)
          & v1_tops_1(X2,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v3_pre_topc(sK2,X0)
        & v1_tops_1(sK2,X0)
        & v1_tops_1(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v3_pre_topc(X2,X0)
            & v1_tops_1(X2,X0)
            & v1_tops_1(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v1_tops_1(X2,X0)
                & v1_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v1_tops_1(X2,sK0)
              & v1_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f26,f25,f24])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f46,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_212,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_698,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_222,plain,
    ( ~ l1_pre_topc(X0_48)
    | l1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_688,plain,
    ( l1_pre_topc(X0_48) != iProver_top
    | l1_struct_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_1089,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_688])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_223,plain,
    ( ~ l1_struct_0(X0_48)
    | u1_struct_0(X0_48) = k2_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_687,plain,
    ( u1_struct_0(X0_48) = k2_struct_0(X0_48)
    | l1_struct_0(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_1219,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1089,c_687])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_213,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_697,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_46))
    | r1_tarski(X0_45,X0_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_686,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(X0_46)) != iProver_top
    | r1_tarski(X0_45,X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_1161,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_686])).

cnf(c_1428,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1219,c_1161])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_225,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(X0_46))
    | ~ r1_tarski(X0_45,X0_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_685,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(X0_46)) = iProver_top
    | r1_tarski(X0_45,X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_214,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_696,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_1432,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1219,c_696])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v1_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_219,plain,
    ( ~ v3_pre_topc(X0_45,X0_48)
    | ~ v1_tops_1(X1_45,X0_48)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(X0_48)))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_48)))
    | ~ v2_pre_topc(X0_48)
    | ~ l1_pre_topc(X0_48)
    | k2_pre_topc(X0_48,k9_subset_1(u1_struct_0(X0_48),X0_45,X1_45)) = k2_pre_topc(X0_48,X0_45) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_691,plain,
    ( k2_pre_topc(X0_48,k9_subset_1(u1_struct_0(X0_48),X0_45,X1_45)) = k2_pre_topc(X0_48,X0_45)
    | v3_pre_topc(X0_45,X0_48) != iProver_top
    | v1_tops_1(X1_45,X0_48) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(X0_48))) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_48))) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_1756,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0_45,X1_45)) = k2_pre_topc(sK0,X0_45)
    | v3_pre_topc(X0_45,sK0) != iProver_top
    | v1_tops_1(X1_45,sK0) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_691])).

cnf(c_1764,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0_45,X1_45)) = k2_pre_topc(sK0,X0_45)
    | v3_pre_topc(X0_45,sK0) != iProver_top
    | v1_tops_1(X1_45,sK0) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1756,c_1219])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3283,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0_45,X1_45)) = k2_pre_topc(sK0,X0_45)
    | v3_pre_topc(X0_45,sK0) != iProver_top
    | v1_tops_1(X1_45,sK0) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1764,c_18,c_19])).

cnf(c_3296,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0_45)) = k2_pre_topc(sK0,sK2)
    | v3_pre_topc(sK2,sK0) != iProver_top
    | v1_tops_1(X0_45,sK0) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1432,c_3283])).

cnf(c_8,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_220,plain,
    ( ~ v1_tops_1(X0_45,X0_48)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_48)))
    | ~ l1_pre_topc(X0_48)
    | k2_pre_topc(X0_48,X0_45) = k2_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_690,plain,
    ( k2_pre_topc(X0_48,X0_45) = k2_struct_0(X0_48)
    | v1_tops_1(X0_45,X0_48) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_48))) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_1724,plain,
    ( k2_pre_topc(sK0,X0_45) = k2_struct_0(sK0)
    | v1_tops_1(X0_45,sK0) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_690])).

cnf(c_2245,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v1_tops_1(X0_45,sK0) != iProver_top
    | k2_pre_topc(sK0,X0_45) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1724,c_19])).

cnf(c_2246,plain,
    ( k2_pre_topc(sK0,X0_45) = k2_struct_0(sK0)
    | v1_tops_1(X0_45,sK0) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2245])).

cnf(c_2256,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
    | v1_tops_1(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1432,c_2246])).

cnf(c_12,negated_conjecture,
    ( v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_270,plain,
    ( ~ v1_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_2359,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2256,c_16,c_14,c_12,c_270])).

cnf(c_3301,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0_45)) = k2_struct_0(sK0)
    | v3_pre_topc(sK2,sK0) != iProver_top
    | v1_tops_1(X0_45,sK0) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3296,c_2359])).

cnf(c_11,negated_conjecture,
    ( v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_24,plain,
    ( v3_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4625,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0_45)) = k2_struct_0(sK0)
    | v1_tops_1(X0_45,sK0) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3301,c_24])).

cnf(c_4634,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0_45)) = k2_struct_0(sK0)
    | v1_tops_1(X0_45,sK0) != iProver_top
    | r1_tarski(X0_45,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_685,c_4625])).

cnf(c_1160,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_696,c_686])).

cnf(c_1429,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1219,c_1160])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_120,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_119])).

cnf(c_151,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_120])).

cnf(c_210,plain,
    ( ~ r1_tarski(X0_45,X0_46)
    | k9_subset_1(X0_46,X0_45,X1_45) = k9_subset_1(X0_46,X1_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_151])).

cnf(c_700,plain,
    ( k9_subset_1(X0_46,X0_45,X1_45) = k9_subset_1(X0_46,X1_45,X0_45)
    | r1_tarski(X0_45,X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_2071,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0_45,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X0_45) ),
    inference(superposition,[status(thm)],[c_1429,c_700])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_152,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_120])).

cnf(c_209,plain,
    ( ~ r1_tarski(X0_45,X0_46)
    | k9_subset_1(X0_46,X1_45,X0_45) = k1_setfam_1(k2_tarski(X1_45,X0_45)) ),
    inference(subtyping,[status(esa)],[c_152])).

cnf(c_701,plain,
    ( k9_subset_1(X0_46,X0_45,X1_45) = k1_setfam_1(k2_tarski(X0_45,X1_45))
    | r1_tarski(X1_45,X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_2072,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0_45,sK2) = k1_setfam_1(k2_tarski(X0_45,sK2)) ),
    inference(superposition,[status(thm)],[c_1429,c_701])).

cnf(c_2075,plain,
    ( k9_subset_1(k2_struct_0(sK0),sK2,X0_45) = k1_setfam_1(k2_tarski(X0_45,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2071,c_2072])).

cnf(c_4868,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X0_45,sK2))) = k2_struct_0(sK0)
    | v1_tops_1(X0_45,sK0) != iProver_top
    | r1_tarski(X0_45,k2_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4634,c_2075])).

cnf(c_4874,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1428,c_4868])).

cnf(c_7,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_221,plain,
    ( v1_tops_1(X0_45,X0_48)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_48)))
    | ~ l1_pre_topc(X0_48)
    | k2_pre_topc(X0_48,X0_45) != k2_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1264,plain,
    ( v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_239,plain,
    ( ~ v1_tops_1(X0_45,X0_48)
    | v1_tops_1(X1_45,X0_48)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_850,plain,
    ( ~ v1_tops_1(X0_45,sK0)
    | v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_45 ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_1066,plain,
    ( v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_912,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),X0_45,sK2) = k1_setfam_1(k2_tarski(X0_45,sK2)) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_1065,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_1023,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0_45)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X0_45)),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_1025,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_226,plain,
    ( ~ r1_tarski(X0_45,X0_46)
    | r1_tarski(k1_setfam_1(k2_tarski(X0_45,X1_45)),X0_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_925,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0_45)),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_933,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_847,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_844,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_10,negated_conjecture,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,negated_conjecture,
    ( v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_22,plain,
    ( v1_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4874,c_1264,c_1066,c_1065,c_1025,c_933,c_847,c_844,c_10,c_22,c_14,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:48:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.39/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/1.00  
% 3.39/1.00  ------  iProver source info
% 3.39/1.00  
% 3.39/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.39/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/1.00  git: non_committed_changes: false
% 3.39/1.00  git: last_make_outside_of_git: false
% 3.39/1.00  
% 3.39/1.00  ------ 
% 3.39/1.00  ------ Parsing...
% 3.39/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.00  ------ Proving...
% 3.39/1.00  ------ Problem Properties 
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  clauses                                 18
% 3.39/1.00  conjectures                             8
% 3.39/1.00  EPR                                     6
% 3.39/1.00  Horn                                    18
% 3.39/1.00  unary                                   8
% 3.39/1.00  binary                                  7
% 3.39/1.00  lits                                    37
% 3.39/1.00  lits eq                                 6
% 3.39/1.00  fd_pure                                 0
% 3.39/1.00  fd_pseudo                               0
% 3.39/1.00  fd_cond                                 0
% 3.39/1.00  fd_pseudo_cond                          0
% 3.39/1.00  AC symbols                              0
% 3.39/1.00  
% 3.39/1.00  ------ Input Options Time Limit: Unbounded
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  ------ 
% 3.39/1.00  Current options:
% 3.39/1.00  ------ 
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  ------ Proving...
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  % SZS status Theorem for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  fof(f10,conjecture,(
% 3.39/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f11,negated_conjecture,(
% 3.39/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.39/1.00    inference(negated_conjecture,[],[f10])).
% 3.39/1.00  
% 3.39/1.00  fof(f20,plain,(
% 3.39/1.00    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f11])).
% 3.39/1.00  
% 3.39/1.00  fof(f21,plain,(
% 3.39/1.00    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.39/1.00    inference(flattening,[],[f20])).
% 3.39/1.00  
% 3.39/1.00  fof(f26,plain,(
% 3.39/1.00    ( ! [X0,X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v3_pre_topc(sK2,X0) & v1_tops_1(sK2,X0) & v1_tops_1(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f25,plain,(
% 3.39/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f24,plain,(
% 3.39/1.00    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f27,plain,(
% 3.39/1.00    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f26,f25,f24])).
% 3.39/1.00  
% 3.39/1.00  fof(f40,plain,(
% 3.39/1.00    l1_pre_topc(sK0)),
% 3.39/1.00    inference(cnf_transformation,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  fof(f7,axiom,(
% 3.39/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f16,plain,(
% 3.39/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.39/1.00    inference(ennf_transformation,[],[f7])).
% 3.39/1.00  
% 3.39/1.00  fof(f35,plain,(
% 3.39/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f16])).
% 3.39/1.00  
% 3.39/1.00  fof(f6,axiom,(
% 3.39/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f15,plain,(
% 3.39/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.39/1.00    inference(ennf_transformation,[],[f6])).
% 3.39/1.00  
% 3.39/1.00  fof(f34,plain,(
% 3.39/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f15])).
% 3.39/1.00  
% 3.39/1.00  fof(f41,plain,(
% 3.39/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.39/1.00    inference(cnf_transformation,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  fof(f5,axiom,(
% 3.39/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f22,plain,(
% 3.39/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.39/1.00    inference(nnf_transformation,[],[f5])).
% 3.39/1.00  
% 3.39/1.00  fof(f32,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f22])).
% 3.39/1.00  
% 3.39/1.00  fof(f33,plain,(
% 3.39/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f22])).
% 3.39/1.00  
% 3.39/1.00  fof(f42,plain,(
% 3.39/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.39/1.00    inference(cnf_transformation,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  fof(f9,axiom,(
% 3.39/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f18,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f9])).
% 3.39/1.00  
% 3.39/1.00  fof(f19,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.39/1.00    inference(flattening,[],[f18])).
% 3.39/1.00  
% 3.39/1.00  fof(f38,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f19])).
% 3.39/1.00  
% 3.39/1.00  fof(f39,plain,(
% 3.39/1.00    v2_pre_topc(sK0)),
% 3.39/1.00    inference(cnf_transformation,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  fof(f8,axiom,(
% 3.39/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f17,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.39/1.00    inference(ennf_transformation,[],[f8])).
% 3.39/1.00  
% 3.39/1.00  fof(f23,plain,(
% 3.39/1.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.39/1.00    inference(nnf_transformation,[],[f17])).
% 3.39/1.00  
% 3.39/1.00  fof(f36,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f23])).
% 3.39/1.00  
% 3.39/1.00  fof(f44,plain,(
% 3.39/1.00    v1_tops_1(sK2,sK0)),
% 3.39/1.00    inference(cnf_transformation,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  fof(f45,plain,(
% 3.39/1.00    v3_pre_topc(sK2,sK0)),
% 3.39/1.00    inference(cnf_transformation,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  fof(f2,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f13,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f2])).
% 3.39/1.00  
% 3.39/1.00  fof(f29,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f13])).
% 3.39/1.00  
% 3.39/1.00  fof(f3,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f14,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.39/1.00    inference(ennf_transformation,[],[f3])).
% 3.39/1.00  
% 3.39/1.00  fof(f30,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f14])).
% 3.39/1.00  
% 3.39/1.00  fof(f4,axiom,(
% 3.39/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f31,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f4])).
% 3.39/1.00  
% 3.39/1.00  fof(f48,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.39/1.00    inference(definition_unfolding,[],[f30,f31])).
% 3.39/1.00  
% 3.39/1.00  fof(f37,plain,(
% 3.39/1.00    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f23])).
% 3.39/1.00  
% 3.39/1.00  fof(f1,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 3.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f12,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.39/1.00    inference(ennf_transformation,[],[f1])).
% 3.39/1.00  
% 3.39/1.00  fof(f28,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f12])).
% 3.39/1.00  
% 3.39/1.00  fof(f47,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 3.39/1.00    inference(definition_unfolding,[],[f28,f31])).
% 3.39/1.00  
% 3.39/1.00  fof(f46,plain,(
% 3.39/1.00    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 3.39/1.00    inference(cnf_transformation,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  fof(f43,plain,(
% 3.39/1.00    v1_tops_1(sK1,sK0)),
% 3.39/1.00    inference(cnf_transformation,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  cnf(c_16,negated_conjecture,
% 3.39/1.00      ( l1_pre_topc(sK0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_212,negated_conjecture,
% 3.39/1.00      ( l1_pre_topc(sK0) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_698,plain,
% 3.39/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6,plain,
% 3.39/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_222,plain,
% 3.39/1.00      ( ~ l1_pre_topc(X0_48) | l1_struct_0(X0_48) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_688,plain,
% 3.39/1.00      ( l1_pre_topc(X0_48) != iProver_top
% 3.39/1.00      | l1_struct_0(X0_48) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1089,plain,
% 3.39/1.00      ( l1_struct_0(sK0) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_698,c_688]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5,plain,
% 3.39/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_223,plain,
% 3.39/1.00      ( ~ l1_struct_0(X0_48) | u1_struct_0(X0_48) = k2_struct_0(X0_48) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_687,plain,
% 3.39/1.00      ( u1_struct_0(X0_48) = k2_struct_0(X0_48)
% 3.39/1.00      | l1_struct_0(X0_48) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1219,plain,
% 3.39/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1089,c_687]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_15,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_213,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_697,plain,
% 3.39/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_224,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_46))
% 3.39/1.00      | r1_tarski(X0_45,X0_46) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_686,plain,
% 3.39/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(X0_46)) != iProver_top
% 3.39/1.00      | r1_tarski(X0_45,X0_46) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1161,plain,
% 3.39/1.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_697,c_686]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1428,plain,
% 3.39/1.00      ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_1219,c_1161]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3,plain,
% 3.39/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_225,plain,
% 3.39/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(X0_46))
% 3.39/1.00      | ~ r1_tarski(X0_45,X0_46) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_685,plain,
% 3.39/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(X0_46)) = iProver_top
% 3.39/1.00      | r1_tarski(X0_45,X0_46) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_14,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_214,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_696,plain,
% 3.39/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1432,plain,
% 3.39/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_1219,c_696]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9,plain,
% 3.39/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.39/1.00      | ~ v1_tops_1(X2,X1)
% 3.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/1.00      | ~ v2_pre_topc(X1)
% 3.39/1.00      | ~ l1_pre_topc(X1)
% 3.39/1.00      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_219,plain,
% 3.39/1.00      ( ~ v3_pre_topc(X0_45,X0_48)
% 3.39/1.00      | ~ v1_tops_1(X1_45,X0_48)
% 3.39/1.00      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(X0_48)))
% 3.39/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_48)))
% 3.39/1.00      | ~ v2_pre_topc(X0_48)
% 3.39/1.00      | ~ l1_pre_topc(X0_48)
% 3.39/1.00      | k2_pre_topc(X0_48,k9_subset_1(u1_struct_0(X0_48),X0_45,X1_45)) = k2_pre_topc(X0_48,X0_45) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_691,plain,
% 3.39/1.00      ( k2_pre_topc(X0_48,k9_subset_1(u1_struct_0(X0_48),X0_45,X1_45)) = k2_pre_topc(X0_48,X0_45)
% 3.39/1.00      | v3_pre_topc(X0_45,X0_48) != iProver_top
% 3.39/1.00      | v1_tops_1(X1_45,X0_48) != iProver_top
% 3.39/1.00      | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(X0_48))) != iProver_top
% 3.39/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_48))) != iProver_top
% 3.39/1.00      | v2_pre_topc(X0_48) != iProver_top
% 3.39/1.00      | l1_pre_topc(X0_48) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1756,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0_45,X1_45)) = k2_pre_topc(sK0,X0_45)
% 3.39/1.00      | v3_pre_topc(X0_45,sK0) != iProver_top
% 3.39/1.00      | v1_tops_1(X1_45,sK0) != iProver_top
% 3.39/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.39/1.00      | m1_subset_1(X1_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.39/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.39/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1219,c_691]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1764,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0_45,X1_45)) = k2_pre_topc(sK0,X0_45)
% 3.39/1.00      | v3_pre_topc(X0_45,sK0) != iProver_top
% 3.39/1.00      | v1_tops_1(X1_45,sK0) != iProver_top
% 3.39/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.39/1.00      | m1_subset_1(X1_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.39/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.39/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_1756,c_1219]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_17,negated_conjecture,
% 3.39/1.00      ( v2_pre_topc(sK0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_18,plain,
% 3.39/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_19,plain,
% 3.39/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3283,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0_45,X1_45)) = k2_pre_topc(sK0,X0_45)
% 3.39/1.00      | v3_pre_topc(X0_45,sK0) != iProver_top
% 3.39/1.00      | v1_tops_1(X1_45,sK0) != iProver_top
% 3.39/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.39/1.00      | m1_subset_1(X1_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_1764,c_18,c_19]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3296,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0_45)) = k2_pre_topc(sK0,sK2)
% 3.39/1.00      | v3_pre_topc(sK2,sK0) != iProver_top
% 3.39/1.00      | v1_tops_1(X0_45,sK0) != iProver_top
% 3.39/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1432,c_3283]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_8,plain,
% 3.39/1.00      ( ~ v1_tops_1(X0,X1)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/1.00      | ~ l1_pre_topc(X1)
% 3.39/1.00      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_220,plain,
% 3.39/1.00      ( ~ v1_tops_1(X0_45,X0_48)
% 3.39/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_48)))
% 3.39/1.00      | ~ l1_pre_topc(X0_48)
% 3.39/1.00      | k2_pre_topc(X0_48,X0_45) = k2_struct_0(X0_48) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_690,plain,
% 3.39/1.00      ( k2_pre_topc(X0_48,X0_45) = k2_struct_0(X0_48)
% 3.39/1.00      | v1_tops_1(X0_45,X0_48) != iProver_top
% 3.39/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_48))) != iProver_top
% 3.39/1.00      | l1_pre_topc(X0_48) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1724,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,X0_45) = k2_struct_0(sK0)
% 3.39/1.00      | v1_tops_1(X0_45,sK0) != iProver_top
% 3.39/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.39/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1219,c_690]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2245,plain,
% 3.39/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 3.39/1.00      | v1_tops_1(X0_45,sK0) != iProver_top
% 3.39/1.00      | k2_pre_topc(sK0,X0_45) = k2_struct_0(sK0) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_1724,c_19]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2246,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,X0_45) = k2_struct_0(sK0)
% 3.39/1.00      | v1_tops_1(X0_45,sK0) != iProver_top
% 3.39/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_2245]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2256,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
% 3.39/1.00      | v1_tops_1(sK2,sK0) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1432,c_2246]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_12,negated_conjecture,
% 3.39/1.00      ( v1_tops_1(sK2,sK0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_270,plain,
% 3.39/1.00      ( ~ v1_tops_1(sK2,sK0)
% 3.39/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/1.00      | ~ l1_pre_topc(sK0)
% 3.39/1.00      | k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_220]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2359,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_2256,c_16,c_14,c_12,c_270]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3301,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0_45)) = k2_struct_0(sK0)
% 3.39/1.00      | v3_pre_topc(sK2,sK0) != iProver_top
% 3.39/1.00      | v1_tops_1(X0_45,sK0) != iProver_top
% 3.39/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_3296,c_2359]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_11,negated_conjecture,
% 3.39/1.00      ( v3_pre_topc(sK2,sK0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_24,plain,
% 3.39/1.00      ( v3_pre_topc(sK2,sK0) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4625,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0_45)) = k2_struct_0(sK0)
% 3.39/1.00      | v1_tops_1(X0_45,sK0) != iProver_top
% 3.39/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_3301,c_24]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4634,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0_45)) = k2_struct_0(sK0)
% 3.39/1.00      | v1_tops_1(X0_45,sK0) != iProver_top
% 3.39/1.00      | r1_tarski(X0_45,k2_struct_0(sK0)) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_685,c_4625]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1160,plain,
% 3.39/1.00      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_696,c_686]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1429,plain,
% 3.39/1.00      ( r1_tarski(sK2,k2_struct_0(sK0)) = iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_1219,c_1160]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.39/1.00      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_119,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.39/1.00      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_120,plain,
% 3.39/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_119]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_151,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,X1)
% 3.39/1.00      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 3.39/1.00      inference(bin_hyper_res,[status(thm)],[c_1,c_120]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_210,plain,
% 3.39/1.00      ( ~ r1_tarski(X0_45,X0_46)
% 3.39/1.00      | k9_subset_1(X0_46,X0_45,X1_45) = k9_subset_1(X0_46,X1_45,X0_45) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_151]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_700,plain,
% 3.39/1.00      ( k9_subset_1(X0_46,X0_45,X1_45) = k9_subset_1(X0_46,X1_45,X0_45)
% 3.39/1.00      | r1_tarski(X0_45,X0_46) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2071,plain,
% 3.39/1.00      ( k9_subset_1(k2_struct_0(sK0),X0_45,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X0_45) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1429,c_700]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.39/1.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.39/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_152,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,X1)
% 3.39/1.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.39/1.00      inference(bin_hyper_res,[status(thm)],[c_2,c_120]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_209,plain,
% 3.39/1.00      ( ~ r1_tarski(X0_45,X0_46)
% 3.39/1.00      | k9_subset_1(X0_46,X1_45,X0_45) = k1_setfam_1(k2_tarski(X1_45,X0_45)) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_152]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_701,plain,
% 3.39/1.00      ( k9_subset_1(X0_46,X0_45,X1_45) = k1_setfam_1(k2_tarski(X0_45,X1_45))
% 3.39/1.00      | r1_tarski(X1_45,X0_46) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2072,plain,
% 3.39/1.00      ( k9_subset_1(k2_struct_0(sK0),X0_45,sK2) = k1_setfam_1(k2_tarski(X0_45,sK2)) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1429,c_701]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2075,plain,
% 3.39/1.00      ( k9_subset_1(k2_struct_0(sK0),sK2,X0_45) = k1_setfam_1(k2_tarski(X0_45,sK2)) ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_2071,c_2072]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4868,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X0_45,sK2))) = k2_struct_0(sK0)
% 3.39/1.00      | v1_tops_1(X0_45,sK0) != iProver_top
% 3.39/1.00      | r1_tarski(X0_45,k2_struct_0(sK0)) != iProver_top ),
% 3.39/1.00      inference(light_normalisation,[status(thm)],[c_4634,c_2075]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4874,plain,
% 3.39/1.00      ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_struct_0(sK0)
% 3.39/1.00      | v1_tops_1(sK1,sK0) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_1428,c_4868]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7,plain,
% 3.39/1.00      ( v1_tops_1(X0,X1)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.39/1.00      | ~ l1_pre_topc(X1)
% 3.39/1.00      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_221,plain,
% 3.39/1.00      ( v1_tops_1(X0_45,X0_48)
% 3.39/1.00      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_48)))
% 3.39/1.00      | ~ l1_pre_topc(X0_48)
% 3.39/1.00      | k2_pre_topc(X0_48,X0_45) != k2_struct_0(X0_48) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1264,plain,
% 3.39/1.00      ( v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
% 3.39/1.00      | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/1.00      | ~ l1_pre_topc(sK0)
% 3.39/1.00      | k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) != k2_struct_0(sK0) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_221]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_239,plain,
% 3.39/1.00      ( ~ v1_tops_1(X0_45,X0_48)
% 3.39/1.00      | v1_tops_1(X1_45,X0_48)
% 3.39/1.00      | X1_45 != X0_45 ),
% 3.39/1.00      theory(equality) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_850,plain,
% 3.39/1.00      ( ~ v1_tops_1(X0_45,sK0)
% 3.39/1.00      | v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 3.39/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_45 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_239]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1066,plain,
% 3.39/1.00      ( v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 3.39/1.00      | ~ v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
% 3.39/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_850]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_912,plain,
% 3.39/1.00      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 3.39/1.00      | k9_subset_1(u1_struct_0(sK0),X0_45,sK2) = k1_setfam_1(k2_tarski(X0_45,sK2)) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_209]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1065,plain,
% 3.39/1.00      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 3.39/1.00      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_912]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1023,plain,
% 3.39/1.00      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,X0_45)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/1.00      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X0_45)),u1_struct_0(sK0)) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_225]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1025,plain,
% 3.39/1.00      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/1.00      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_1023]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_0,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,X1)
% 3.39/1.00      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_226,plain,
% 3.39/1.00      ( ~ r1_tarski(X0_45,X0_46)
% 3.39/1.00      | r1_tarski(k1_setfam_1(k2_tarski(X0_45,X1_45)),X0_46) ),
% 3.39/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_925,plain,
% 3.39/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0_45)),u1_struct_0(sK0))
% 3.39/1.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_226]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_933,plain,
% 3.39/1.00      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
% 3.39/1.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_925]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_847,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/1.00      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_224]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_844,plain,
% 3.39/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.39/1.00      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_224]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10,negated_conjecture,
% 3.39/1.00      ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_13,negated_conjecture,
% 3.39/1.00      ( v1_tops_1(sK1,sK0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_22,plain,
% 3.39/1.00      ( v1_tops_1(sK1,sK0) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(contradiction,plain,
% 3.39/1.00      ( $false ),
% 3.39/1.00      inference(minisat,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_4874,c_1264,c_1066,c_1065,c_1025,c_933,c_847,c_844,
% 3.39/1.00                 c_10,c_22,c_14,c_15,c_16]) ).
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  ------                               Statistics
% 3.39/1.00  
% 3.39/1.00  ------ Selected
% 3.39/1.00  
% 3.39/1.00  total_time:                             0.167
% 3.39/1.00  
%------------------------------------------------------------------------------
