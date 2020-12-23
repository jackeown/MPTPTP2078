%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:56 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 378 expanded)
%              Number of clauses        :   62 ( 118 expanded)
%              Number of leaves         :   12 ( 107 expanded)
%              Depth                    :   19
%              Number of atoms          :  293 (2042 expanded)
%              Number of equality atoms :   86 ( 160 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f23,plain,(
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

fof(f22,plain,(
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

fof(f21,plain,
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

fof(f24,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23,f22,f21])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f38,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_398,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_537,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_168,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_4,c_3])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_207,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_168,c_14])).

cnf(c_208,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_207])).

cnf(c_396,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_208])).

cnf(c_549,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_537,c_396])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | k9_subset_1(X0_45,X1_44,X0_44) = k1_setfam_1(k2_tarski(X1_44,X0_44)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_536,plain,
    ( k9_subset_1(X0_45,X0_44,X1_44) = k1_setfam_1(k2_tarski(X0_44,X1_44))
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_807,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0_44,sK2) = k1_setfam_1(k2_tarski(X0_44,sK2)) ),
    inference(superposition,[status(thm)],[c_549,c_536])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | m1_subset_1(k9_subset_1(X0_45,X1_44,X0_44),k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_535,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(k9_subset_1(X0_45,X1_44,X0_44),k1_zfmisc_1(X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_832,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0_44,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_535])).

cnf(c_1349,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0_44,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_549])).

cnf(c_8,negated_conjecture,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_227,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_228,plain,
    ( v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_228])).

cnf(c_281,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_281])).

cnf(c_540,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
    | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_575,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
    | m1_subset_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_540,c_396])).

cnf(c_941,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) != k2_struct_0(sK0)
    | m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_575,c_807])).

cnf(c_0,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_401,plain,
    ( k2_tarski(X0_44,X1_44) = k2_tarski(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_11,negated_conjecture,
    ( v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v1_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,negated_conjecture,
    ( v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_182,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X0)) = k2_pre_topc(X1,X2)
    | sK2 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_183,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_187,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_1(X0,sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_183,c_15,c_14,c_12])).

cnf(c_188,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
    inference(renaming,[status(thm)],[c_187])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_188])).

cnf(c_315,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_317,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_315,c_13])).

cnf(c_390,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_317])).

cnf(c_10,negated_conjecture,
    ( v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_212,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_213,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_213])).

cnf(c_291,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_293,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_291,c_12])).

cnf(c_393,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_564,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_390,c_393,c_396])).

cnf(c_397,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_538,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_552,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_538,c_396])).

cnf(c_808,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0_44,sK1) = k1_setfam_1(k2_tarski(X0_44,sK1)) ),
    inference(superposition,[status(thm)],[c_552,c_536])).

cnf(c_891,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_564,c_808])).

cnf(c_893,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_401,c_891])).

cnf(c_945,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_941,c_893])).

cnf(c_1360,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1349,c_945])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:31:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 1.44/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.44/0.98  
% 1.44/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.44/0.98  
% 1.44/0.98  ------  iProver source info
% 1.44/0.98  
% 1.44/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.44/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.44/0.98  git: non_committed_changes: false
% 1.44/0.98  git: last_make_outside_of_git: false
% 1.44/0.98  
% 1.44/0.98  ------ 
% 1.44/0.98  
% 1.44/0.98  ------ Input Options
% 1.44/0.98  
% 1.44/0.98  --out_options                           all
% 1.44/0.98  --tptp_safe_out                         true
% 1.44/0.98  --problem_path                          ""
% 1.44/0.98  --include_path                          ""
% 1.44/0.98  --clausifier                            res/vclausify_rel
% 1.44/0.98  --clausifier_options                    --mode clausify
% 1.44/0.98  --stdin                                 false
% 1.44/0.98  --stats_out                             all
% 1.44/0.98  
% 1.44/0.98  ------ General Options
% 1.44/0.98  
% 1.44/0.98  --fof                                   false
% 1.44/0.98  --time_out_real                         305.
% 1.44/0.98  --time_out_virtual                      -1.
% 1.44/0.98  --symbol_type_check                     false
% 1.44/0.98  --clausify_out                          false
% 1.44/0.98  --sig_cnt_out                           false
% 1.44/0.98  --trig_cnt_out                          false
% 1.44/0.98  --trig_cnt_out_tolerance                1.
% 1.44/0.98  --trig_cnt_out_sk_spl                   false
% 1.44/0.98  --abstr_cl_out                          false
% 1.44/0.98  
% 1.44/0.98  ------ Global Options
% 1.44/0.98  
% 1.44/0.98  --schedule                              default
% 1.44/0.98  --add_important_lit                     false
% 1.44/0.98  --prop_solver_per_cl                    1000
% 1.44/0.98  --min_unsat_core                        false
% 1.44/0.98  --soft_assumptions                      false
% 1.44/0.98  --soft_lemma_size                       3
% 1.44/0.98  --prop_impl_unit_size                   0
% 1.44/0.98  --prop_impl_unit                        []
% 1.44/0.98  --share_sel_clauses                     true
% 1.44/0.98  --reset_solvers                         false
% 1.44/0.98  --bc_imp_inh                            [conj_cone]
% 1.44/0.98  --conj_cone_tolerance                   3.
% 1.44/0.98  --extra_neg_conj                        none
% 1.44/0.98  --large_theory_mode                     true
% 1.44/0.98  --prolific_symb_bound                   200
% 1.44/0.98  --lt_threshold                          2000
% 1.44/0.98  --clause_weak_htbl                      true
% 1.44/0.98  --gc_record_bc_elim                     false
% 1.44/0.98  
% 1.44/0.98  ------ Preprocessing Options
% 1.44/0.98  
% 1.44/0.98  --preprocessing_flag                    true
% 1.44/0.98  --time_out_prep_mult                    0.1
% 1.44/0.98  --splitting_mode                        input
% 1.44/0.98  --splitting_grd                         true
% 1.44/0.98  --splitting_cvd                         false
% 1.44/0.98  --splitting_cvd_svl                     false
% 1.44/0.98  --splitting_nvd                         32
% 1.44/0.98  --sub_typing                            true
% 1.44/0.98  --prep_gs_sim                           true
% 1.44/0.98  --prep_unflatten                        true
% 1.44/0.98  --prep_res_sim                          true
% 1.44/0.98  --prep_upred                            true
% 1.44/0.98  --prep_sem_filter                       exhaustive
% 1.44/0.98  --prep_sem_filter_out                   false
% 1.44/0.98  --pred_elim                             true
% 1.44/0.98  --res_sim_input                         true
% 1.44/0.98  --eq_ax_congr_red                       true
% 1.44/0.98  --pure_diseq_elim                       true
% 1.44/0.98  --brand_transform                       false
% 1.44/0.98  --non_eq_to_eq                          false
% 1.44/0.98  --prep_def_merge                        true
% 1.44/0.98  --prep_def_merge_prop_impl              false
% 1.44/0.98  --prep_def_merge_mbd                    true
% 1.44/0.98  --prep_def_merge_tr_red                 false
% 1.44/0.98  --prep_def_merge_tr_cl                  false
% 1.44/0.98  --smt_preprocessing                     true
% 1.44/0.98  --smt_ac_axioms                         fast
% 1.44/0.98  --preprocessed_out                      false
% 1.44/0.98  --preprocessed_stats                    false
% 1.44/0.98  
% 1.44/0.98  ------ Abstraction refinement Options
% 1.44/0.98  
% 1.44/0.98  --abstr_ref                             []
% 1.44/0.98  --abstr_ref_prep                        false
% 1.44/0.98  --abstr_ref_until_sat                   false
% 1.44/0.98  --abstr_ref_sig_restrict                funpre
% 1.44/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.44/0.98  --abstr_ref_under                       []
% 1.44/0.98  
% 1.44/0.98  ------ SAT Options
% 1.44/0.98  
% 1.44/0.98  --sat_mode                              false
% 1.44/0.98  --sat_fm_restart_options                ""
% 1.44/0.98  --sat_gr_def                            false
% 1.44/0.98  --sat_epr_types                         true
% 1.44/0.98  --sat_non_cyclic_types                  false
% 1.44/0.98  --sat_finite_models                     false
% 1.44/0.98  --sat_fm_lemmas                         false
% 1.44/0.98  --sat_fm_prep                           false
% 1.44/0.98  --sat_fm_uc_incr                        true
% 1.44/0.98  --sat_out_model                         small
% 1.44/0.98  --sat_out_clauses                       false
% 1.44/0.98  
% 1.44/0.98  ------ QBF Options
% 1.44/0.98  
% 1.44/0.98  --qbf_mode                              false
% 1.44/0.98  --qbf_elim_univ                         false
% 1.44/0.98  --qbf_dom_inst                          none
% 1.44/0.98  --qbf_dom_pre_inst                      false
% 1.44/0.98  --qbf_sk_in                             false
% 1.44/0.98  --qbf_pred_elim                         true
% 1.44/0.98  --qbf_split                             512
% 1.44/0.98  
% 1.44/0.98  ------ BMC1 Options
% 1.44/0.98  
% 1.44/0.98  --bmc1_incremental                      false
% 1.44/0.98  --bmc1_axioms                           reachable_all
% 1.44/0.98  --bmc1_min_bound                        0
% 1.44/0.98  --bmc1_max_bound                        -1
% 1.44/0.98  --bmc1_max_bound_default                -1
% 1.44/0.98  --bmc1_symbol_reachability              true
% 1.44/0.98  --bmc1_property_lemmas                  false
% 1.44/0.98  --bmc1_k_induction                      false
% 1.44/0.98  --bmc1_non_equiv_states                 false
% 1.44/0.98  --bmc1_deadlock                         false
% 1.44/0.98  --bmc1_ucm                              false
% 1.44/0.98  --bmc1_add_unsat_core                   none
% 1.44/0.98  --bmc1_unsat_core_children              false
% 1.44/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.44/0.98  --bmc1_out_stat                         full
% 1.44/0.98  --bmc1_ground_init                      false
% 1.44/0.98  --bmc1_pre_inst_next_state              false
% 1.44/0.98  --bmc1_pre_inst_state                   false
% 1.44/0.98  --bmc1_pre_inst_reach_state             false
% 1.44/0.98  --bmc1_out_unsat_core                   false
% 1.44/0.98  --bmc1_aig_witness_out                  false
% 1.44/0.98  --bmc1_verbose                          false
% 1.44/0.98  --bmc1_dump_clauses_tptp                false
% 1.44/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.44/0.98  --bmc1_dump_file                        -
% 1.44/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.44/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.44/0.98  --bmc1_ucm_extend_mode                  1
% 1.44/0.98  --bmc1_ucm_init_mode                    2
% 1.44/0.98  --bmc1_ucm_cone_mode                    none
% 1.44/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.44/0.98  --bmc1_ucm_relax_model                  4
% 1.44/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.44/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.44/0.98  --bmc1_ucm_layered_model                none
% 1.44/0.98  --bmc1_ucm_max_lemma_size               10
% 1.44/0.98  
% 1.44/0.98  ------ AIG Options
% 1.44/0.98  
% 1.44/0.98  --aig_mode                              false
% 1.44/0.98  
% 1.44/0.98  ------ Instantiation Options
% 1.44/0.98  
% 1.44/0.98  --instantiation_flag                    true
% 1.44/0.98  --inst_sos_flag                         false
% 1.44/0.98  --inst_sos_phase                        true
% 1.44/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.44/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.44/0.98  --inst_lit_sel_side                     num_symb
% 1.44/0.98  --inst_solver_per_active                1400
% 1.44/0.98  --inst_solver_calls_frac                1.
% 1.44/0.98  --inst_passive_queue_type               priority_queues
% 1.44/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.44/0.98  --inst_passive_queues_freq              [25;2]
% 1.44/0.98  --inst_dismatching                      true
% 1.44/0.98  --inst_eager_unprocessed_to_passive     true
% 1.44/0.98  --inst_prop_sim_given                   true
% 1.44/0.98  --inst_prop_sim_new                     false
% 1.44/0.98  --inst_subs_new                         false
% 1.44/0.98  --inst_eq_res_simp                      false
% 1.44/0.98  --inst_subs_given                       false
% 1.44/0.98  --inst_orphan_elimination               true
% 1.44/0.98  --inst_learning_loop_flag               true
% 1.44/0.98  --inst_learning_start                   3000
% 1.44/0.98  --inst_learning_factor                  2
% 1.44/0.98  --inst_start_prop_sim_after_learn       3
% 1.44/0.98  --inst_sel_renew                        solver
% 1.44/0.98  --inst_lit_activity_flag                true
% 1.44/0.98  --inst_restr_to_given                   false
% 1.44/0.98  --inst_activity_threshold               500
% 1.44/0.98  --inst_out_proof                        true
% 1.44/0.98  
% 1.44/0.98  ------ Resolution Options
% 1.44/0.98  
% 1.44/0.98  --resolution_flag                       true
% 1.44/0.98  --res_lit_sel                           adaptive
% 1.44/0.98  --res_lit_sel_side                      none
% 1.44/0.98  --res_ordering                          kbo
% 1.44/0.98  --res_to_prop_solver                    active
% 1.44/0.98  --res_prop_simpl_new                    false
% 1.44/0.98  --res_prop_simpl_given                  true
% 1.44/0.98  --res_passive_queue_type                priority_queues
% 1.44/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.44/0.98  --res_passive_queues_freq               [15;5]
% 1.44/0.98  --res_forward_subs                      full
% 1.44/0.98  --res_backward_subs                     full
% 1.44/0.98  --res_forward_subs_resolution           true
% 1.44/0.98  --res_backward_subs_resolution          true
% 1.44/0.98  --res_orphan_elimination                true
% 1.44/0.98  --res_time_limit                        2.
% 1.44/0.98  --res_out_proof                         true
% 1.44/0.98  
% 1.44/0.98  ------ Superposition Options
% 1.44/0.98  
% 1.44/0.98  --superposition_flag                    true
% 1.44/0.98  --sup_passive_queue_type                priority_queues
% 1.44/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.44/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.44/0.98  --demod_completeness_check              fast
% 1.44/0.98  --demod_use_ground                      true
% 1.44/0.98  --sup_to_prop_solver                    passive
% 1.44/0.98  --sup_prop_simpl_new                    true
% 1.44/0.98  --sup_prop_simpl_given                  true
% 1.44/0.98  --sup_fun_splitting                     false
% 1.44/0.98  --sup_smt_interval                      50000
% 1.44/0.98  
% 1.44/0.98  ------ Superposition Simplification Setup
% 1.44/0.98  
% 1.44/0.98  --sup_indices_passive                   []
% 1.44/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.44/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/0.98  --sup_full_bw                           [BwDemod]
% 1.44/0.98  --sup_immed_triv                        [TrivRules]
% 1.44/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.44/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/0.98  --sup_immed_bw_main                     []
% 1.44/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.44/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.44/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.44/0.98  
% 1.44/0.98  ------ Combination Options
% 1.44/0.98  
% 1.44/0.98  --comb_res_mult                         3
% 1.44/0.98  --comb_sup_mult                         2
% 1.44/0.98  --comb_inst_mult                        10
% 1.44/0.98  
% 1.44/0.98  ------ Debug Options
% 1.44/0.98  
% 1.44/0.98  --dbg_backtrace                         false
% 1.44/0.98  --dbg_dump_prop_clauses                 false
% 1.44/0.98  --dbg_dump_prop_clauses_file            -
% 1.44/0.98  --dbg_out_stat                          false
% 1.44/0.98  ------ Parsing...
% 1.44/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.44/0.98  
% 1.44/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.44/0.98  
% 1.44/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.44/0.98  
% 1.44/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.44/0.98  ------ Proving...
% 1.44/0.98  ------ Problem Properties 
% 1.44/0.98  
% 1.44/0.98  
% 1.44/0.98  clauses                                 14
% 1.44/0.98  conjectures                             2
% 1.44/0.98  EPR                                     0
% 1.44/0.98  Horn                                    14
% 1.44/0.98  unary                                   10
% 1.44/0.98  binary                                  3
% 1.44/0.98  lits                                    19
% 1.44/0.98  lits eq                                 12
% 1.44/0.98  fd_pure                                 0
% 1.44/0.98  fd_pseudo                               0
% 1.44/0.98  fd_cond                                 0
% 1.44/0.98  fd_pseudo_cond                          0
% 1.44/0.98  AC symbols                              0
% 1.44/0.98  
% 1.44/0.98  ------ Schedule dynamic 5 is on 
% 1.44/0.98  
% 1.44/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.44/0.98  
% 1.44/0.98  
% 1.44/0.98  ------ 
% 1.44/0.98  Current options:
% 1.44/0.98  ------ 
% 1.44/0.98  
% 1.44/0.98  ------ Input Options
% 1.44/0.98  
% 1.44/0.98  --out_options                           all
% 1.44/0.98  --tptp_safe_out                         true
% 1.44/0.98  --problem_path                          ""
% 1.44/0.98  --include_path                          ""
% 1.44/0.98  --clausifier                            res/vclausify_rel
% 1.44/0.98  --clausifier_options                    --mode clausify
% 1.44/0.98  --stdin                                 false
% 1.44/0.98  --stats_out                             all
% 1.44/0.98  
% 1.44/0.98  ------ General Options
% 1.44/0.98  
% 1.44/0.98  --fof                                   false
% 1.44/0.98  --time_out_real                         305.
% 1.44/0.98  --time_out_virtual                      -1.
% 1.44/0.98  --symbol_type_check                     false
% 1.44/0.98  --clausify_out                          false
% 1.44/0.98  --sig_cnt_out                           false
% 1.44/0.98  --trig_cnt_out                          false
% 1.44/0.98  --trig_cnt_out_tolerance                1.
% 1.44/0.98  --trig_cnt_out_sk_spl                   false
% 1.44/0.98  --abstr_cl_out                          false
% 1.44/0.98  
% 1.44/0.98  ------ Global Options
% 1.44/0.98  
% 1.44/0.98  --schedule                              default
% 1.44/0.98  --add_important_lit                     false
% 1.44/0.98  --prop_solver_per_cl                    1000
% 1.44/0.98  --min_unsat_core                        false
% 1.44/0.98  --soft_assumptions                      false
% 1.44/0.98  --soft_lemma_size                       3
% 1.44/0.98  --prop_impl_unit_size                   0
% 1.44/0.98  --prop_impl_unit                        []
% 1.44/0.98  --share_sel_clauses                     true
% 1.44/0.98  --reset_solvers                         false
% 1.44/0.98  --bc_imp_inh                            [conj_cone]
% 1.44/0.98  --conj_cone_tolerance                   3.
% 1.44/0.98  --extra_neg_conj                        none
% 1.44/0.98  --large_theory_mode                     true
% 1.44/0.98  --prolific_symb_bound                   200
% 1.44/0.98  --lt_threshold                          2000
% 1.44/0.98  --clause_weak_htbl                      true
% 1.44/0.98  --gc_record_bc_elim                     false
% 1.44/0.98  
% 1.44/0.98  ------ Preprocessing Options
% 1.44/0.98  
% 1.44/0.98  --preprocessing_flag                    true
% 1.44/0.98  --time_out_prep_mult                    0.1
% 1.44/0.98  --splitting_mode                        input
% 1.44/0.98  --splitting_grd                         true
% 1.44/0.98  --splitting_cvd                         false
% 1.44/0.98  --splitting_cvd_svl                     false
% 1.44/0.98  --splitting_nvd                         32
% 1.44/0.98  --sub_typing                            true
% 1.44/0.98  --prep_gs_sim                           true
% 1.44/0.98  --prep_unflatten                        true
% 1.44/0.98  --prep_res_sim                          true
% 1.44/0.98  --prep_upred                            true
% 1.44/0.98  --prep_sem_filter                       exhaustive
% 1.44/0.98  --prep_sem_filter_out                   false
% 1.44/0.98  --pred_elim                             true
% 1.44/0.98  --res_sim_input                         true
% 1.44/0.98  --eq_ax_congr_red                       true
% 1.44/0.98  --pure_diseq_elim                       true
% 1.44/0.98  --brand_transform                       false
% 1.44/0.98  --non_eq_to_eq                          false
% 1.44/0.98  --prep_def_merge                        true
% 1.44/0.98  --prep_def_merge_prop_impl              false
% 1.44/0.98  --prep_def_merge_mbd                    true
% 1.44/0.98  --prep_def_merge_tr_red                 false
% 1.44/0.98  --prep_def_merge_tr_cl                  false
% 1.44/0.98  --smt_preprocessing                     true
% 1.44/0.98  --smt_ac_axioms                         fast
% 1.44/0.98  --preprocessed_out                      false
% 1.44/0.98  --preprocessed_stats                    false
% 1.44/0.98  
% 1.44/0.98  ------ Abstraction refinement Options
% 1.44/0.98  
% 1.44/0.98  --abstr_ref                             []
% 1.44/0.98  --abstr_ref_prep                        false
% 1.44/0.98  --abstr_ref_until_sat                   false
% 1.44/0.98  --abstr_ref_sig_restrict                funpre
% 1.44/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.44/0.98  --abstr_ref_under                       []
% 1.44/0.98  
% 1.44/0.98  ------ SAT Options
% 1.44/0.98  
% 1.44/0.98  --sat_mode                              false
% 1.44/0.98  --sat_fm_restart_options                ""
% 1.44/0.98  --sat_gr_def                            false
% 1.44/0.98  --sat_epr_types                         true
% 1.44/0.98  --sat_non_cyclic_types                  false
% 1.44/0.98  --sat_finite_models                     false
% 1.44/0.98  --sat_fm_lemmas                         false
% 1.44/0.98  --sat_fm_prep                           false
% 1.44/0.98  --sat_fm_uc_incr                        true
% 1.44/0.98  --sat_out_model                         small
% 1.44/0.98  --sat_out_clauses                       false
% 1.44/0.98  
% 1.44/0.98  ------ QBF Options
% 1.44/0.98  
% 1.44/0.98  --qbf_mode                              false
% 1.44/0.98  --qbf_elim_univ                         false
% 1.44/0.98  --qbf_dom_inst                          none
% 1.44/0.98  --qbf_dom_pre_inst                      false
% 1.44/0.98  --qbf_sk_in                             false
% 1.44/0.98  --qbf_pred_elim                         true
% 1.44/0.98  --qbf_split                             512
% 1.44/0.98  
% 1.44/0.98  ------ BMC1 Options
% 1.44/0.98  
% 1.44/0.98  --bmc1_incremental                      false
% 1.44/0.98  --bmc1_axioms                           reachable_all
% 1.44/0.98  --bmc1_min_bound                        0
% 1.44/0.98  --bmc1_max_bound                        -1
% 1.44/0.98  --bmc1_max_bound_default                -1
% 1.44/0.98  --bmc1_symbol_reachability              true
% 1.44/0.98  --bmc1_property_lemmas                  false
% 1.44/0.98  --bmc1_k_induction                      false
% 1.44/0.98  --bmc1_non_equiv_states                 false
% 1.44/0.98  --bmc1_deadlock                         false
% 1.44/0.98  --bmc1_ucm                              false
% 1.44/0.98  --bmc1_add_unsat_core                   none
% 1.44/0.98  --bmc1_unsat_core_children              false
% 1.44/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.44/0.98  --bmc1_out_stat                         full
% 1.44/0.98  --bmc1_ground_init                      false
% 1.44/0.98  --bmc1_pre_inst_next_state              false
% 1.44/0.98  --bmc1_pre_inst_state                   false
% 1.44/0.98  --bmc1_pre_inst_reach_state             false
% 1.44/0.98  --bmc1_out_unsat_core                   false
% 1.44/0.98  --bmc1_aig_witness_out                  false
% 1.44/0.98  --bmc1_verbose                          false
% 1.44/0.98  --bmc1_dump_clauses_tptp                false
% 1.44/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.44/0.98  --bmc1_dump_file                        -
% 1.44/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.44/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.44/0.98  --bmc1_ucm_extend_mode                  1
% 1.44/0.98  --bmc1_ucm_init_mode                    2
% 1.44/0.98  --bmc1_ucm_cone_mode                    none
% 1.44/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.44/0.98  --bmc1_ucm_relax_model                  4
% 1.44/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.44/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.44/0.98  --bmc1_ucm_layered_model                none
% 1.44/0.98  --bmc1_ucm_max_lemma_size               10
% 1.44/0.98  
% 1.44/0.98  ------ AIG Options
% 1.44/0.98  
% 1.44/0.98  --aig_mode                              false
% 1.44/0.98  
% 1.44/0.98  ------ Instantiation Options
% 1.44/0.98  
% 1.44/0.98  --instantiation_flag                    true
% 1.44/0.98  --inst_sos_flag                         false
% 1.44/0.98  --inst_sos_phase                        true
% 1.44/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.44/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.44/0.98  --inst_lit_sel_side                     none
% 1.44/0.98  --inst_solver_per_active                1400
% 1.44/0.98  --inst_solver_calls_frac                1.
% 1.44/0.98  --inst_passive_queue_type               priority_queues
% 1.44/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.44/0.98  --inst_passive_queues_freq              [25;2]
% 1.44/0.98  --inst_dismatching                      true
% 1.44/0.98  --inst_eager_unprocessed_to_passive     true
% 1.44/0.98  --inst_prop_sim_given                   true
% 1.44/0.98  --inst_prop_sim_new                     false
% 1.44/0.98  --inst_subs_new                         false
% 1.44/0.98  --inst_eq_res_simp                      false
% 1.44/0.98  --inst_subs_given                       false
% 1.44/0.98  --inst_orphan_elimination               true
% 1.44/0.98  --inst_learning_loop_flag               true
% 1.44/0.98  --inst_learning_start                   3000
% 1.44/0.98  --inst_learning_factor                  2
% 1.44/0.98  --inst_start_prop_sim_after_learn       3
% 1.44/0.98  --inst_sel_renew                        solver
% 1.44/0.98  --inst_lit_activity_flag                true
% 1.44/0.98  --inst_restr_to_given                   false
% 1.44/0.98  --inst_activity_threshold               500
% 1.44/0.98  --inst_out_proof                        true
% 1.44/0.98  
% 1.44/0.98  ------ Resolution Options
% 1.44/0.98  
% 1.44/0.98  --resolution_flag                       false
% 1.44/0.98  --res_lit_sel                           adaptive
% 1.44/0.98  --res_lit_sel_side                      none
% 1.44/0.98  --res_ordering                          kbo
% 1.44/0.98  --res_to_prop_solver                    active
% 1.44/0.98  --res_prop_simpl_new                    false
% 1.44/0.98  --res_prop_simpl_given                  true
% 1.44/0.98  --res_passive_queue_type                priority_queues
% 1.44/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.44/0.98  --res_passive_queues_freq               [15;5]
% 1.44/0.98  --res_forward_subs                      full
% 1.44/0.98  --res_backward_subs                     full
% 1.44/0.98  --res_forward_subs_resolution           true
% 1.44/0.98  --res_backward_subs_resolution          true
% 1.44/0.98  --res_orphan_elimination                true
% 1.44/0.98  --res_time_limit                        2.
% 1.44/0.98  --res_out_proof                         true
% 1.44/0.98  
% 1.44/0.98  ------ Superposition Options
% 1.44/0.98  
% 1.44/0.98  --superposition_flag                    true
% 1.44/0.98  --sup_passive_queue_type                priority_queues
% 1.44/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.44/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.44/0.98  --demod_completeness_check              fast
% 1.44/0.98  --demod_use_ground                      true
% 1.44/0.98  --sup_to_prop_solver                    passive
% 1.44/0.98  --sup_prop_simpl_new                    true
% 1.44/0.98  --sup_prop_simpl_given                  true
% 1.44/0.98  --sup_fun_splitting                     false
% 1.44/0.98  --sup_smt_interval                      50000
% 1.44/0.98  
% 1.44/0.98  ------ Superposition Simplification Setup
% 1.44/0.98  
% 1.44/0.98  --sup_indices_passive                   []
% 1.44/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.44/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/0.98  --sup_full_bw                           [BwDemod]
% 1.44/0.98  --sup_immed_triv                        [TrivRules]
% 1.44/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.44/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/0.98  --sup_immed_bw_main                     []
% 1.44/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.44/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.44/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.44/0.98  
% 1.44/0.98  ------ Combination Options
% 1.44/0.98  
% 1.44/0.98  --comb_res_mult                         3
% 1.44/0.98  --comb_sup_mult                         2
% 1.44/0.98  --comb_inst_mult                        10
% 1.44/0.98  
% 1.44/0.98  ------ Debug Options
% 1.44/0.98  
% 1.44/0.98  --dbg_backtrace                         false
% 1.44/0.98  --dbg_dump_prop_clauses                 false
% 1.44/0.98  --dbg_dump_prop_clauses_file            -
% 1.44/0.98  --dbg_out_stat                          false
% 1.44/0.98  
% 1.44/0.98  
% 1.44/0.98  
% 1.44/0.98  
% 1.44/0.98  ------ Proving...
% 1.44/0.98  
% 1.44/0.98  
% 1.44/0.98  % SZS status Theorem for theBenchmark.p
% 1.44/0.98  
% 1.44/0.98   Resolution empty clause
% 1.44/0.98  
% 1.44/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.44/0.98  
% 1.44/0.98  fof(f9,conjecture,(
% 1.44/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/0.98  
% 1.44/0.98  fof(f10,negated_conjecture,(
% 1.44/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.44/0.98    inference(negated_conjecture,[],[f9])).
% 1.44/0.98  
% 1.44/0.98  fof(f18,plain,(
% 1.44/0.98    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.44/0.98    inference(ennf_transformation,[],[f10])).
% 1.44/0.98  
% 1.44/0.98  fof(f19,plain,(
% 1.44/0.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.44/0.98    inference(flattening,[],[f18])).
% 1.44/0.98  
% 1.44/0.98  fof(f23,plain,(
% 1.44/0.98    ( ! [X0,X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v3_pre_topc(sK2,X0) & v1_tops_1(sK2,X0) & v1_tops_1(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.44/0.98    introduced(choice_axiom,[])).
% 1.44/0.98  
% 1.44/0.98  fof(f22,plain,(
% 1.44/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.44/0.98    introduced(choice_axiom,[])).
% 1.44/0.98  
% 1.44/0.98  fof(f21,plain,(
% 1.44/0.98    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.44/0.98    introduced(choice_axiom,[])).
% 1.44/0.98  
% 1.44/0.98  fof(f24,plain,(
% 1.44/0.98    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.44/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23,f22,f21])).
% 1.44/0.98  
% 1.44/0.98  fof(f37,plain,(
% 1.44/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.44/0.98    inference(cnf_transformation,[],[f24])).
% 1.44/0.98  
% 1.44/0.98  fof(f6,axiom,(
% 1.44/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/0.98  
% 1.44/0.98  fof(f14,plain,(
% 1.44/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.44/0.98    inference(ennf_transformation,[],[f6])).
% 1.44/0.98  
% 1.44/0.98  fof(f30,plain,(
% 1.44/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.98    inference(cnf_transformation,[],[f14])).
% 1.44/0.98  
% 1.44/0.98  fof(f5,axiom,(
% 1.44/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/0.98  
% 1.44/0.98  fof(f13,plain,(
% 1.44/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.44/0.98    inference(ennf_transformation,[],[f5])).
% 1.44/0.98  
% 1.44/0.98  fof(f29,plain,(
% 1.44/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.44/0.98    inference(cnf_transformation,[],[f13])).
% 1.44/0.98  
% 1.44/0.98  fof(f35,plain,(
% 1.44/0.98    l1_pre_topc(sK0)),
% 1.44/0.98    inference(cnf_transformation,[],[f24])).
% 1.44/0.98  
% 1.44/0.98  fof(f3,axiom,(
% 1.44/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/0.98  
% 1.44/0.98  fof(f12,plain,(
% 1.44/0.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.44/0.98    inference(ennf_transformation,[],[f3])).
% 1.44/0.98  
% 1.44/0.98  fof(f27,plain,(
% 1.44/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.98    inference(cnf_transformation,[],[f12])).
% 1.44/0.98  
% 1.44/0.98  fof(f4,axiom,(
% 1.44/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/0.98  
% 1.44/0.98  fof(f28,plain,(
% 1.44/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.44/0.98    inference(cnf_transformation,[],[f4])).
% 1.44/0.98  
% 1.44/0.98  fof(f42,plain,(
% 1.44/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.98    inference(definition_unfolding,[],[f27,f28])).
% 1.44/0.98  
% 1.44/0.98  fof(f2,axiom,(
% 1.44/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/0.98  
% 1.44/0.98  fof(f11,plain,(
% 1.44/0.98    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.44/0.98    inference(ennf_transformation,[],[f2])).
% 1.44/0.98  
% 1.44/0.98  fof(f26,plain,(
% 1.44/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.98    inference(cnf_transformation,[],[f11])).
% 1.44/0.98  
% 1.44/0.98  fof(f41,plain,(
% 1.44/0.98    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.44/0.98    inference(cnf_transformation,[],[f24])).
% 1.44/0.98  
% 1.44/0.98  fof(f7,axiom,(
% 1.44/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/0.98  
% 1.44/0.98  fof(f15,plain,(
% 1.44/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.98    inference(ennf_transformation,[],[f7])).
% 1.44/0.98  
% 1.44/0.98  fof(f20,plain,(
% 1.44/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.98    inference(nnf_transformation,[],[f15])).
% 1.44/0.98  
% 1.44/0.98  fof(f32,plain,(
% 1.44/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.98    inference(cnf_transformation,[],[f20])).
% 1.44/0.98  
% 1.44/0.98  fof(f1,axiom,(
% 1.44/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/0.98  
% 1.44/0.98  fof(f25,plain,(
% 1.44/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.44/0.98    inference(cnf_transformation,[],[f1])).
% 1.44/0.98  
% 1.44/0.98  fof(f38,plain,(
% 1.44/0.98    v1_tops_1(sK1,sK0)),
% 1.44/0.98    inference(cnf_transformation,[],[f24])).
% 1.44/0.98  
% 1.44/0.98  fof(f8,axiom,(
% 1.44/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.44/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/0.98  
% 1.44/0.98  fof(f16,plain,(
% 1.44/0.98    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.44/0.98    inference(ennf_transformation,[],[f8])).
% 1.44/0.98  
% 1.44/0.98  fof(f17,plain,(
% 1.44/0.98    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.44/0.98    inference(flattening,[],[f16])).
% 1.44/0.98  
% 1.44/0.98  fof(f33,plain,(
% 1.44/0.98    ( ! [X2,X0,X1] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.44/0.98    inference(cnf_transformation,[],[f17])).
% 1.44/0.98  
% 1.44/0.98  fof(f40,plain,(
% 1.44/0.98    v3_pre_topc(sK2,sK0)),
% 1.44/0.98    inference(cnf_transformation,[],[f24])).
% 1.44/0.98  
% 1.44/0.98  fof(f34,plain,(
% 1.44/0.98    v2_pre_topc(sK0)),
% 1.44/0.98    inference(cnf_transformation,[],[f24])).
% 1.44/0.98  
% 1.44/0.98  fof(f36,plain,(
% 1.44/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.44/0.98    inference(cnf_transformation,[],[f24])).
% 1.44/0.98  
% 1.44/0.98  fof(f39,plain,(
% 1.44/0.98    v1_tops_1(sK2,sK0)),
% 1.44/0.98    inference(cnf_transformation,[],[f24])).
% 1.44/0.98  
% 1.44/0.98  fof(f31,plain,(
% 1.44/0.98    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.98    inference(cnf_transformation,[],[f20])).
% 1.44/0.98  
% 1.44/0.98  cnf(c_12,negated_conjecture,
% 1.44/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.44/0.98      inference(cnf_transformation,[],[f37]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_398,negated_conjecture,
% 1.44/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.44/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_537,plain,
% 1.44/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.44/0.98      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_4,plain,
% 1.44/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.44/0.98      inference(cnf_transformation,[],[f30]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_3,plain,
% 1.44/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.44/0.98      inference(cnf_transformation,[],[f29]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_168,plain,
% 1.44/0.98      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.44/0.98      inference(resolution,[status(thm)],[c_4,c_3]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_14,negated_conjecture,
% 1.44/0.98      ( l1_pre_topc(sK0) ),
% 1.44/0.98      inference(cnf_transformation,[],[f35]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_207,plain,
% 1.44/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.44/0.98      inference(resolution_lifted,[status(thm)],[c_168,c_14]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_208,plain,
% 1.44/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.44/0.98      inference(unflattening,[status(thm)],[c_207]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_396,plain,
% 1.44/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.44/0.98      inference(subtyping,[status(esa)],[c_208]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_549,plain,
% 1.44/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 1.44/0.98      inference(light_normalisation,[status(thm)],[c_537,c_396]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_2,plain,
% 1.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.44/0.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 1.44/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_399,plain,
% 1.44/0.98      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
% 1.44/0.98      | k9_subset_1(X0_45,X1_44,X0_44) = k1_setfam_1(k2_tarski(X1_44,X0_44)) ),
% 1.44/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_536,plain,
% 1.44/0.98      ( k9_subset_1(X0_45,X0_44,X1_44) = k1_setfam_1(k2_tarski(X0_44,X1_44))
% 1.44/0.98      | m1_subset_1(X1_44,k1_zfmisc_1(X0_45)) != iProver_top ),
% 1.44/0.98      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_807,plain,
% 1.44/0.98      ( k9_subset_1(k2_struct_0(sK0),X0_44,sK2) = k1_setfam_1(k2_tarski(X0_44,sK2)) ),
% 1.44/0.98      inference(superposition,[status(thm)],[c_549,c_536]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_1,plain,
% 1.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.44/0.98      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 1.44/0.98      inference(cnf_transformation,[],[f26]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_400,plain,
% 1.44/0.98      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
% 1.44/0.98      | m1_subset_1(k9_subset_1(X0_45,X1_44,X0_44),k1_zfmisc_1(X0_45)) ),
% 1.44/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_535,plain,
% 1.44/0.98      ( m1_subset_1(X0_44,k1_zfmisc_1(X0_45)) != iProver_top
% 1.44/0.98      | m1_subset_1(k9_subset_1(X0_45,X1_44,X0_44),k1_zfmisc_1(X0_45)) = iProver_top ),
% 1.44/0.98      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_832,plain,
% 1.44/0.98      ( m1_subset_1(k1_setfam_1(k2_tarski(X0_44,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 1.44/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.44/0.98      inference(superposition,[status(thm)],[c_807,c_535]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_1349,plain,
% 1.44/0.98      ( m1_subset_1(k1_setfam_1(k2_tarski(X0_44,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 1.44/0.98      inference(global_propositional_subsumption,[status(thm)],[c_832,c_549]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_8,negated_conjecture,
% 1.44/0.98      ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 1.44/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_5,plain,
% 1.44/0.98      ( v1_tops_1(X0,X1)
% 1.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.44/0.98      | ~ l1_pre_topc(X1)
% 1.44/0.98      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 1.44/0.98      inference(cnf_transformation,[],[f32]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_227,plain,
% 1.44/0.98      ( v1_tops_1(X0,X1)
% 1.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.44/0.98      | k2_pre_topc(X1,X0) != k2_struct_0(X1)
% 1.44/0.98      | sK0 != X1 ),
% 1.44/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_228,plain,
% 1.44/0.98      ( v1_tops_1(X0,sK0)
% 1.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
% 1.44/0.98      inference(unflattening,[status(thm)],[c_227]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_280,plain,
% 1.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 1.44/0.98      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
% 1.44/0.98      | sK0 != sK0 ),
% 1.44/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_228]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_281,plain,
% 1.44/0.98      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0) ),
% 1.44/0.98      inference(unflattening,[status(thm)],[c_280]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_394,plain,
% 1.44/0.98      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0) ),
% 1.44/0.98      inference(subtyping,[status(esa)],[c_281]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_540,plain,
% 1.44/0.98      ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
% 1.44/0.98      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.44/0.98      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_575,plain,
% 1.44/0.98      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
% 1.44/0.98      | m1_subset_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.44/0.98      inference(light_normalisation,[status(thm)],[c_540,c_396]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_941,plain,
% 1.44/0.98      ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) != k2_struct_0(sK0)
% 1.44/0.98      | m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.44/0.98      inference(demodulation,[status(thm)],[c_575,c_807]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_0,plain,
% 1.44/0.98      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 1.44/0.98      inference(cnf_transformation,[],[f25]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_401,plain,
% 1.44/0.98      ( k2_tarski(X0_44,X1_44) = k2_tarski(X1_44,X0_44) ),
% 1.44/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_11,negated_conjecture,
% 1.44/0.98      ( v1_tops_1(sK1,sK0) ),
% 1.44/0.98      inference(cnf_transformation,[],[f38]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_7,plain,
% 1.44/0.98      ( ~ v3_pre_topc(X0,X1)
% 1.44/0.98      | ~ v1_tops_1(X2,X1)
% 1.44/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.44/0.98      | ~ v2_pre_topc(X1)
% 1.44/0.98      | ~ l1_pre_topc(X1)
% 1.44/0.98      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0) ),
% 1.44/0.98      inference(cnf_transformation,[],[f33]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_9,negated_conjecture,
% 1.44/0.98      ( v3_pre_topc(sK2,sK0) ),
% 1.44/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_182,plain,
% 1.44/0.98      ( ~ v1_tops_1(X0,X1)
% 1.44/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.44/0.98      | ~ v2_pre_topc(X1)
% 1.44/0.98      | ~ l1_pre_topc(X1)
% 1.44/0.98      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X0)) = k2_pre_topc(X1,X2)
% 1.44/0.98      | sK2 != X2
% 1.44/0.98      | sK0 != X1 ),
% 1.44/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_9]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_183,plain,
% 1.44/0.98      ( ~ v1_tops_1(X0,sK0)
% 1.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | ~ v2_pre_topc(sK0)
% 1.44/0.98      | ~ l1_pre_topc(sK0)
% 1.44/0.98      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
% 1.44/0.98      inference(unflattening,[status(thm)],[c_182]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_15,negated_conjecture,
% 1.44/0.98      ( v2_pre_topc(sK0) ),
% 1.44/0.98      inference(cnf_transformation,[],[f34]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_187,plain,
% 1.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | ~ v1_tops_1(X0,sK0)
% 1.44/0.98      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
% 1.44/0.98      inference(global_propositional_subsumption,
% 1.44/0.98                [status(thm)],
% 1.44/0.98                [c_183,c_15,c_14,c_12]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_188,plain,
% 1.44/0.98      ( ~ v1_tops_1(X0,sK0)
% 1.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
% 1.44/0.98      inference(renaming,[status(thm)],[c_187]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_314,plain,
% 1.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2)
% 1.44/0.98      | sK1 != X0
% 1.44/0.98      | sK0 != sK0 ),
% 1.44/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_188]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_315,plain,
% 1.44/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
% 1.44/0.98      inference(unflattening,[status(thm)],[c_314]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_13,negated_conjecture,
% 1.44/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.44/0.98      inference(cnf_transformation,[],[f36]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_317,plain,
% 1.44/0.98      ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
% 1.44/0.98      inference(global_propositional_subsumption,[status(thm)],[c_315,c_13]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_390,plain,
% 1.44/0.98      ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
% 1.44/0.98      inference(subtyping,[status(esa)],[c_317]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_10,negated_conjecture,
% 1.44/0.98      ( v1_tops_1(sK2,sK0) ),
% 1.44/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_6,plain,
% 1.44/0.98      ( ~ v1_tops_1(X0,X1)
% 1.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.44/0.98      | ~ l1_pre_topc(X1)
% 1.44/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 1.44/0.98      inference(cnf_transformation,[],[f31]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_212,plain,
% 1.44/0.98      ( ~ v1_tops_1(X0,X1)
% 1.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.44/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 1.44/0.98      | sK0 != X1 ),
% 1.44/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_213,plain,
% 1.44/0.98      ( ~ v1_tops_1(X0,sK0)
% 1.44/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 1.44/0.98      inference(unflattening,[status(thm)],[c_212]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_290,plain,
% 1.44/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 1.44/0.98      | sK2 != X0
% 1.44/0.98      | sK0 != sK0 ),
% 1.44/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_213]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_291,plain,
% 1.44/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.44/0.98      | k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
% 1.44/0.98      inference(unflattening,[status(thm)],[c_290]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_293,plain,
% 1.44/0.98      ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
% 1.44/0.98      inference(global_propositional_subsumption,[status(thm)],[c_291,c_12]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_393,plain,
% 1.44/0.98      ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
% 1.44/0.98      inference(subtyping,[status(esa)],[c_293]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_564,plain,
% 1.44/0.98      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_struct_0(sK0) ),
% 1.44/0.98      inference(light_normalisation,[status(thm)],[c_390,c_393,c_396]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_397,negated_conjecture,
% 1.44/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.44/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_538,plain,
% 1.44/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.44/0.98      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_552,plain,
% 1.44/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 1.44/0.98      inference(light_normalisation,[status(thm)],[c_538,c_396]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_808,plain,
% 1.44/0.98      ( k9_subset_1(k2_struct_0(sK0),X0_44,sK1) = k1_setfam_1(k2_tarski(X0_44,sK1)) ),
% 1.44/0.98      inference(superposition,[status(thm)],[c_552,c_536]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_891,plain,
% 1.44/0.98      ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) = k2_struct_0(sK0) ),
% 1.44/0.98      inference(demodulation,[status(thm)],[c_564,c_808]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_893,plain,
% 1.44/0.98      ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_struct_0(sK0) ),
% 1.44/0.98      inference(superposition,[status(thm)],[c_401,c_891]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_945,plain,
% 1.44/0.98      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.44/0.98      inference(global_propositional_subsumption,[status(thm)],[c_941,c_893]) ).
% 1.44/0.98  
% 1.44/0.98  cnf(c_1360,plain,
% 1.44/0.98      ( $false ),
% 1.44/0.98      inference(superposition,[status(thm)],[c_1349,c_945]) ).
% 1.44/0.98  
% 1.44/0.98  
% 1.44/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.44/0.98  
% 1.44/0.98  ------                               Statistics
% 1.44/0.98  
% 1.44/0.98  ------ General
% 1.44/0.98  
% 1.44/0.98  abstr_ref_over_cycles:                  0
% 1.44/0.98  abstr_ref_under_cycles:                 0
% 1.44/0.98  gc_basic_clause_elim:                   0
% 1.44/0.98  forced_gc_time:                         0
% 1.44/0.98  parsing_time:                           0.01
% 1.44/0.98  unif_index_cands_time:                  0.
% 1.44/0.98  unif_index_add_time:                    0.
% 1.44/0.98  orderings_time:                         0.
% 1.44/0.98  out_proof_time:                         0.013
% 1.44/0.98  total_time:                             0.084
% 1.44/0.98  num_of_symbols:                         49
% 1.44/0.98  num_of_terms:                           1563
% 1.44/0.98  
% 1.44/0.98  ------ Preprocessing
% 1.44/0.98  
% 1.44/0.98  num_of_splits:                          0
% 1.44/0.98  num_of_split_atoms:                     0
% 1.44/0.98  num_of_reused_defs:                     0
% 1.44/0.98  num_eq_ax_congr_red:                    12
% 1.44/0.98  num_of_sem_filtered_clauses:            1
% 1.44/0.98  num_of_subtypes:                        5
% 1.44/0.98  monotx_restored_types:                  0
% 1.44/0.98  sat_num_of_epr_types:                   0
% 1.44/0.98  sat_num_of_non_cyclic_types:            0
% 1.44/0.98  sat_guarded_non_collapsed_types:        0
% 1.44/0.98  num_pure_diseq_elim:                    0
% 1.44/0.98  simp_replaced_by:                       0
% 1.44/0.98  res_preprocessed:                       83
% 1.44/0.98  prep_upred:                             0
% 1.44/0.98  prep_unflattend:                        10
% 1.44/0.98  smt_new_axioms:                         0
% 1.44/0.98  pred_elim_cands:                        1
% 1.44/0.98  pred_elim:                              5
% 1.44/0.98  pred_elim_cl:                           2
% 1.44/0.98  pred_elim_cycles:                       7
% 1.44/0.98  merged_defs:                            0
% 1.44/0.98  merged_defs_ncl:                        0
% 1.44/0.98  bin_hyper_res:                          0
% 1.44/0.98  prep_cycles:                            4
% 1.44/0.98  pred_elim_time:                         0.004
% 1.44/0.98  splitting_time:                         0.
% 1.44/0.98  sem_filter_time:                        0.
% 1.44/0.98  monotx_time:                            0.
% 1.44/0.98  subtype_inf_time:                       0.
% 1.44/0.98  
% 1.44/0.98  ------ Problem properties
% 1.44/0.98  
% 1.44/0.98  clauses:                                14
% 1.44/0.98  conjectures:                            2
% 1.44/0.98  epr:                                    0
% 1.44/0.98  horn:                                   14
% 1.44/0.98  ground:                                 10
% 1.44/0.98  unary:                                  10
% 1.44/0.98  binary:                                 3
% 1.44/0.98  lits:                                   19
% 1.44/0.98  lits_eq:                                12
% 1.44/0.98  fd_pure:                                0
% 1.44/0.98  fd_pseudo:                              0
% 1.44/0.98  fd_cond:                                0
% 1.44/0.98  fd_pseudo_cond:                         0
% 1.44/0.98  ac_symbols:                             0
% 1.44/0.98  
% 1.44/0.98  ------ Propositional Solver
% 1.44/0.98  
% 1.44/0.98  prop_solver_calls:                      28
% 1.44/0.98  prop_fast_solver_calls:                 368
% 1.44/0.98  smt_solver_calls:                       0
% 1.44/0.98  smt_fast_solver_calls:                  0
% 1.44/0.98  prop_num_of_clauses:                    545
% 1.44/0.98  prop_preprocess_simplified:             1991
% 1.44/0.98  prop_fo_subsumed:                       11
% 1.44/0.98  prop_solver_time:                       0.
% 1.44/0.98  smt_solver_time:                        0.
% 1.44/0.98  smt_fast_solver_time:                   0.
% 1.44/0.98  prop_fast_solver_time:                  0.
% 1.44/0.98  prop_unsat_core_time:                   0.
% 1.44/0.98  
% 1.44/0.98  ------ QBF
% 1.44/0.98  
% 1.44/0.98  qbf_q_res:                              0
% 1.44/0.98  qbf_num_tautologies:                    0
% 1.44/0.98  qbf_prep_cycles:                        0
% 1.44/0.98  
% 1.44/0.98  ------ BMC1
% 1.44/0.98  
% 1.44/0.98  bmc1_current_bound:                     -1
% 1.44/0.98  bmc1_last_solved_bound:                 -1
% 1.44/0.98  bmc1_unsat_core_size:                   -1
% 1.44/0.98  bmc1_unsat_core_parents_size:           -1
% 1.44/0.98  bmc1_merge_next_fun:                    0
% 1.44/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.44/0.98  
% 1.44/0.98  ------ Instantiation
% 1.44/0.98  
% 1.44/0.98  inst_num_of_clauses:                    209
% 1.44/0.98  inst_num_in_passive:                    41
% 1.44/0.98  inst_num_in_active:                     123
% 1.44/0.98  inst_num_in_unprocessed:                45
% 1.44/0.98  inst_num_of_loops:                      130
% 1.44/0.98  inst_num_of_learning_restarts:          0
% 1.44/0.98  inst_num_moves_active_passive:          3
% 1.44/0.98  inst_lit_activity:                      0
% 1.44/0.98  inst_lit_activity_moves:                0
% 1.44/0.98  inst_num_tautologies:                   0
% 1.44/0.98  inst_num_prop_implied:                  0
% 1.44/0.98  inst_num_existing_simplified:           0
% 1.44/0.98  inst_num_eq_res_simplified:             0
% 1.44/0.98  inst_num_child_elim:                    0
% 1.44/0.98  inst_num_of_dismatching_blockings:      29
% 1.44/0.98  inst_num_of_non_proper_insts:           177
% 1.44/0.98  inst_num_of_duplicates:                 0
% 1.44/0.98  inst_inst_num_from_inst_to_res:         0
% 1.44/0.98  inst_dismatching_checking_time:         0.
% 1.44/0.98  
% 1.44/0.98  ------ Resolution
% 1.44/0.98  
% 1.44/0.98  res_num_of_clauses:                     0
% 1.44/0.98  res_num_in_passive:                     0
% 1.44/0.98  res_num_in_active:                      0
% 1.44/0.98  res_num_of_loops:                       87
% 1.44/0.98  res_forward_subset_subsumed:            28
% 1.44/0.98  res_backward_subset_subsumed:           0
% 1.44/0.98  res_forward_subsumed:                   0
% 1.44/0.98  res_backward_subsumed:                  0
% 1.44/0.98  res_forward_subsumption_resolution:     0
% 1.44/0.98  res_backward_subsumption_resolution:    0
% 1.44/0.98  res_clause_to_clause_subsumption:       46
% 1.44/0.98  res_orphan_elimination:                 0
% 1.44/0.98  res_tautology_del:                      33
% 1.44/0.98  res_num_eq_res_simplified:              2
% 1.44/0.98  res_num_sel_changes:                    0
% 1.44/0.98  res_moves_from_active_to_pass:          0
% 1.44/0.98  
% 1.44/0.98  ------ Superposition
% 1.44/0.98  
% 1.44/0.98  sup_time_total:                         0.
% 1.44/0.98  sup_time_generating:                    0.
% 1.44/0.98  sup_time_sim_full:                      0.
% 1.44/0.98  sup_time_sim_immed:                     0.
% 1.44/0.98  
% 1.44/0.98  sup_num_of_clauses:                     29
% 1.44/0.98  sup_num_in_active:                      22
% 1.44/0.98  sup_num_in_passive:                     7
% 1.44/0.98  sup_num_of_loops:                       24
% 1.44/0.98  sup_fw_superposition:                   15
% 1.44/0.98  sup_bw_superposition:                   9
% 1.44/0.98  sup_immediate_simplified:               6
% 1.44/0.98  sup_given_eliminated:                   0
% 1.44/0.98  comparisons_done:                       0
% 1.44/0.98  comparisons_avoided:                    0
% 1.44/0.98  
% 1.44/0.98  ------ Simplifications
% 1.44/0.98  
% 1.44/0.98  
% 1.44/0.98  sim_fw_subset_subsumed:                 2
% 1.44/0.98  sim_bw_subset_subsumed:                 0
% 1.44/0.98  sim_fw_subsumed:                        0
% 1.44/0.98  sim_bw_subsumed:                        0
% 1.44/0.98  sim_fw_subsumption_res:                 0
% 1.44/0.98  sim_bw_subsumption_res:                 0
% 1.44/0.98  sim_tautology_del:                      0
% 1.44/0.98  sim_eq_tautology_del:                   1
% 1.44/0.98  sim_eq_res_simp:                        0
% 1.44/0.98  sim_fw_demodulated:                     6
% 1.44/0.98  sim_bw_demodulated:                     3
% 1.44/0.98  sim_light_normalised:                   8
% 1.44/0.98  sim_joinable_taut:                      0
% 1.44/0.98  sim_joinable_simp:                      0
% 1.44/0.98  sim_ac_normalised:                      0
% 1.44/0.98  sim_smt_subsumption:                    0
% 1.44/0.98  
%------------------------------------------------------------------------------
