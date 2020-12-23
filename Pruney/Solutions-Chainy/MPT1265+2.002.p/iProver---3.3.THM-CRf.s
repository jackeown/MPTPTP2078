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
% DateTime   : Thu Dec  3 12:14:56 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 734 expanded)
%              Number of clauses        :   90 ( 239 expanded)
%              Number of leaves         :   14 ( 204 expanded)
%              Depth                    :   21
%              Number of atoms          :  388 (4052 expanded)
%              Number of equality atoms :  143 ( 322 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f19])).

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f23,plain,
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

fof(f26,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f25,f24,f23])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f30])).

cnf(c_1,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_620,plain,
    ( k2_tarski(X0_45,X1_45) = k2_tarski(X1_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_128,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_129,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_128])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_414,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_129,c_15])).

cnf(c_415,plain,
    ( r1_tarski(sK1,X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_612,plain,
    ( r1_tarski(sK1,X0_46)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_415])).

cnf(c_765,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | r1_tarski(sK1,X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_232,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_271,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_232,c_16])).

cnf(c_272,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_618,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_272])).

cnf(c_793,plain,
    ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | r1_tarski(sK1,X0_46) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_765,c_618])).

cnf(c_1164,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_793])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_130,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_131,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_130])).

cnf(c_162,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_131])).

cnf(c_619,plain,
    ( ~ r1_tarski(X0_45,X0_46)
    | k9_subset_1(X0_46,X1_45,X0_45) = k1_setfam_1(k2_tarski(X1_45,X0_45)) ),
    inference(subtyping,[status(esa)],[c_162])).

cnf(c_763,plain,
    ( k9_subset_1(X0_46,X0_45,X1_45) = k1_setfam_1(k2_tarski(X0_45,X1_45))
    | r1_tarski(X1_45,X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_1307,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0_45,sK1) = k1_setfam_1(k2_tarski(X0_45,sK1)) ),
    inference(superposition,[status(thm)],[c_1164,c_763])).

cnf(c_13,negated_conjecture,
    ( v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v1_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,negated_conjecture,
    ( v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_246,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X0)) = k2_pre_topc(X1,X2)
    | sK2 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_247,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_1(X0,sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_247,c_17,c_16,c_14])).

cnf(c_252,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
    inference(renaming,[status(thm)],[c_251])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_252])).

cnf(c_379,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_381,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_379,c_15])).

cnf(c_614,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_381])).

cnf(c_12,negated_conjecture,
    ( v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_276,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_277,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_277])).

cnf(c_355,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_357,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_14])).

cnf(c_617,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_357])).

cnf(c_785,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_614,c_617,c_618])).

cnf(c_1880,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1307,c_785])).

cnf(c_1893,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_620,c_1880])).

cnf(c_7,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_291,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_292,plain,
    ( v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
    inference(resolution,[status(thm)],[c_292,c_252])).

cnf(c_426,plain,
    ( ~ r1_tarski(X0,X1)
    | X2 != X0
    | k2_pre_topc(sK0,X2) != k2_struct_0(sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X2)) = k2_pre_topc(sK0,sK2)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1) ),
    inference(resolution_lifted,[status(thm)],[c_131,c_316])).

cnf(c_427,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_611,plain,
    ( ~ r1_tarski(X0_45,X0_46)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | k2_pre_topc(sK0,X0_45) != k2_struct_0(sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0_45)) = k2_pre_topc(sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_427])).

cnf(c_766,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | k2_pre_topc(sK0,X0_45) != k2_struct_0(sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0_45)) = k2_pre_topc(sK0,sK2)
    | r1_tarski(X0_45,X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_813,plain,
    ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | k2_pre_topc(sK0,X0_45) != k2_struct_0(sK0)
    | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0_45)) = k2_struct_0(sK0)
    | r1_tarski(X0_45,X0_46) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_766,c_617,c_618])).

cnf(c_1950,plain,
    ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k1_setfam_1(k2_tarski(sK1,sK2)))) = k2_struct_0(sK0)
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_813])).

cnf(c_402,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_129,c_14])).

cnf(c_403,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_613,plain,
    ( r1_tarski(sK2,X0_46)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_403])).

cnf(c_764,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | r1_tarski(sK2,X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_788,plain,
    ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | r1_tarski(sK2,X0_46) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_764,c_618])).

cnf(c_931,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_788])).

cnf(c_1297,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0_45,sK2) = k1_setfam_1(k2_tarski(X0_45,sK2)) ),
    inference(superposition,[status(thm)],[c_931,c_763])).

cnf(c_10,negated_conjecture,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_292])).

cnf(c_345,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_444,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1) ),
    inference(resolution_lifted,[status(thm)],[c_131,c_345])).

cnf(c_445,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_610,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0_46)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_445])).

cnf(c_767,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_806,plain,
    ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
    | r1_tarski(k9_subset_1(k2_struct_0(sK0),sK1,sK2),X0_46) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_767,c_618])).

cnf(c_1416,plain,
    ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) != k2_struct_0(sK0)
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),X0_46) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1297,c_806])).

cnf(c_1955,plain,
    ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1950,c_1416,c_1893])).

cnf(c_1963,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),k2_struct_0(sK0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1955])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_621,plain,
    ( ~ r1_tarski(X0_45,X0_46)
    | r1_tarski(k1_setfam_1(k2_tarski(X0_45,X1_45)),X0_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_948,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0_45)),k2_struct_0(sK0))
    | ~ r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_949,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0_45)),k2_struct_0(sK0)) = iProver_top
    | r1_tarski(sK1,k2_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_951,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),k2_struct_0(sK0)) = iProver_top
    | r1_tarski(sK1,k2_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_916,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(k2_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_917,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(k2_struct_0(sK0))
    | r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_916])).

cnf(c_634,plain,
    ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46)
    | X0_46 != X1_46 ),
    theory(equality)).

cnf(c_852,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(X0_46)
    | u1_struct_0(sK0) != X0_46 ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_894,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(k2_struct_0(sK0))
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1963,c_951,c_917,c_894,c_618])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:28:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.41/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/0.98  
% 2.41/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/0.98  
% 2.41/0.98  ------  iProver source info
% 2.41/0.98  
% 2.41/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.41/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/0.98  git: non_committed_changes: false
% 2.41/0.98  git: last_make_outside_of_git: false
% 2.41/0.98  
% 2.41/0.98  ------ 
% 2.41/0.98  
% 2.41/0.98  ------ Input Options
% 2.41/0.98  
% 2.41/0.98  --out_options                           all
% 2.41/0.98  --tptp_safe_out                         true
% 2.41/0.98  --problem_path                          ""
% 2.41/0.98  --include_path                          ""
% 2.41/0.98  --clausifier                            res/vclausify_rel
% 2.41/0.98  --clausifier_options                    --mode clausify
% 2.41/0.98  --stdin                                 false
% 2.41/0.98  --stats_out                             all
% 2.41/0.98  
% 2.41/0.98  ------ General Options
% 2.41/0.98  
% 2.41/0.98  --fof                                   false
% 2.41/0.98  --time_out_real                         305.
% 2.41/0.98  --time_out_virtual                      -1.
% 2.41/0.98  --symbol_type_check                     false
% 2.41/0.98  --clausify_out                          false
% 2.41/0.98  --sig_cnt_out                           false
% 2.41/0.98  --trig_cnt_out                          false
% 2.41/0.98  --trig_cnt_out_tolerance                1.
% 2.41/0.98  --trig_cnt_out_sk_spl                   false
% 2.41/0.98  --abstr_cl_out                          false
% 2.41/0.98  
% 2.41/0.98  ------ Global Options
% 2.41/0.98  
% 2.41/0.98  --schedule                              default
% 2.41/0.98  --add_important_lit                     false
% 2.41/0.98  --prop_solver_per_cl                    1000
% 2.41/0.98  --min_unsat_core                        false
% 2.41/0.98  --soft_assumptions                      false
% 2.41/0.98  --soft_lemma_size                       3
% 2.41/0.98  --prop_impl_unit_size                   0
% 2.41/0.98  --prop_impl_unit                        []
% 2.41/0.98  --share_sel_clauses                     true
% 2.41/0.98  --reset_solvers                         false
% 2.41/0.98  --bc_imp_inh                            [conj_cone]
% 2.41/0.98  --conj_cone_tolerance                   3.
% 2.41/0.98  --extra_neg_conj                        none
% 2.41/0.98  --large_theory_mode                     true
% 2.41/0.98  --prolific_symb_bound                   200
% 2.41/0.98  --lt_threshold                          2000
% 2.41/0.98  --clause_weak_htbl                      true
% 2.41/0.98  --gc_record_bc_elim                     false
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing Options
% 2.41/0.98  
% 2.41/0.98  --preprocessing_flag                    true
% 2.41/0.98  --time_out_prep_mult                    0.1
% 2.41/0.98  --splitting_mode                        input
% 2.41/0.98  --splitting_grd                         true
% 2.41/0.98  --splitting_cvd                         false
% 2.41/0.98  --splitting_cvd_svl                     false
% 2.41/0.98  --splitting_nvd                         32
% 2.41/0.98  --sub_typing                            true
% 2.41/0.98  --prep_gs_sim                           true
% 2.41/0.98  --prep_unflatten                        true
% 2.41/0.98  --prep_res_sim                          true
% 2.41/0.98  --prep_upred                            true
% 2.41/0.98  --prep_sem_filter                       exhaustive
% 2.41/0.98  --prep_sem_filter_out                   false
% 2.41/0.98  --pred_elim                             true
% 2.41/0.98  --res_sim_input                         true
% 2.41/0.98  --eq_ax_congr_red                       true
% 2.41/0.98  --pure_diseq_elim                       true
% 2.41/0.98  --brand_transform                       false
% 2.41/0.98  --non_eq_to_eq                          false
% 2.41/0.98  --prep_def_merge                        true
% 2.41/0.98  --prep_def_merge_prop_impl              false
% 2.41/0.98  --prep_def_merge_mbd                    true
% 2.41/0.98  --prep_def_merge_tr_red                 false
% 2.41/0.98  --prep_def_merge_tr_cl                  false
% 2.41/0.98  --smt_preprocessing                     true
% 2.41/0.98  --smt_ac_axioms                         fast
% 2.41/0.98  --preprocessed_out                      false
% 2.41/0.98  --preprocessed_stats                    false
% 2.41/0.98  
% 2.41/0.98  ------ Abstraction refinement Options
% 2.41/0.98  
% 2.41/0.98  --abstr_ref                             []
% 2.41/0.98  --abstr_ref_prep                        false
% 2.41/0.98  --abstr_ref_until_sat                   false
% 2.41/0.98  --abstr_ref_sig_restrict                funpre
% 2.41/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/0.98  --abstr_ref_under                       []
% 2.41/0.98  
% 2.41/0.98  ------ SAT Options
% 2.41/0.98  
% 2.41/0.98  --sat_mode                              false
% 2.41/0.98  --sat_fm_restart_options                ""
% 2.41/0.98  --sat_gr_def                            false
% 2.41/0.98  --sat_epr_types                         true
% 2.41/0.98  --sat_non_cyclic_types                  false
% 2.41/0.98  --sat_finite_models                     false
% 2.41/0.98  --sat_fm_lemmas                         false
% 2.41/0.98  --sat_fm_prep                           false
% 2.41/0.98  --sat_fm_uc_incr                        true
% 2.41/0.98  --sat_out_model                         small
% 2.41/0.98  --sat_out_clauses                       false
% 2.41/0.98  
% 2.41/0.98  ------ QBF Options
% 2.41/0.98  
% 2.41/0.98  --qbf_mode                              false
% 2.41/0.98  --qbf_elim_univ                         false
% 2.41/0.98  --qbf_dom_inst                          none
% 2.41/0.98  --qbf_dom_pre_inst                      false
% 2.41/0.98  --qbf_sk_in                             false
% 2.41/0.98  --qbf_pred_elim                         true
% 2.41/0.98  --qbf_split                             512
% 2.41/0.98  
% 2.41/0.98  ------ BMC1 Options
% 2.41/0.98  
% 2.41/0.98  --bmc1_incremental                      false
% 2.41/0.98  --bmc1_axioms                           reachable_all
% 2.41/0.98  --bmc1_min_bound                        0
% 2.41/0.98  --bmc1_max_bound                        -1
% 2.41/0.98  --bmc1_max_bound_default                -1
% 2.41/0.98  --bmc1_symbol_reachability              true
% 2.41/0.98  --bmc1_property_lemmas                  false
% 2.41/0.98  --bmc1_k_induction                      false
% 2.41/0.98  --bmc1_non_equiv_states                 false
% 2.41/0.98  --bmc1_deadlock                         false
% 2.41/0.98  --bmc1_ucm                              false
% 2.41/0.98  --bmc1_add_unsat_core                   none
% 2.41/0.98  --bmc1_unsat_core_children              false
% 2.41/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/0.98  --bmc1_out_stat                         full
% 2.41/0.98  --bmc1_ground_init                      false
% 2.41/0.98  --bmc1_pre_inst_next_state              false
% 2.41/0.98  --bmc1_pre_inst_state                   false
% 2.41/0.98  --bmc1_pre_inst_reach_state             false
% 2.41/0.98  --bmc1_out_unsat_core                   false
% 2.41/0.98  --bmc1_aig_witness_out                  false
% 2.41/0.98  --bmc1_verbose                          false
% 2.41/0.98  --bmc1_dump_clauses_tptp                false
% 2.41/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.41/0.98  --bmc1_dump_file                        -
% 2.41/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.41/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.41/0.98  --bmc1_ucm_extend_mode                  1
% 2.41/0.98  --bmc1_ucm_init_mode                    2
% 2.41/0.98  --bmc1_ucm_cone_mode                    none
% 2.41/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.41/0.98  --bmc1_ucm_relax_model                  4
% 2.41/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.41/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/0.98  --bmc1_ucm_layered_model                none
% 2.41/0.98  --bmc1_ucm_max_lemma_size               10
% 2.41/0.98  
% 2.41/0.98  ------ AIG Options
% 2.41/0.98  
% 2.41/0.98  --aig_mode                              false
% 2.41/0.98  
% 2.41/0.98  ------ Instantiation Options
% 2.41/0.98  
% 2.41/0.98  --instantiation_flag                    true
% 2.41/0.98  --inst_sos_flag                         false
% 2.41/0.98  --inst_sos_phase                        true
% 2.41/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/0.98  --inst_lit_sel_side                     num_symb
% 2.41/0.98  --inst_solver_per_active                1400
% 2.41/0.98  --inst_solver_calls_frac                1.
% 2.41/0.98  --inst_passive_queue_type               priority_queues
% 2.41/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/0.98  --inst_passive_queues_freq              [25;2]
% 2.41/0.98  --inst_dismatching                      true
% 2.41/0.98  --inst_eager_unprocessed_to_passive     true
% 2.41/0.98  --inst_prop_sim_given                   true
% 2.41/0.98  --inst_prop_sim_new                     false
% 2.41/0.98  --inst_subs_new                         false
% 2.41/0.98  --inst_eq_res_simp                      false
% 2.41/0.98  --inst_subs_given                       false
% 2.41/0.98  --inst_orphan_elimination               true
% 2.41/0.98  --inst_learning_loop_flag               true
% 2.41/0.98  --inst_learning_start                   3000
% 2.41/0.98  --inst_learning_factor                  2
% 2.41/0.98  --inst_start_prop_sim_after_learn       3
% 2.41/0.98  --inst_sel_renew                        solver
% 2.41/0.98  --inst_lit_activity_flag                true
% 2.41/0.98  --inst_restr_to_given                   false
% 2.41/0.98  --inst_activity_threshold               500
% 2.41/0.98  --inst_out_proof                        true
% 2.41/0.98  
% 2.41/0.98  ------ Resolution Options
% 2.41/0.98  
% 2.41/0.98  --resolution_flag                       true
% 2.41/0.98  --res_lit_sel                           adaptive
% 2.41/0.98  --res_lit_sel_side                      none
% 2.41/0.98  --res_ordering                          kbo
% 2.41/0.98  --res_to_prop_solver                    active
% 2.41/0.98  --res_prop_simpl_new                    false
% 2.41/0.98  --res_prop_simpl_given                  true
% 2.41/0.98  --res_passive_queue_type                priority_queues
% 2.41/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/0.98  --res_passive_queues_freq               [15;5]
% 2.41/0.98  --res_forward_subs                      full
% 2.41/0.98  --res_backward_subs                     full
% 2.41/0.98  --res_forward_subs_resolution           true
% 2.41/0.98  --res_backward_subs_resolution          true
% 2.41/0.98  --res_orphan_elimination                true
% 2.41/0.98  --res_time_limit                        2.
% 2.41/0.98  --res_out_proof                         true
% 2.41/0.98  
% 2.41/0.98  ------ Superposition Options
% 2.41/0.98  
% 2.41/0.98  --superposition_flag                    true
% 2.41/0.98  --sup_passive_queue_type                priority_queues
% 2.41/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.41/0.98  --demod_completeness_check              fast
% 2.41/0.98  --demod_use_ground                      true
% 2.41/0.98  --sup_to_prop_solver                    passive
% 2.41/0.98  --sup_prop_simpl_new                    true
% 2.41/0.98  --sup_prop_simpl_given                  true
% 2.41/0.98  --sup_fun_splitting                     false
% 2.41/0.98  --sup_smt_interval                      50000
% 2.41/0.98  
% 2.41/0.98  ------ Superposition Simplification Setup
% 2.41/0.98  
% 2.41/0.98  --sup_indices_passive                   []
% 2.41/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.98  --sup_full_bw                           [BwDemod]
% 2.41/0.98  --sup_immed_triv                        [TrivRules]
% 2.41/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.98  --sup_immed_bw_main                     []
% 2.41/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.98  
% 2.41/0.98  ------ Combination Options
% 2.41/0.98  
% 2.41/0.98  --comb_res_mult                         3
% 2.41/0.98  --comb_sup_mult                         2
% 2.41/0.98  --comb_inst_mult                        10
% 2.41/0.98  
% 2.41/0.98  ------ Debug Options
% 2.41/0.98  
% 2.41/0.98  --dbg_backtrace                         false
% 2.41/0.98  --dbg_dump_prop_clauses                 false
% 2.41/0.98  --dbg_dump_prop_clauses_file            -
% 2.41/0.98  --dbg_out_stat                          false
% 2.41/0.98  ------ Parsing...
% 2.41/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.41/0.98  ------ Proving...
% 2.41/0.98  ------ Problem Properties 
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  clauses                                 14
% 2.41/0.98  conjectures                             0
% 2.41/0.98  EPR                                     0
% 2.41/0.98  Horn                                    14
% 2.41/0.98  unary                                   8
% 2.41/0.98  binary                                  4
% 2.41/0.98  lits                                    23
% 2.41/0.98  lits eq                                 16
% 2.41/0.98  fd_pure                                 0
% 2.41/0.98  fd_pseudo                               0
% 2.41/0.98  fd_cond                                 0
% 2.41/0.98  fd_pseudo_cond                          0
% 2.41/0.98  AC symbols                              0
% 2.41/0.98  
% 2.41/0.98  ------ Schedule dynamic 5 is on 
% 2.41/0.98  
% 2.41/0.98  ------ no conjectures: strip conj schedule 
% 2.41/0.98  
% 2.41/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.41/0.98  
% 2.41/0.98  
% 2.41/0.98  ------ 
% 2.41/0.98  Current options:
% 2.41/0.98  ------ 
% 2.41/0.98  
% 2.41/0.98  ------ Input Options
% 2.41/0.98  
% 2.41/0.98  --out_options                           all
% 2.41/0.98  --tptp_safe_out                         true
% 2.41/0.98  --problem_path                          ""
% 2.41/0.98  --include_path                          ""
% 2.41/0.98  --clausifier                            res/vclausify_rel
% 2.41/0.98  --clausifier_options                    --mode clausify
% 2.41/0.98  --stdin                                 false
% 2.41/0.98  --stats_out                             all
% 2.41/0.98  
% 2.41/0.98  ------ General Options
% 2.41/0.98  
% 2.41/0.98  --fof                                   false
% 2.41/0.98  --time_out_real                         305.
% 2.41/0.98  --time_out_virtual                      -1.
% 2.41/0.98  --symbol_type_check                     false
% 2.41/0.98  --clausify_out                          false
% 2.41/0.98  --sig_cnt_out                           false
% 2.41/0.98  --trig_cnt_out                          false
% 2.41/0.98  --trig_cnt_out_tolerance                1.
% 2.41/0.98  --trig_cnt_out_sk_spl                   false
% 2.41/0.98  --abstr_cl_out                          false
% 2.41/0.98  
% 2.41/0.98  ------ Global Options
% 2.41/0.98  
% 2.41/0.98  --schedule                              default
% 2.41/0.98  --add_important_lit                     false
% 2.41/0.98  --prop_solver_per_cl                    1000
% 2.41/0.98  --min_unsat_core                        false
% 2.41/0.98  --soft_assumptions                      false
% 2.41/0.98  --soft_lemma_size                       3
% 2.41/0.98  --prop_impl_unit_size                   0
% 2.41/0.98  --prop_impl_unit                        []
% 2.41/0.98  --share_sel_clauses                     true
% 2.41/0.98  --reset_solvers                         false
% 2.41/0.98  --bc_imp_inh                            [conj_cone]
% 2.41/0.98  --conj_cone_tolerance                   3.
% 2.41/0.98  --extra_neg_conj                        none
% 2.41/0.98  --large_theory_mode                     true
% 2.41/0.98  --prolific_symb_bound                   200
% 2.41/0.98  --lt_threshold                          2000
% 2.41/0.98  --clause_weak_htbl                      true
% 2.41/0.98  --gc_record_bc_elim                     false
% 2.41/0.98  
% 2.41/0.98  ------ Preprocessing Options
% 2.41/0.98  
% 2.41/0.98  --preprocessing_flag                    true
% 2.41/0.98  --time_out_prep_mult                    0.1
% 2.41/0.98  --splitting_mode                        input
% 2.41/0.98  --splitting_grd                         true
% 2.41/0.98  --splitting_cvd                         false
% 2.41/0.98  --splitting_cvd_svl                     false
% 2.41/0.98  --splitting_nvd                         32
% 2.41/0.98  --sub_typing                            true
% 2.41/0.98  --prep_gs_sim                           true
% 2.41/0.98  --prep_unflatten                        true
% 2.41/0.98  --prep_res_sim                          true
% 2.41/0.98  --prep_upred                            true
% 2.41/0.98  --prep_sem_filter                       exhaustive
% 2.41/0.98  --prep_sem_filter_out                   false
% 2.41/0.98  --pred_elim                             true
% 2.41/0.98  --res_sim_input                         true
% 2.41/0.98  --eq_ax_congr_red                       true
% 2.41/0.98  --pure_diseq_elim                       true
% 2.41/0.98  --brand_transform                       false
% 2.41/0.98  --non_eq_to_eq                          false
% 2.41/0.98  --prep_def_merge                        true
% 2.41/0.98  --prep_def_merge_prop_impl              false
% 2.41/0.98  --prep_def_merge_mbd                    true
% 2.41/0.98  --prep_def_merge_tr_red                 false
% 2.41/0.98  --prep_def_merge_tr_cl                  false
% 2.41/0.98  --smt_preprocessing                     true
% 2.41/0.98  --smt_ac_axioms                         fast
% 2.41/0.98  --preprocessed_out                      false
% 2.41/0.98  --preprocessed_stats                    false
% 2.41/0.98  
% 2.41/0.98  ------ Abstraction refinement Options
% 2.41/0.98  
% 2.41/0.98  --abstr_ref                             []
% 2.41/0.98  --abstr_ref_prep                        false
% 2.41/0.98  --abstr_ref_until_sat                   false
% 2.41/0.98  --abstr_ref_sig_restrict                funpre
% 2.41/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/0.98  --abstr_ref_under                       []
% 2.41/0.98  
% 2.41/0.98  ------ SAT Options
% 2.41/0.98  
% 2.41/0.98  --sat_mode                              false
% 2.41/0.98  --sat_fm_restart_options                ""
% 2.41/0.98  --sat_gr_def                            false
% 2.41/0.98  --sat_epr_types                         true
% 2.41/0.98  --sat_non_cyclic_types                  false
% 2.41/0.98  --sat_finite_models                     false
% 2.41/0.98  --sat_fm_lemmas                         false
% 2.41/0.98  --sat_fm_prep                           false
% 2.41/0.98  --sat_fm_uc_incr                        true
% 2.41/0.98  --sat_out_model                         small
% 2.41/0.98  --sat_out_clauses                       false
% 2.41/0.98  
% 2.41/0.98  ------ QBF Options
% 2.41/0.98  
% 2.41/0.98  --qbf_mode                              false
% 2.41/0.98  --qbf_elim_univ                         false
% 2.41/0.98  --qbf_dom_inst                          none
% 2.41/0.98  --qbf_dom_pre_inst                      false
% 2.41/0.98  --qbf_sk_in                             false
% 2.41/0.98  --qbf_pred_elim                         true
% 2.41/0.98  --qbf_split                             512
% 2.41/0.98  
% 2.41/0.98  ------ BMC1 Options
% 2.41/0.98  
% 2.41/0.98  --bmc1_incremental                      false
% 2.41/0.98  --bmc1_axioms                           reachable_all
% 2.41/0.98  --bmc1_min_bound                        0
% 2.41/0.98  --bmc1_max_bound                        -1
% 2.41/0.98  --bmc1_max_bound_default                -1
% 2.41/0.98  --bmc1_symbol_reachability              true
% 2.41/0.98  --bmc1_property_lemmas                  false
% 2.41/0.98  --bmc1_k_induction                      false
% 2.41/0.98  --bmc1_non_equiv_states                 false
% 2.41/0.98  --bmc1_deadlock                         false
% 2.41/0.98  --bmc1_ucm                              false
% 2.41/0.98  --bmc1_add_unsat_core                   none
% 2.41/0.98  --bmc1_unsat_core_children              false
% 2.41/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/0.98  --bmc1_out_stat                         full
% 2.41/0.98  --bmc1_ground_init                      false
% 2.41/0.98  --bmc1_pre_inst_next_state              false
% 2.41/0.98  --bmc1_pre_inst_state                   false
% 2.41/0.98  --bmc1_pre_inst_reach_state             false
% 2.41/0.98  --bmc1_out_unsat_core                   false
% 2.41/0.98  --bmc1_aig_witness_out                  false
% 2.41/0.98  --bmc1_verbose                          false
% 2.41/0.98  --bmc1_dump_clauses_tptp                false
% 2.41/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.41/0.98  --bmc1_dump_file                        -
% 2.41/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.41/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.41/0.98  --bmc1_ucm_extend_mode                  1
% 2.41/0.98  --bmc1_ucm_init_mode                    2
% 2.41/0.98  --bmc1_ucm_cone_mode                    none
% 2.41/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.41/0.98  --bmc1_ucm_relax_model                  4
% 2.41/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.41/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/0.98  --bmc1_ucm_layered_model                none
% 2.41/0.98  --bmc1_ucm_max_lemma_size               10
% 2.41/0.98  
% 2.41/0.98  ------ AIG Options
% 2.41/0.98  
% 2.41/0.98  --aig_mode                              false
% 2.41/0.98  
% 2.41/0.98  ------ Instantiation Options
% 2.41/0.98  
% 2.41/0.98  --instantiation_flag                    true
% 2.41/0.98  --inst_sos_flag                         false
% 2.41/0.98  --inst_sos_phase                        true
% 2.41/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/0.98  --inst_lit_sel_side                     none
% 2.41/0.98  --inst_solver_per_active                1400
% 2.41/0.98  --inst_solver_calls_frac                1.
% 2.41/0.98  --inst_passive_queue_type               priority_queues
% 2.41/0.98  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.41/0.98  --inst_passive_queues_freq              [25;2]
% 2.41/0.98  --inst_dismatching                      true
% 2.41/0.98  --inst_eager_unprocessed_to_passive     true
% 2.41/0.98  --inst_prop_sim_given                   true
% 2.41/0.98  --inst_prop_sim_new                     false
% 2.41/0.98  --inst_subs_new                         false
% 2.41/0.98  --inst_eq_res_simp                      false
% 2.41/0.98  --inst_subs_given                       false
% 2.41/0.98  --inst_orphan_elimination               true
% 2.41/0.98  --inst_learning_loop_flag               true
% 2.41/0.98  --inst_learning_start                   3000
% 2.41/0.98  --inst_learning_factor                  2
% 2.41/0.98  --inst_start_prop_sim_after_learn       3
% 2.41/0.98  --inst_sel_renew                        solver
% 2.41/0.98  --inst_lit_activity_flag                true
% 2.41/0.98  --inst_restr_to_given                   false
% 2.41/0.98  --inst_activity_threshold               500
% 2.41/0.98  --inst_out_proof                        true
% 2.41/0.98  
% 2.41/0.98  ------ Resolution Options
% 2.41/0.98  
% 2.41/0.98  --resolution_flag                       false
% 2.41/0.98  --res_lit_sel                           adaptive
% 2.41/0.98  --res_lit_sel_side                      none
% 2.41/0.98  --res_ordering                          kbo
% 2.41/0.98  --res_to_prop_solver                    active
% 2.41/0.98  --res_prop_simpl_new                    false
% 2.41/0.98  --res_prop_simpl_given                  true
% 2.41/0.98  --res_passive_queue_type                priority_queues
% 2.41/0.98  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.41/0.98  --res_passive_queues_freq               [15;5]
% 2.41/0.98  --res_forward_subs                      full
% 2.41/0.98  --res_backward_subs                     full
% 2.41/0.98  --res_forward_subs_resolution           true
% 2.41/0.98  --res_backward_subs_resolution          true
% 2.41/0.98  --res_orphan_elimination                true
% 2.41/0.98  --res_time_limit                        2.
% 2.41/0.98  --res_out_proof                         true
% 2.41/0.98  
% 2.41/0.98  ------ Superposition Options
% 2.41/0.98  
% 2.41/0.98  --superposition_flag                    true
% 2.41/0.98  --sup_passive_queue_type                priority_queues
% 2.41/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.41/0.99  --demod_completeness_check              fast
% 2.41/0.99  --demod_use_ground                      true
% 2.41/0.99  --sup_to_prop_solver                    passive
% 2.41/0.99  --sup_prop_simpl_new                    true
% 2.41/0.99  --sup_prop_simpl_given                  true
% 2.41/0.99  --sup_fun_splitting                     false
% 2.41/0.99  --sup_smt_interval                      50000
% 2.41/0.99  
% 2.41/0.99  ------ Superposition Simplification Setup
% 2.41/0.99  
% 2.41/0.99  --sup_indices_passive                   []
% 2.41/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_full_bw                           [BwDemod]
% 2.41/0.99  --sup_immed_triv                        [TrivRules]
% 2.41/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_immed_bw_main                     []
% 2.41/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/0.99  
% 2.41/0.99  ------ Combination Options
% 2.41/0.99  
% 2.41/0.99  --comb_res_mult                         3
% 2.41/0.99  --comb_sup_mult                         2
% 2.41/0.99  --comb_inst_mult                        10
% 2.41/0.99  
% 2.41/0.99  ------ Debug Options
% 2.41/0.99  
% 2.41/0.99  --dbg_backtrace                         false
% 2.41/0.99  --dbg_dump_prop_clauses                 false
% 2.41/0.99  --dbg_dump_prop_clauses_file            -
% 2.41/0.99  --dbg_out_stat                          false
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  ------ Proving...
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  % SZS status Theorem for theBenchmark.p
% 2.41/0.99  
% 2.41/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/0.99  
% 2.41/0.99  fof(f2,axiom,(
% 2.41/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f28,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f2])).
% 2.41/0.99  
% 2.41/0.99  fof(f5,axiom,(
% 2.41/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f21,plain,(
% 2.41/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.41/0.99    inference(nnf_transformation,[],[f5])).
% 2.41/0.99  
% 2.41/0.99  fof(f31,plain,(
% 2.41/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.41/0.99    inference(cnf_transformation,[],[f21])).
% 2.41/0.99  
% 2.41/0.99  fof(f10,conjecture,(
% 2.41/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f11,negated_conjecture,(
% 2.41/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 2.41/0.99    inference(negated_conjecture,[],[f10])).
% 2.41/0.99  
% 2.41/0.99  fof(f19,plain,(
% 2.41/0.99    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.41/0.99    inference(ennf_transformation,[],[f11])).
% 2.41/0.99  
% 2.41/0.99  fof(f20,plain,(
% 2.41/0.99    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.41/0.99    inference(flattening,[],[f19])).
% 2.41/0.99  
% 2.41/0.99  fof(f25,plain,(
% 2.41/0.99    ( ! [X0,X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v3_pre_topc(sK2,X0) & v1_tops_1(sK2,X0) & v1_tops_1(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.41/0.99    introduced(choice_axiom,[])).
% 2.41/0.99  
% 2.41/0.99  fof(f24,plain,(
% 2.41/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.41/0.99    introduced(choice_axiom,[])).
% 2.41/0.99  
% 2.41/0.99  fof(f23,plain,(
% 2.41/0.99    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.41/0.99    introduced(choice_axiom,[])).
% 2.41/0.99  
% 2.41/0.99  fof(f26,plain,(
% 2.41/0.99    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f25,f24,f23])).
% 2.41/0.99  
% 2.41/0.99  fof(f40,plain,(
% 2.41/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.41/0.99    inference(cnf_transformation,[],[f26])).
% 2.41/0.99  
% 2.41/0.99  fof(f7,axiom,(
% 2.41/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f15,plain,(
% 2.41/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.41/0.99    inference(ennf_transformation,[],[f7])).
% 2.41/0.99  
% 2.41/0.99  fof(f34,plain,(
% 2.41/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f15])).
% 2.41/0.99  
% 2.41/0.99  fof(f6,axiom,(
% 2.41/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f14,plain,(
% 2.41/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.41/0.99    inference(ennf_transformation,[],[f6])).
% 2.41/0.99  
% 2.41/0.99  fof(f33,plain,(
% 2.41/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f14])).
% 2.41/0.99  
% 2.41/0.99  fof(f39,plain,(
% 2.41/0.99    l1_pre_topc(sK0)),
% 2.41/0.99    inference(cnf_transformation,[],[f26])).
% 2.41/0.99  
% 2.41/0.99  fof(f3,axiom,(
% 2.41/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f13,plain,(
% 2.41/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.41/0.99    inference(ennf_transformation,[],[f3])).
% 2.41/0.99  
% 2.41/0.99  fof(f29,plain,(
% 2.41/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.41/0.99    inference(cnf_transformation,[],[f13])).
% 2.41/0.99  
% 2.41/0.99  fof(f4,axiom,(
% 2.41/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f30,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.41/0.99    inference(cnf_transformation,[],[f4])).
% 2.41/0.99  
% 2.41/0.99  fof(f47,plain,(
% 2.41/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.41/0.99    inference(definition_unfolding,[],[f29,f30])).
% 2.41/0.99  
% 2.41/0.99  fof(f32,plain,(
% 2.41/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f21])).
% 2.41/0.99  
% 2.41/0.99  fof(f42,plain,(
% 2.41/0.99    v1_tops_1(sK1,sK0)),
% 2.41/0.99    inference(cnf_transformation,[],[f26])).
% 2.41/0.99  
% 2.41/0.99  fof(f9,axiom,(
% 2.41/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f17,plain,(
% 2.41/0.99    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.41/0.99    inference(ennf_transformation,[],[f9])).
% 2.41/0.99  
% 2.41/0.99  fof(f18,plain,(
% 2.41/0.99    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.41/0.99    inference(flattening,[],[f17])).
% 2.41/0.99  
% 2.41/0.99  fof(f37,plain,(
% 2.41/0.99    ( ! [X2,X0,X1] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f18])).
% 2.41/0.99  
% 2.41/0.99  fof(f44,plain,(
% 2.41/0.99    v3_pre_topc(sK2,sK0)),
% 2.41/0.99    inference(cnf_transformation,[],[f26])).
% 2.41/0.99  
% 2.41/0.99  fof(f38,plain,(
% 2.41/0.99    v2_pre_topc(sK0)),
% 2.41/0.99    inference(cnf_transformation,[],[f26])).
% 2.41/0.99  
% 2.41/0.99  fof(f41,plain,(
% 2.41/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.41/0.99    inference(cnf_transformation,[],[f26])).
% 2.41/0.99  
% 2.41/0.99  fof(f43,plain,(
% 2.41/0.99    v1_tops_1(sK2,sK0)),
% 2.41/0.99    inference(cnf_transformation,[],[f26])).
% 2.41/0.99  
% 2.41/0.99  fof(f8,axiom,(
% 2.41/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f16,plain,(
% 2.41/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.41/0.99    inference(ennf_transformation,[],[f8])).
% 2.41/0.99  
% 2.41/0.99  fof(f22,plain,(
% 2.41/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.41/0.99    inference(nnf_transformation,[],[f16])).
% 2.41/0.99  
% 2.41/0.99  fof(f35,plain,(
% 2.41/0.99    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f22])).
% 2.41/0.99  
% 2.41/0.99  fof(f36,plain,(
% 2.41/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f22])).
% 2.41/0.99  
% 2.41/0.99  fof(f45,plain,(
% 2.41/0.99    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 2.41/0.99    inference(cnf_transformation,[],[f26])).
% 2.41/0.99  
% 2.41/0.99  fof(f1,axiom,(
% 2.41/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 2.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/0.99  
% 2.41/0.99  fof(f12,plain,(
% 2.41/0.99    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 2.41/0.99    inference(ennf_transformation,[],[f1])).
% 2.41/0.99  
% 2.41/0.99  fof(f27,plain,(
% 2.41/0.99    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 2.41/0.99    inference(cnf_transformation,[],[f12])).
% 2.41/0.99  
% 2.41/0.99  fof(f46,plain,(
% 2.41/0.99    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 2.41/0.99    inference(definition_unfolding,[],[f27,f30])).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1,plain,
% 2.41/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_620,plain,
% 2.41/0.99      ( k2_tarski(X0_45,X1_45) = k2_tarski(X1_45,X0_45) ),
% 2.41/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_4,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.41/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_128,plain,
% 2.41/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.41/0.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_129,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.41/0.99      inference(renaming,[status(thm)],[c_128]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_15,negated_conjecture,
% 2.41/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.41/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_414,plain,
% 2.41/0.99      ( r1_tarski(X0,X1)
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
% 2.41/0.99      | sK1 != X0 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_129,c_15]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_415,plain,
% 2.41/0.99      ( r1_tarski(sK1,X0)
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_414]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_612,plain,
% 2.41/0.99      ( r1_tarski(sK1,X0_46)
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46) ),
% 2.41/0.99      inference(subtyping,[status(esa)],[c_415]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_765,plain,
% 2.41/0.99      ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | r1_tarski(sK1,X0_46) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_6,plain,
% 2.41/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_5,plain,
% 2.41/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_232,plain,
% 2.41/0.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.41/0.99      inference(resolution,[status(thm)],[c_6,c_5]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_16,negated_conjecture,
% 2.41/0.99      ( l1_pre_topc(sK0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_271,plain,
% 2.41/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_232,c_16]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_272,plain,
% 2.41/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_271]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_618,plain,
% 2.41/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.41/0.99      inference(subtyping,[status(esa)],[c_272]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_793,plain,
% 2.41/0.99      ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | r1_tarski(sK1,X0_46) = iProver_top ),
% 2.41/0.99      inference(light_normalisation,[status(thm)],[c_765,c_618]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1164,plain,
% 2.41/0.99      ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
% 2.41/0.99      inference(equality_resolution,[status(thm)],[c_793]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_2,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.41/0.99      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 2.41/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_3,plain,
% 2.41/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.41/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_130,plain,
% 2.41/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.41/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_131,plain,
% 2.41/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.41/0.99      inference(renaming,[status(thm)],[c_130]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_162,plain,
% 2.41/0.99      ( ~ r1_tarski(X0,X1)
% 2.41/0.99      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 2.41/0.99      inference(bin_hyper_res,[status(thm)],[c_2,c_131]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_619,plain,
% 2.41/0.99      ( ~ r1_tarski(X0_45,X0_46)
% 2.41/0.99      | k9_subset_1(X0_46,X1_45,X0_45) = k1_setfam_1(k2_tarski(X1_45,X0_45)) ),
% 2.41/0.99      inference(subtyping,[status(esa)],[c_162]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_763,plain,
% 2.41/0.99      ( k9_subset_1(X0_46,X0_45,X1_45) = k1_setfam_1(k2_tarski(X0_45,X1_45))
% 2.41/0.99      | r1_tarski(X1_45,X0_46) != iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1307,plain,
% 2.41/0.99      ( k9_subset_1(k2_struct_0(sK0),X0_45,sK1) = k1_setfam_1(k2_tarski(X0_45,sK1)) ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1164,c_763]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_13,negated_conjecture,
% 2.41/0.99      ( v1_tops_1(sK1,sK0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_9,plain,
% 2.41/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.41/0.99      | ~ v1_tops_1(X2,X1)
% 2.41/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | ~ v2_pre_topc(X1)
% 2.41/0.99      | ~ l1_pre_topc(X1)
% 2.41/0.99      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_11,negated_conjecture,
% 2.41/0.99      ( v3_pre_topc(sK2,sK0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_246,plain,
% 2.41/0.99      ( ~ v1_tops_1(X0,X1)
% 2.41/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | ~ v2_pre_topc(X1)
% 2.41/0.99      | ~ l1_pre_topc(X1)
% 2.41/0.99      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X2,X0)) = k2_pre_topc(X1,X2)
% 2.41/0.99      | sK2 != X2
% 2.41/0.99      | sK0 != X1 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_247,plain,
% 2.41/0.99      ( ~ v1_tops_1(X0,sK0)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | ~ v2_pre_topc(sK0)
% 2.41/0.99      | ~ l1_pre_topc(sK0)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_246]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_17,negated_conjecture,
% 2.41/0.99      ( v2_pre_topc(sK0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_14,negated_conjecture,
% 2.41/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.41/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_251,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | ~ v1_tops_1(X0,sK0)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
% 2.41/0.99      inference(global_propositional_subsumption,
% 2.41/0.99                [status(thm)],
% 2.41/0.99                [c_247,c_17,c_16,c_14]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_252,plain,
% 2.41/0.99      ( ~ v1_tops_1(X0,sK0)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
% 2.41/0.99      inference(renaming,[status(thm)],[c_251]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_378,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2)
% 2.41/0.99      | sK1 != X0
% 2.41/0.99      | sK0 != sK0 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_252]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_379,plain,
% 2.41/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_378]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_381,plain,
% 2.41/0.99      ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
% 2.41/0.99      inference(global_propositional_subsumption,
% 2.41/0.99                [status(thm)],
% 2.41/0.99                [c_379,c_15]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_614,plain,
% 2.41/0.99      ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,sK2) ),
% 2.41/0.99      inference(subtyping,[status(esa)],[c_381]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_12,negated_conjecture,
% 2.41/0.99      ( v1_tops_1(sK2,sK0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_8,plain,
% 2.41/0.99      ( ~ v1_tops_1(X0,X1)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | ~ l1_pre_topc(X1)
% 2.41/0.99      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 2.41/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_276,plain,
% 2.41/0.99      ( ~ v1_tops_1(X0,X1)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 2.41/0.99      | sK0 != X1 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_277,plain,
% 2.41/0.99      ( ~ v1_tops_1(X0,sK0)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_276]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_354,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
% 2.41/0.99      | sK2 != X0
% 2.41/0.99      | sK0 != sK0 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_277]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_355,plain,
% 2.41/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_354]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_357,plain,
% 2.41/0.99      ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
% 2.41/0.99      inference(global_propositional_subsumption,
% 2.41/0.99                [status(thm)],
% 2.41/0.99                [c_355,c_14]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_617,plain,
% 2.41/0.99      ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
% 2.41/0.99      inference(subtyping,[status(esa)],[c_357]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_785,plain,
% 2.41/0.99      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_struct_0(sK0) ),
% 2.41/0.99      inference(light_normalisation,[status(thm)],[c_614,c_617,c_618]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1880,plain,
% 2.41/0.99      ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) = k2_struct_0(sK0) ),
% 2.41/0.99      inference(demodulation,[status(thm)],[c_1307,c_785]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1893,plain,
% 2.41/0.99      ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_struct_0(sK0) ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_620,c_1880]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_7,plain,
% 2.41/0.99      ( v1_tops_1(X0,X1)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | ~ l1_pre_topc(X1)
% 2.41/0.99      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 2.41/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_291,plain,
% 2.41/0.99      ( v1_tops_1(X0,X1)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.41/0.99      | k2_pre_topc(X1,X0) != k2_struct_0(X1)
% 2.41/0.99      | sK0 != X1 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_292,plain,
% 2.41/0.99      ( v1_tops_1(X0,sK0)
% 2.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_291]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_316,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2) ),
% 2.41/0.99      inference(resolution,[status(thm)],[c_292,c_252]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_426,plain,
% 2.41/0.99      ( ~ r1_tarski(X0,X1)
% 2.41/0.99      | X2 != X0
% 2.41/0.99      | k2_pre_topc(sK0,X2) != k2_struct_0(sK0)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X2)) = k2_pre_topc(sK0,sK2)
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1) ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_131,c_316]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_427,plain,
% 2.41/0.99      ( ~ r1_tarski(X0,X1)
% 2.41/0.99      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) = k2_pre_topc(sK0,sK2)
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_426]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_611,plain,
% 2.41/0.99      ( ~ r1_tarski(X0_45,X0_46)
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | k2_pre_topc(sK0,X0_45) != k2_struct_0(sK0)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0_45)) = k2_pre_topc(sK0,sK2) ),
% 2.41/0.99      inference(subtyping,[status(esa)],[c_427]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_766,plain,
% 2.41/0.99      ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | k2_pre_topc(sK0,X0_45) != k2_struct_0(sK0)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0_45)) = k2_pre_topc(sK0,sK2)
% 2.41/0.99      | r1_tarski(X0_45,X0_46) != iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_813,plain,
% 2.41/0.99      ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | k2_pre_topc(sK0,X0_45) != k2_struct_0(sK0)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0_45)) = k2_struct_0(sK0)
% 2.41/0.99      | r1_tarski(X0_45,X0_46) != iProver_top ),
% 2.41/0.99      inference(light_normalisation,[status(thm)],[c_766,c_617,c_618]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1950,plain,
% 2.41/0.99      ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k1_setfam_1(k2_tarski(sK1,sK2)))) = k2_struct_0(sK0)
% 2.41/0.99      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),X0_46) != iProver_top ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_1893,c_813]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_402,plain,
% 2.41/0.99      ( r1_tarski(X0,X1)
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
% 2.41/0.99      | sK2 != X0 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_129,c_14]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_403,plain,
% 2.41/0.99      ( r1_tarski(sK2,X0)
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_402]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_613,plain,
% 2.41/0.99      ( r1_tarski(sK2,X0_46)
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46) ),
% 2.41/0.99      inference(subtyping,[status(esa)],[c_403]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_764,plain,
% 2.41/0.99      ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | r1_tarski(sK2,X0_46) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_788,plain,
% 2.41/0.99      ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | r1_tarski(sK2,X0_46) = iProver_top ),
% 2.41/0.99      inference(light_normalisation,[status(thm)],[c_764,c_618]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_931,plain,
% 2.41/0.99      ( r1_tarski(sK2,k2_struct_0(sK0)) = iProver_top ),
% 2.41/0.99      inference(equality_resolution,[status(thm)],[c_788]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1297,plain,
% 2.41/0.99      ( k9_subset_1(k2_struct_0(sK0),X0_45,sK2) = k1_setfam_1(k2_tarski(X0_45,sK2)) ),
% 2.41/0.99      inference(superposition,[status(thm)],[c_931,c_763]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_10,negated_conjecture,
% 2.41/0.99      ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 2.41/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_344,plain,
% 2.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 2.41/0.99      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
% 2.41/0.99      | sK0 != sK0 ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_292]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_345,plain,
% 2.41/0.99      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_344]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_444,plain,
% 2.41/0.99      ( ~ r1_tarski(X0,X1)
% 2.41/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1) ),
% 2.41/0.99      inference(resolution_lifted,[status(thm)],[c_131,c_345]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_445,plain,
% 2.41/0.99      ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
% 2.41/0.99      inference(unflattening,[status(thm)],[c_444]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_610,plain,
% 2.41/0.99      ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0_46)
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0) ),
% 2.41/0.99      inference(subtyping,[status(esa)],[c_445]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_767,plain,
% 2.41/0.99      ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
% 2.41/0.99      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0_46) != iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_806,plain,
% 2.41/0.99      ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK1,sK2)) != k2_struct_0(sK0)
% 2.41/0.99      | r1_tarski(k9_subset_1(k2_struct_0(sK0),sK1,sK2),X0_46) != iProver_top ),
% 2.41/0.99      inference(light_normalisation,[status(thm)],[c_767,c_618]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1416,plain,
% 2.41/0.99      ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) != k2_struct_0(sK0)
% 2.41/0.99      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),X0_46) != iProver_top ),
% 2.41/0.99      inference(demodulation,[status(thm)],[c_1297,c_806]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1955,plain,
% 2.41/0.99      ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0_46)
% 2.41/0.99      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),X0_46) != iProver_top ),
% 2.41/0.99      inference(global_propositional_subsumption,
% 2.41/0.99                [status(thm)],
% 2.41/0.99                [c_1950,c_1416,c_1893]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_1963,plain,
% 2.41/0.99      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),k2_struct_0(sK0)) != iProver_top ),
% 2.41/0.99      inference(equality_resolution,[status(thm)],[c_1955]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_0,plain,
% 2.41/0.99      ( ~ r1_tarski(X0,X1)
% 2.41/0.99      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
% 2.41/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_621,plain,
% 2.41/0.99      ( ~ r1_tarski(X0_45,X0_46)
% 2.41/0.99      | r1_tarski(k1_setfam_1(k2_tarski(X0_45,X1_45)),X0_46) ),
% 2.41/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_948,plain,
% 2.41/0.99      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0_45)),k2_struct_0(sK0))
% 2.41/0.99      | ~ r1_tarski(sK1,k2_struct_0(sK0)) ),
% 2.41/0.99      inference(instantiation,[status(thm)],[c_621]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_949,plain,
% 2.41/0.99      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0_45)),k2_struct_0(sK0)) = iProver_top
% 2.41/0.99      | r1_tarski(sK1,k2_struct_0(sK0)) != iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_951,plain,
% 2.41/0.99      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),k2_struct_0(sK0)) = iProver_top
% 2.41/0.99      | r1_tarski(sK1,k2_struct_0(sK0)) != iProver_top ),
% 2.41/0.99      inference(instantiation,[status(thm)],[c_949]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_916,plain,
% 2.41/0.99      ( r1_tarski(sK1,k2_struct_0(sK0))
% 2.41/0.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(k2_struct_0(sK0)) ),
% 2.41/0.99      inference(instantiation,[status(thm)],[c_612]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_917,plain,
% 2.41/0.99      ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(k2_struct_0(sK0))
% 2.41/0.99      | r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
% 2.41/0.99      inference(predicate_to_equality,[status(thm)],[c_916]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_634,plain,
% 2.41/0.99      ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46) | X0_46 != X1_46 ),
% 2.41/0.99      theory(equality) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_852,plain,
% 2.41/0.99      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(X0_46)
% 2.41/0.99      | u1_struct_0(sK0) != X0_46 ),
% 2.41/0.99      inference(instantiation,[status(thm)],[c_634]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(c_894,plain,
% 2.41/0.99      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(k2_struct_0(sK0))
% 2.41/0.99      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 2.41/0.99      inference(instantiation,[status(thm)],[c_852]) ).
% 2.41/0.99  
% 2.41/0.99  cnf(contradiction,plain,
% 2.41/0.99      ( $false ),
% 2.41/0.99      inference(minisat,[status(thm)],[c_1963,c_951,c_917,c_894,c_618]) ).
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/0.99  
% 2.41/0.99  ------                               Statistics
% 2.41/0.99  
% 2.41/0.99  ------ General
% 2.41/0.99  
% 2.41/0.99  abstr_ref_over_cycles:                  0
% 2.41/0.99  abstr_ref_under_cycles:                 0
% 2.41/0.99  gc_basic_clause_elim:                   0
% 2.41/0.99  forced_gc_time:                         0
% 2.41/0.99  parsing_time:                           0.008
% 2.41/0.99  unif_index_cands_time:                  0.
% 2.41/0.99  unif_index_add_time:                    0.
% 2.41/0.99  orderings_time:                         0.
% 2.41/0.99  out_proof_time:                         0.012
% 2.41/0.99  total_time:                             0.101
% 2.41/0.99  num_of_symbols:                         50
% 2.41/0.99  num_of_terms:                           2025
% 2.41/0.99  
% 2.41/0.99  ------ Preprocessing
% 2.41/0.99  
% 2.41/0.99  num_of_splits:                          0
% 2.41/0.99  num_of_split_atoms:                     0
% 2.41/0.99  num_of_reused_defs:                     0
% 2.41/0.99  num_eq_ax_congr_red:                    18
% 2.41/0.99  num_of_sem_filtered_clauses:            1
% 2.41/0.99  num_of_subtypes:                        5
% 2.41/0.99  monotx_restored_types:                  0
% 2.41/0.99  sat_num_of_epr_types:                   0
% 2.41/0.99  sat_num_of_non_cyclic_types:            0
% 2.41/0.99  sat_guarded_non_collapsed_types:        0
% 2.41/0.99  num_pure_diseq_elim:                    0
% 2.41/0.99  simp_replaced_by:                       0
% 2.41/0.99  res_preprocessed:                       101
% 2.41/0.99  prep_upred:                             0
% 2.41/0.99  prep_unflattend:                        16
% 2.41/0.99  smt_new_axioms:                         0
% 2.41/0.99  pred_elim_cands:                        1
% 2.41/0.99  pred_elim:                              6
% 2.41/0.99  pred_elim_cl:                           2
% 2.41/0.99  pred_elim_cycles:                       9
% 2.41/0.99  merged_defs:                            2
% 2.41/0.99  merged_defs_ncl:                        0
% 2.41/0.99  bin_hyper_res:                          3
% 2.41/0.99  prep_cycles:                            5
% 2.41/0.99  pred_elim_time:                         0.006
% 2.41/0.99  splitting_time:                         0.
% 2.41/0.99  sem_filter_time:                        0.
% 2.41/0.99  monotx_time:                            0.
% 2.41/0.99  subtype_inf_time:                       0.
% 2.41/0.99  
% 2.41/0.99  ------ Problem properties
% 2.41/0.99  
% 2.41/0.99  clauses:                                14
% 2.41/0.99  conjectures:                            0
% 2.41/0.99  epr:                                    0
% 2.41/0.99  horn:                                   14
% 2.41/0.99  ground:                                 7
% 2.41/0.99  unary:                                  8
% 2.41/0.99  binary:                                 4
% 2.41/0.99  lits:                                   23
% 2.41/0.99  lits_eq:                                16
% 2.41/0.99  fd_pure:                                0
% 2.41/0.99  fd_pseudo:                              0
% 2.41/0.99  fd_cond:                                0
% 2.41/0.99  fd_pseudo_cond:                         0
% 2.41/0.99  ac_symbols:                             0
% 2.41/0.99  
% 2.41/0.99  ------ Propositional Solver
% 2.41/0.99  
% 2.41/0.99  prop_solver_calls:                      33
% 2.41/0.99  prop_fast_solver_calls:                 494
% 2.41/0.99  smt_solver_calls:                       0
% 2.41/0.99  smt_fast_solver_calls:                  0
% 2.41/0.99  prop_num_of_clauses:                    748
% 2.41/0.99  prop_preprocess_simplified:             2735
% 2.41/0.99  prop_fo_subsumed:                       8
% 2.41/0.99  prop_solver_time:                       0.
% 2.41/0.99  smt_solver_time:                        0.
% 2.41/0.99  smt_fast_solver_time:                   0.
% 2.41/0.99  prop_fast_solver_time:                  0.
% 2.41/0.99  prop_unsat_core_time:                   0.
% 2.41/0.99  
% 2.41/0.99  ------ QBF
% 2.41/0.99  
% 2.41/0.99  qbf_q_res:                              0
% 2.41/0.99  qbf_num_tautologies:                    0
% 2.41/0.99  qbf_prep_cycles:                        0
% 2.41/0.99  
% 2.41/0.99  ------ BMC1
% 2.41/0.99  
% 2.41/0.99  bmc1_current_bound:                     -1
% 2.41/0.99  bmc1_last_solved_bound:                 -1
% 2.41/0.99  bmc1_unsat_core_size:                   -1
% 2.41/0.99  bmc1_unsat_core_parents_size:           -1
% 2.41/0.99  bmc1_merge_next_fun:                    0
% 2.41/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.41/0.99  
% 2.41/0.99  ------ Instantiation
% 2.41/0.99  
% 2.41/0.99  inst_num_of_clauses:                    263
% 2.41/0.99  inst_num_in_passive:                    64
% 2.41/0.99  inst_num_in_active:                     165
% 2.41/0.99  inst_num_in_unprocessed:                34
% 2.41/0.99  inst_num_of_loops:                      170
% 2.41/0.99  inst_num_of_learning_restarts:          0
% 2.41/0.99  inst_num_moves_active_passive:          0
% 2.41/0.99  inst_lit_activity:                      0
% 2.41/0.99  inst_lit_activity_moves:                0
% 2.41/0.99  inst_num_tautologies:                   0
% 2.41/0.99  inst_num_prop_implied:                  0
% 2.41/0.99  inst_num_existing_simplified:           0
% 2.41/0.99  inst_num_eq_res_simplified:             0
% 2.41/0.99  inst_num_child_elim:                    0
% 2.41/0.99  inst_num_of_dismatching_blockings:      44
% 2.41/0.99  inst_num_of_non_proper_insts:           252
% 2.41/0.99  inst_num_of_duplicates:                 0
% 2.41/0.99  inst_inst_num_from_inst_to_res:         0
% 2.41/0.99  inst_dismatching_checking_time:         0.
% 2.41/0.99  
% 2.41/0.99  ------ Resolution
% 2.41/0.99  
% 2.41/0.99  res_num_of_clauses:                     0
% 2.41/0.99  res_num_in_passive:                     0
% 2.41/0.99  res_num_in_active:                      0
% 2.41/0.99  res_num_of_loops:                       106
% 2.41/0.99  res_forward_subset_subsumed:            47
% 2.41/0.99  res_backward_subset_subsumed:           2
% 2.41/0.99  res_forward_subsumed:                   0
% 2.41/0.99  res_backward_subsumed:                  0
% 2.41/0.99  res_forward_subsumption_resolution:     0
% 2.41/0.99  res_backward_subsumption_resolution:    0
% 2.41/0.99  res_clause_to_clause_subsumption:       178
% 2.41/0.99  res_orphan_elimination:                 0
% 2.41/0.99  res_tautology_del:                      44
% 2.41/0.99  res_num_eq_res_simplified:              4
% 2.41/0.99  res_num_sel_changes:                    0
% 2.41/0.99  res_moves_from_active_to_pass:          0
% 2.41/0.99  
% 2.41/0.99  ------ Superposition
% 2.41/0.99  
% 2.41/0.99  sup_time_total:                         0.
% 2.41/0.99  sup_time_generating:                    0.
% 2.41/0.99  sup_time_sim_full:                      0.
% 2.41/0.99  sup_time_sim_immed:                     0.
% 2.41/0.99  
% 2.41/0.99  sup_num_of_clauses:                     52
% 2.41/0.99  sup_num_in_active:                      26
% 2.41/0.99  sup_num_in_passive:                     26
% 2.41/0.99  sup_num_of_loops:                       33
% 2.41/0.99  sup_fw_superposition:                   32
% 2.41/0.99  sup_bw_superposition:                   9
% 2.41/0.99  sup_immediate_simplified:               2
% 2.41/0.99  sup_given_eliminated:                   0
% 2.41/0.99  comparisons_done:                       0
% 2.41/0.99  comparisons_avoided:                    0
% 2.41/0.99  
% 2.41/0.99  ------ Simplifications
% 2.41/0.99  
% 2.41/0.99  
% 2.41/0.99  sim_fw_subset_subsumed:                 2
% 2.41/0.99  sim_bw_subset_subsumed:                 0
% 2.41/0.99  sim_fw_subsumed:                        0
% 2.41/0.99  sim_bw_subsumed:                        0
% 2.41/0.99  sim_fw_subsumption_res:                 0
% 2.41/0.99  sim_bw_subsumption_res:                 0
% 2.41/0.99  sim_tautology_del:                      0
% 2.41/0.99  sim_eq_tautology_del:                   0
% 2.41/0.99  sim_eq_res_simp:                        0
% 2.41/0.99  sim_fw_demodulated:                     0
% 2.41/0.99  sim_bw_demodulated:                     8
% 2.41/0.99  sim_light_normalised:                   8
% 2.41/0.99  sim_joinable_taut:                      0
% 2.41/0.99  sim_joinable_simp:                      0
% 2.41/0.99  sim_ac_normalised:                      0
% 2.41/0.99  sim_smt_subsumption:                    0
% 2.41/0.99  
%------------------------------------------------------------------------------
