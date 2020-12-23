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
% DateTime   : Thu Dec  3 12:18:01 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 399 expanded)
%              Number of clauses        :   62 ( 114 expanded)
%              Number of leaves         :   14 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          :  396 (2156 expanded)
%              Number of equality atoms :   87 ( 176 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f29])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_compts_1(X2,X0)
                  & v2_compts_1(X1,X0)
                  & v8_pre_topc(X0) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_compts_1(X2,X0)
                    & v2_compts_1(X1,X0)
                    & v8_pre_topc(X0) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v2_compts_1(X2,X0)
          & v2_compts_1(X1,X0)
          & v8_pre_topc(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v2_compts_1(sK2,X0)
        & v2_compts_1(X1,X0)
        & v8_pre_topc(X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v2_compts_1(X2,X0)
            & v2_compts_1(sK1,X0)
            & v8_pre_topc(X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_compts_1(X2,X0)
                & v2_compts_1(X1,X0)
                & v8_pre_topc(X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_compts_1(X2,sK0)
              & v2_compts_1(X1,sK0)
              & v8_pre_topc(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_597,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_608,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_597,c_0])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k2_enumset1(X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_595,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1210,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_608,c_595])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_591,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1208,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(superposition,[status(thm)],[c_591,c_595])).

cnf(c_1854,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
    inference(demodulation,[status(thm)],[c_1210,c_1208])).

cnf(c_5,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_253,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_254,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ v4_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_15])).

cnf(c_259,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_587,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_259])).

cnf(c_2345,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1854,c_587])).

cnf(c_19,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,negated_conjecture,
    ( v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,plain,
    ( v2_compts_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,negated_conjecture,
    ( v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_165,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_166,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_165])).

cnf(c_170,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_166,c_15,c_14])).

cnf(c_676,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_677,plain,
    ( v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_6115,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2345,c_19,c_22,c_677])).

cnf(c_6116,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6115])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_596,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2344,plain,
    ( m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1854,c_596])).

cnf(c_2896,plain,
    ( m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2344,c_19])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_190,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | X2 != X3
    | X0 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_7])).

cnf(c_191,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_227,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_14])).

cnf(c_228,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ v4_pre_topc(X1,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v2_compts_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_228,c_15])).

cnf(c_231,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_230])).

cnf(c_588,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(X1,sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_1252,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_591,c_588])).

cnf(c_1411,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1252,c_22])).

cnf(c_2905,plain,
    ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | v4_pre_topc(k9_subset_1(sK2,X0,sK2),sK0) != iProver_top
    | m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2896,c_1411])).

cnf(c_4570,plain,
    ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | v4_pre_topc(k9_subset_1(sK2,X0,sK2),sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_2905])).

cnf(c_5739,plain,
    ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | v4_pre_topc(k9_subset_1(sK2,X0,sK2),sK0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4570,c_608])).

cnf(c_6124,plain,
    ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6116,c_5739])).

cnf(c_8,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_594,plain,
    ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2336,plain,
    ( v2_compts_1(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1854,c_594])).

cnf(c_10207,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6124,c_2336])).

cnf(c_679,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_680,plain,
    ( v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_10,negated_conjecture,
    ( v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10207,c_680,c_21,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.33  % CPULimit   : 60
% 0.18/0.33  % WCLimit    : 600
% 0.18/0.33  % DateTime   : Tue Dec  1 19:08:37 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 3.63/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/0.98  
% 3.63/0.98  ------  iProver source info
% 3.63/0.98  
% 3.63/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.63/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/0.98  git: non_committed_changes: false
% 3.63/0.98  git: last_make_outside_of_git: false
% 3.63/0.98  
% 3.63/0.98  ------ 
% 3.63/0.98  
% 3.63/0.98  ------ Input Options
% 3.63/0.98  
% 3.63/0.98  --out_options                           all
% 3.63/0.98  --tptp_safe_out                         true
% 3.63/0.98  --problem_path                          ""
% 3.63/0.98  --include_path                          ""
% 3.63/0.98  --clausifier                            res/vclausify_rel
% 3.63/0.98  --clausifier_options                    --mode clausify
% 3.63/0.98  --stdin                                 false
% 3.63/0.98  --stats_out                             all
% 3.63/0.98  
% 3.63/0.98  ------ General Options
% 3.63/0.98  
% 3.63/0.98  --fof                                   false
% 3.63/0.98  --time_out_real                         305.
% 3.63/0.98  --time_out_virtual                      -1.
% 3.63/0.98  --symbol_type_check                     false
% 3.63/0.98  --clausify_out                          false
% 3.63/0.98  --sig_cnt_out                           false
% 3.63/0.98  --trig_cnt_out                          false
% 3.63/0.98  --trig_cnt_out_tolerance                1.
% 3.63/0.98  --trig_cnt_out_sk_spl                   false
% 3.63/0.98  --abstr_cl_out                          false
% 3.63/0.98  
% 3.63/0.98  ------ Global Options
% 3.63/0.98  
% 3.63/0.98  --schedule                              default
% 3.63/0.98  --add_important_lit                     false
% 3.63/0.98  --prop_solver_per_cl                    1000
% 3.63/0.98  --min_unsat_core                        false
% 3.63/0.98  --soft_assumptions                      false
% 3.63/0.98  --soft_lemma_size                       3
% 3.63/0.98  --prop_impl_unit_size                   0
% 3.63/0.98  --prop_impl_unit                        []
% 3.63/0.98  --share_sel_clauses                     true
% 3.63/0.98  --reset_solvers                         false
% 3.63/0.98  --bc_imp_inh                            [conj_cone]
% 3.63/0.98  --conj_cone_tolerance                   3.
% 3.63/0.98  --extra_neg_conj                        none
% 3.63/0.98  --large_theory_mode                     true
% 3.63/0.98  --prolific_symb_bound                   200
% 3.63/0.98  --lt_threshold                          2000
% 3.63/0.98  --clause_weak_htbl                      true
% 3.63/0.98  --gc_record_bc_elim                     false
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing Options
% 3.63/0.98  
% 3.63/0.98  --preprocessing_flag                    true
% 3.63/0.98  --time_out_prep_mult                    0.1
% 3.63/0.98  --splitting_mode                        input
% 3.63/0.98  --splitting_grd                         true
% 3.63/0.98  --splitting_cvd                         false
% 3.63/0.98  --splitting_cvd_svl                     false
% 3.63/0.98  --splitting_nvd                         32
% 3.63/0.98  --sub_typing                            true
% 3.63/0.98  --prep_gs_sim                           true
% 3.63/0.98  --prep_unflatten                        true
% 3.63/0.98  --prep_res_sim                          true
% 3.63/0.98  --prep_upred                            true
% 3.63/0.98  --prep_sem_filter                       exhaustive
% 3.63/0.98  --prep_sem_filter_out                   false
% 3.63/0.98  --pred_elim                             true
% 3.63/0.98  --res_sim_input                         true
% 3.63/0.98  --eq_ax_congr_red                       true
% 3.63/0.98  --pure_diseq_elim                       true
% 3.63/0.98  --brand_transform                       false
% 3.63/0.98  --non_eq_to_eq                          false
% 3.63/0.98  --prep_def_merge                        true
% 3.63/0.98  --prep_def_merge_prop_impl              false
% 3.63/0.98  --prep_def_merge_mbd                    true
% 3.63/0.98  --prep_def_merge_tr_red                 false
% 3.63/0.98  --prep_def_merge_tr_cl                  false
% 3.63/0.98  --smt_preprocessing                     true
% 3.63/0.98  --smt_ac_axioms                         fast
% 3.63/0.98  --preprocessed_out                      false
% 3.63/0.98  --preprocessed_stats                    false
% 3.63/0.98  
% 3.63/0.98  ------ Abstraction refinement Options
% 3.63/0.98  
% 3.63/0.98  --abstr_ref                             []
% 3.63/0.98  --abstr_ref_prep                        false
% 3.63/0.98  --abstr_ref_until_sat                   false
% 3.63/0.98  --abstr_ref_sig_restrict                funpre
% 3.63/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/0.98  --abstr_ref_under                       []
% 3.63/0.98  
% 3.63/0.98  ------ SAT Options
% 3.63/0.98  
% 3.63/0.98  --sat_mode                              false
% 3.63/0.98  --sat_fm_restart_options                ""
% 3.63/0.98  --sat_gr_def                            false
% 3.63/0.98  --sat_epr_types                         true
% 3.63/0.98  --sat_non_cyclic_types                  false
% 3.63/0.98  --sat_finite_models                     false
% 3.63/0.98  --sat_fm_lemmas                         false
% 3.63/0.98  --sat_fm_prep                           false
% 3.63/0.98  --sat_fm_uc_incr                        true
% 3.63/0.98  --sat_out_model                         small
% 3.63/0.98  --sat_out_clauses                       false
% 3.63/0.98  
% 3.63/0.98  ------ QBF Options
% 3.63/0.98  
% 3.63/0.98  --qbf_mode                              false
% 3.63/0.98  --qbf_elim_univ                         false
% 3.63/0.98  --qbf_dom_inst                          none
% 3.63/0.98  --qbf_dom_pre_inst                      false
% 3.63/0.98  --qbf_sk_in                             false
% 3.63/0.98  --qbf_pred_elim                         true
% 3.63/0.98  --qbf_split                             512
% 3.63/0.98  
% 3.63/0.98  ------ BMC1 Options
% 3.63/0.98  
% 3.63/0.98  --bmc1_incremental                      false
% 3.63/0.98  --bmc1_axioms                           reachable_all
% 3.63/0.98  --bmc1_min_bound                        0
% 3.63/0.98  --bmc1_max_bound                        -1
% 3.63/0.98  --bmc1_max_bound_default                -1
% 3.63/0.98  --bmc1_symbol_reachability              true
% 3.63/0.98  --bmc1_property_lemmas                  false
% 3.63/0.98  --bmc1_k_induction                      false
% 3.63/0.98  --bmc1_non_equiv_states                 false
% 3.63/0.98  --bmc1_deadlock                         false
% 3.63/0.98  --bmc1_ucm                              false
% 3.63/0.98  --bmc1_add_unsat_core                   none
% 3.63/0.98  --bmc1_unsat_core_children              false
% 3.63/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/0.98  --bmc1_out_stat                         full
% 3.63/0.98  --bmc1_ground_init                      false
% 3.63/0.98  --bmc1_pre_inst_next_state              false
% 3.63/0.98  --bmc1_pre_inst_state                   false
% 3.63/0.98  --bmc1_pre_inst_reach_state             false
% 3.63/0.98  --bmc1_out_unsat_core                   false
% 3.63/0.98  --bmc1_aig_witness_out                  false
% 3.63/0.98  --bmc1_verbose                          false
% 3.63/0.98  --bmc1_dump_clauses_tptp                false
% 3.63/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.63/0.98  --bmc1_dump_file                        -
% 3.63/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.63/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.63/0.98  --bmc1_ucm_extend_mode                  1
% 3.63/0.98  --bmc1_ucm_init_mode                    2
% 3.63/0.98  --bmc1_ucm_cone_mode                    none
% 3.63/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.63/0.98  --bmc1_ucm_relax_model                  4
% 3.63/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.63/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/0.98  --bmc1_ucm_layered_model                none
% 3.63/0.98  --bmc1_ucm_max_lemma_size               10
% 3.63/0.98  
% 3.63/0.98  ------ AIG Options
% 3.63/0.98  
% 3.63/0.98  --aig_mode                              false
% 3.63/0.98  
% 3.63/0.98  ------ Instantiation Options
% 3.63/0.98  
% 3.63/0.98  --instantiation_flag                    true
% 3.63/0.98  --inst_sos_flag                         false
% 3.63/0.98  --inst_sos_phase                        true
% 3.63/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel_side                     num_symb
% 3.63/0.98  --inst_solver_per_active                1400
% 3.63/0.98  --inst_solver_calls_frac                1.
% 3.63/0.98  --inst_passive_queue_type               priority_queues
% 3.63/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/0.98  --inst_passive_queues_freq              [25;2]
% 3.63/0.98  --inst_dismatching                      true
% 3.63/0.98  --inst_eager_unprocessed_to_passive     true
% 3.63/0.98  --inst_prop_sim_given                   true
% 3.63/0.98  --inst_prop_sim_new                     false
% 3.63/0.98  --inst_subs_new                         false
% 3.63/0.98  --inst_eq_res_simp                      false
% 3.63/0.98  --inst_subs_given                       false
% 3.63/0.98  --inst_orphan_elimination               true
% 3.63/0.98  --inst_learning_loop_flag               true
% 3.63/0.98  --inst_learning_start                   3000
% 3.63/0.98  --inst_learning_factor                  2
% 3.63/0.98  --inst_start_prop_sim_after_learn       3
% 3.63/0.98  --inst_sel_renew                        solver
% 3.63/0.98  --inst_lit_activity_flag                true
% 3.63/0.98  --inst_restr_to_given                   false
% 3.63/0.98  --inst_activity_threshold               500
% 3.63/0.98  --inst_out_proof                        true
% 3.63/0.98  
% 3.63/0.98  ------ Resolution Options
% 3.63/0.98  
% 3.63/0.98  --resolution_flag                       true
% 3.63/0.98  --res_lit_sel                           adaptive
% 3.63/0.98  --res_lit_sel_side                      none
% 3.63/0.98  --res_ordering                          kbo
% 3.63/0.98  --res_to_prop_solver                    active
% 3.63/0.98  --res_prop_simpl_new                    false
% 3.63/0.98  --res_prop_simpl_given                  true
% 3.63/0.98  --res_passive_queue_type                priority_queues
% 3.63/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/0.98  --res_passive_queues_freq               [15;5]
% 3.63/0.98  --res_forward_subs                      full
% 3.63/0.98  --res_backward_subs                     full
% 3.63/0.98  --res_forward_subs_resolution           true
% 3.63/0.98  --res_backward_subs_resolution          true
% 3.63/0.98  --res_orphan_elimination                true
% 3.63/0.98  --res_time_limit                        2.
% 3.63/0.98  --res_out_proof                         true
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Options
% 3.63/0.98  
% 3.63/0.98  --superposition_flag                    true
% 3.63/0.98  --sup_passive_queue_type                priority_queues
% 3.63/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.63/0.98  --demod_completeness_check              fast
% 3.63/0.98  --demod_use_ground                      true
% 3.63/0.98  --sup_to_prop_solver                    passive
% 3.63/0.98  --sup_prop_simpl_new                    true
% 3.63/0.98  --sup_prop_simpl_given                  true
% 3.63/0.98  --sup_fun_splitting                     false
% 3.63/0.98  --sup_smt_interval                      50000
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Simplification Setup
% 3.63/0.98  
% 3.63/0.98  --sup_indices_passive                   []
% 3.63/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_full_bw                           [BwDemod]
% 3.63/0.98  --sup_immed_triv                        [TrivRules]
% 3.63/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_immed_bw_main                     []
% 3.63/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  
% 3.63/0.98  ------ Combination Options
% 3.63/0.98  
% 3.63/0.98  --comb_res_mult                         3
% 3.63/0.98  --comb_sup_mult                         2
% 3.63/0.98  --comb_inst_mult                        10
% 3.63/0.98  
% 3.63/0.98  ------ Debug Options
% 3.63/0.98  
% 3.63/0.98  --dbg_backtrace                         false
% 3.63/0.98  --dbg_dump_prop_clauses                 false
% 3.63/0.98  --dbg_dump_prop_clauses_file            -
% 3.63/0.98  --dbg_out_stat                          false
% 3.63/0.98  ------ Parsing...
% 3.63/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/0.98  ------ Proving...
% 3.63/0.98  ------ Problem Properties 
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  clauses                                 12
% 3.63/0.98  conjectures                             5
% 3.63/0.98  EPR                                     2
% 3.63/0.98  Horn                                    12
% 3.63/0.98  unary                                   7
% 3.63/0.98  binary                                  2
% 3.63/0.98  lits                                    25
% 3.63/0.98  lits eq                                 2
% 3.63/0.98  fd_pure                                 0
% 3.63/0.98  fd_pseudo                               0
% 3.63/0.98  fd_cond                                 0
% 3.63/0.98  fd_pseudo_cond                          0
% 3.63/0.98  AC symbols                              0
% 3.63/0.98  
% 3.63/0.98  ------ Schedule dynamic 5 is on 
% 3.63/0.98  
% 3.63/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  ------ 
% 3.63/0.98  Current options:
% 3.63/0.98  ------ 
% 3.63/0.98  
% 3.63/0.98  ------ Input Options
% 3.63/0.98  
% 3.63/0.98  --out_options                           all
% 3.63/0.98  --tptp_safe_out                         true
% 3.63/0.98  --problem_path                          ""
% 3.63/0.98  --include_path                          ""
% 3.63/0.98  --clausifier                            res/vclausify_rel
% 3.63/0.98  --clausifier_options                    --mode clausify
% 3.63/0.98  --stdin                                 false
% 3.63/0.98  --stats_out                             all
% 3.63/0.98  
% 3.63/0.98  ------ General Options
% 3.63/0.98  
% 3.63/0.98  --fof                                   false
% 3.63/0.98  --time_out_real                         305.
% 3.63/0.98  --time_out_virtual                      -1.
% 3.63/0.98  --symbol_type_check                     false
% 3.63/0.98  --clausify_out                          false
% 3.63/0.98  --sig_cnt_out                           false
% 3.63/0.98  --trig_cnt_out                          false
% 3.63/0.98  --trig_cnt_out_tolerance                1.
% 3.63/0.98  --trig_cnt_out_sk_spl                   false
% 3.63/0.98  --abstr_cl_out                          false
% 3.63/0.98  
% 3.63/0.98  ------ Global Options
% 3.63/0.98  
% 3.63/0.98  --schedule                              default
% 3.63/0.98  --add_important_lit                     false
% 3.63/0.98  --prop_solver_per_cl                    1000
% 3.63/0.98  --min_unsat_core                        false
% 3.63/0.98  --soft_assumptions                      false
% 3.63/0.98  --soft_lemma_size                       3
% 3.63/0.98  --prop_impl_unit_size                   0
% 3.63/0.98  --prop_impl_unit                        []
% 3.63/0.98  --share_sel_clauses                     true
% 3.63/0.98  --reset_solvers                         false
% 3.63/0.98  --bc_imp_inh                            [conj_cone]
% 3.63/0.98  --conj_cone_tolerance                   3.
% 3.63/0.98  --extra_neg_conj                        none
% 3.63/0.98  --large_theory_mode                     true
% 3.63/0.98  --prolific_symb_bound                   200
% 3.63/0.98  --lt_threshold                          2000
% 3.63/0.98  --clause_weak_htbl                      true
% 3.63/0.98  --gc_record_bc_elim                     false
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing Options
% 3.63/0.98  
% 3.63/0.98  --preprocessing_flag                    true
% 3.63/0.98  --time_out_prep_mult                    0.1
% 3.63/0.98  --splitting_mode                        input
% 3.63/0.98  --splitting_grd                         true
% 3.63/0.98  --splitting_cvd                         false
% 3.63/0.98  --splitting_cvd_svl                     false
% 3.63/0.98  --splitting_nvd                         32
% 3.63/0.98  --sub_typing                            true
% 3.63/0.98  --prep_gs_sim                           true
% 3.63/0.98  --prep_unflatten                        true
% 3.63/0.98  --prep_res_sim                          true
% 3.63/0.98  --prep_upred                            true
% 3.63/0.98  --prep_sem_filter                       exhaustive
% 3.63/0.98  --prep_sem_filter_out                   false
% 3.63/0.98  --pred_elim                             true
% 3.63/0.98  --res_sim_input                         true
% 3.63/0.98  --eq_ax_congr_red                       true
% 3.63/0.98  --pure_diseq_elim                       true
% 3.63/0.98  --brand_transform                       false
% 3.63/0.98  --non_eq_to_eq                          false
% 3.63/0.98  --prep_def_merge                        true
% 3.63/0.98  --prep_def_merge_prop_impl              false
% 3.63/0.98  --prep_def_merge_mbd                    true
% 3.63/0.98  --prep_def_merge_tr_red                 false
% 3.63/0.98  --prep_def_merge_tr_cl                  false
% 3.63/0.98  --smt_preprocessing                     true
% 3.63/0.98  --smt_ac_axioms                         fast
% 3.63/0.98  --preprocessed_out                      false
% 3.63/0.98  --preprocessed_stats                    false
% 3.63/0.98  
% 3.63/0.98  ------ Abstraction refinement Options
% 3.63/0.98  
% 3.63/0.98  --abstr_ref                             []
% 3.63/0.98  --abstr_ref_prep                        false
% 3.63/0.98  --abstr_ref_until_sat                   false
% 3.63/0.98  --abstr_ref_sig_restrict                funpre
% 3.63/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/0.98  --abstr_ref_under                       []
% 3.63/0.98  
% 3.63/0.98  ------ SAT Options
% 3.63/0.98  
% 3.63/0.98  --sat_mode                              false
% 3.63/0.98  --sat_fm_restart_options                ""
% 3.63/0.98  --sat_gr_def                            false
% 3.63/0.98  --sat_epr_types                         true
% 3.63/0.98  --sat_non_cyclic_types                  false
% 3.63/0.98  --sat_finite_models                     false
% 3.63/0.98  --sat_fm_lemmas                         false
% 3.63/0.98  --sat_fm_prep                           false
% 3.63/0.98  --sat_fm_uc_incr                        true
% 3.63/0.98  --sat_out_model                         small
% 3.63/0.98  --sat_out_clauses                       false
% 3.63/0.98  
% 3.63/0.98  ------ QBF Options
% 3.63/0.98  
% 3.63/0.98  --qbf_mode                              false
% 3.63/0.98  --qbf_elim_univ                         false
% 3.63/0.98  --qbf_dom_inst                          none
% 3.63/0.98  --qbf_dom_pre_inst                      false
% 3.63/0.98  --qbf_sk_in                             false
% 3.63/0.98  --qbf_pred_elim                         true
% 3.63/0.98  --qbf_split                             512
% 3.63/0.98  
% 3.63/0.98  ------ BMC1 Options
% 3.63/0.98  
% 3.63/0.98  --bmc1_incremental                      false
% 3.63/0.98  --bmc1_axioms                           reachable_all
% 3.63/0.98  --bmc1_min_bound                        0
% 3.63/0.98  --bmc1_max_bound                        -1
% 3.63/0.98  --bmc1_max_bound_default                -1
% 3.63/0.98  --bmc1_symbol_reachability              true
% 3.63/0.98  --bmc1_property_lemmas                  false
% 3.63/0.98  --bmc1_k_induction                      false
% 3.63/0.98  --bmc1_non_equiv_states                 false
% 3.63/0.98  --bmc1_deadlock                         false
% 3.63/0.98  --bmc1_ucm                              false
% 3.63/0.98  --bmc1_add_unsat_core                   none
% 3.63/0.98  --bmc1_unsat_core_children              false
% 3.63/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/0.98  --bmc1_out_stat                         full
% 3.63/0.98  --bmc1_ground_init                      false
% 3.63/0.98  --bmc1_pre_inst_next_state              false
% 3.63/0.98  --bmc1_pre_inst_state                   false
% 3.63/0.98  --bmc1_pre_inst_reach_state             false
% 3.63/0.98  --bmc1_out_unsat_core                   false
% 3.63/0.98  --bmc1_aig_witness_out                  false
% 3.63/0.98  --bmc1_verbose                          false
% 3.63/0.98  --bmc1_dump_clauses_tptp                false
% 3.63/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.63/0.98  --bmc1_dump_file                        -
% 3.63/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.63/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.63/0.98  --bmc1_ucm_extend_mode                  1
% 3.63/0.98  --bmc1_ucm_init_mode                    2
% 3.63/0.98  --bmc1_ucm_cone_mode                    none
% 3.63/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.63/0.98  --bmc1_ucm_relax_model                  4
% 3.63/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.63/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/0.98  --bmc1_ucm_layered_model                none
% 3.63/0.98  --bmc1_ucm_max_lemma_size               10
% 3.63/0.98  
% 3.63/0.98  ------ AIG Options
% 3.63/0.98  
% 3.63/0.98  --aig_mode                              false
% 3.63/0.98  
% 3.63/0.98  ------ Instantiation Options
% 3.63/0.98  
% 3.63/0.98  --instantiation_flag                    true
% 3.63/0.98  --inst_sos_flag                         false
% 3.63/0.98  --inst_sos_phase                        true
% 3.63/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel_side                     none
% 3.63/0.98  --inst_solver_per_active                1400
% 3.63/0.98  --inst_solver_calls_frac                1.
% 3.63/0.98  --inst_passive_queue_type               priority_queues
% 3.63/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/0.98  --inst_passive_queues_freq              [25;2]
% 3.63/0.98  --inst_dismatching                      true
% 3.63/0.98  --inst_eager_unprocessed_to_passive     true
% 3.63/0.98  --inst_prop_sim_given                   true
% 3.63/0.98  --inst_prop_sim_new                     false
% 3.63/0.98  --inst_subs_new                         false
% 3.63/0.98  --inst_eq_res_simp                      false
% 3.63/0.98  --inst_subs_given                       false
% 3.63/0.98  --inst_orphan_elimination               true
% 3.63/0.98  --inst_learning_loop_flag               true
% 3.63/0.98  --inst_learning_start                   3000
% 3.63/0.98  --inst_learning_factor                  2
% 3.63/0.98  --inst_start_prop_sim_after_learn       3
% 3.63/0.98  --inst_sel_renew                        solver
% 3.63/0.98  --inst_lit_activity_flag                true
% 3.63/0.98  --inst_restr_to_given                   false
% 3.63/0.98  --inst_activity_threshold               500
% 3.63/0.98  --inst_out_proof                        true
% 3.63/0.98  
% 3.63/0.98  ------ Resolution Options
% 3.63/0.98  
% 3.63/0.98  --resolution_flag                       false
% 3.63/0.98  --res_lit_sel                           adaptive
% 3.63/0.98  --res_lit_sel_side                      none
% 3.63/0.98  --res_ordering                          kbo
% 3.63/0.98  --res_to_prop_solver                    active
% 3.63/0.98  --res_prop_simpl_new                    false
% 3.63/0.98  --res_prop_simpl_given                  true
% 3.63/0.98  --res_passive_queue_type                priority_queues
% 3.63/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/0.98  --res_passive_queues_freq               [15;5]
% 3.63/0.98  --res_forward_subs                      full
% 3.63/0.98  --res_backward_subs                     full
% 3.63/0.98  --res_forward_subs_resolution           true
% 3.63/0.98  --res_backward_subs_resolution          true
% 3.63/0.98  --res_orphan_elimination                true
% 3.63/0.98  --res_time_limit                        2.
% 3.63/0.98  --res_out_proof                         true
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Options
% 3.63/0.98  
% 3.63/0.98  --superposition_flag                    true
% 3.63/0.98  --sup_passive_queue_type                priority_queues
% 3.63/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.63/0.98  --demod_completeness_check              fast
% 3.63/0.98  --demod_use_ground                      true
% 3.63/0.98  --sup_to_prop_solver                    passive
% 3.63/0.98  --sup_prop_simpl_new                    true
% 3.63/0.98  --sup_prop_simpl_given                  true
% 3.63/0.98  --sup_fun_splitting                     false
% 3.63/0.98  --sup_smt_interval                      50000
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Simplification Setup
% 3.63/0.98  
% 3.63/0.98  --sup_indices_passive                   []
% 3.63/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_full_bw                           [BwDemod]
% 3.63/0.98  --sup_immed_triv                        [TrivRules]
% 3.63/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_immed_bw_main                     []
% 3.63/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  
% 3.63/0.98  ------ Combination Options
% 3.63/0.98  
% 3.63/0.98  --comb_res_mult                         3
% 3.63/0.98  --comb_sup_mult                         2
% 3.63/0.98  --comb_inst_mult                        10
% 3.63/0.98  
% 3.63/0.98  ------ Debug Options
% 3.63/0.98  
% 3.63/0.98  --dbg_backtrace                         false
% 3.63/0.98  --dbg_dump_prop_clauses                 false
% 3.63/0.98  --dbg_dump_prop_clauses_file            -
% 3.63/0.98  --dbg_out_stat                          false
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  ------ Proving...
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  % SZS status Theorem for theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  fof(f3,axiom,(
% 3.63/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f31,plain,(
% 3.63/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f3])).
% 3.63/0.98  
% 3.63/0.98  fof(f2,axiom,(
% 3.63/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f30,plain,(
% 3.63/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.63/0.98    inference(cnf_transformation,[],[f2])).
% 3.63/0.98  
% 3.63/0.98  fof(f5,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f15,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.63/0.98    inference(ennf_transformation,[],[f5])).
% 3.63/0.98  
% 3.63/0.98  fof(f33,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f15])).
% 3.63/0.98  
% 3.63/0.98  fof(f6,axiom,(
% 3.63/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f34,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f6])).
% 3.63/0.98  
% 3.63/0.98  fof(f1,axiom,(
% 3.63/0.98    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f29,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f1])).
% 3.63/0.98  
% 3.63/0.98  fof(f47,plain,(
% 3.63/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 3.63/0.98    inference(definition_unfolding,[],[f34,f29])).
% 3.63/0.98  
% 3.63/0.98  fof(f48,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.63/0.98    inference(definition_unfolding,[],[f33,f47])).
% 3.63/0.98  
% 3.63/0.98  fof(f11,conjecture,(
% 3.63/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f12,negated_conjecture,(
% 3.63/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.63/0.98    inference(negated_conjecture,[],[f11])).
% 3.63/0.98  
% 3.63/0.98  fof(f23,plain,(
% 3.63/0.98    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.63/0.98    inference(ennf_transformation,[],[f12])).
% 3.63/0.98  
% 3.63/0.98  fof(f24,plain,(
% 3.63/0.98    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.63/0.98    inference(flattening,[],[f23])).
% 3.63/0.98  
% 3.63/0.98  fof(f27,plain,(
% 3.63/0.98    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v2_compts_1(sK2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f26,plain,(
% 3.63/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(sK1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f25,plain,(
% 3.63/0.98    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f28,plain,(
% 3.63/0.98    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 3.63/0.98  
% 3.63/0.98  fof(f42,plain,(
% 3.63/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.63/0.98    inference(cnf_transformation,[],[f28])).
% 3.63/0.98  
% 3.63/0.98  fof(f8,axiom,(
% 3.63/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f17,plain,(
% 3.63/0.98    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.63/0.98    inference(ennf_transformation,[],[f8])).
% 3.63/0.98  
% 3.63/0.98  fof(f18,plain,(
% 3.63/0.98    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.63/0.98    inference(flattening,[],[f17])).
% 3.63/0.98  
% 3.63/0.98  fof(f36,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f18])).
% 3.63/0.98  
% 3.63/0.98  fof(f40,plain,(
% 3.63/0.98    l1_pre_topc(sK0)),
% 3.63/0.98    inference(cnf_transformation,[],[f28])).
% 3.63/0.98  
% 3.63/0.98  fof(f39,plain,(
% 3.63/0.98    v2_pre_topc(sK0)),
% 3.63/0.98    inference(cnf_transformation,[],[f28])).
% 3.63/0.98  
% 3.63/0.98  fof(f45,plain,(
% 3.63/0.98    v2_compts_1(sK2,sK0)),
% 3.63/0.98    inference(cnf_transformation,[],[f28])).
% 3.63/0.98  
% 3.63/0.98  fof(f9,axiom,(
% 3.63/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f19,plain,(
% 3.63/0.98    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.63/0.98    inference(ennf_transformation,[],[f9])).
% 3.63/0.98  
% 3.63/0.98  fof(f20,plain,(
% 3.63/0.98    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.63/0.98    inference(flattening,[],[f19])).
% 3.63/0.98  
% 3.63/0.98  fof(f37,plain,(
% 3.63/0.98    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f20])).
% 3.63/0.98  
% 3.63/0.98  fof(f43,plain,(
% 3.63/0.98    v8_pre_topc(sK0)),
% 3.63/0.98    inference(cnf_transformation,[],[f28])).
% 3.63/0.98  
% 3.63/0.98  fof(f4,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f14,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.63/0.98    inference(ennf_transformation,[],[f4])).
% 3.63/0.98  
% 3.63/0.98  fof(f32,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f14])).
% 3.63/0.98  
% 3.63/0.98  fof(f7,axiom,(
% 3.63/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f13,plain,(
% 3.63/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.63/0.98    inference(unused_predicate_definition_removal,[],[f7])).
% 3.63/0.98  
% 3.63/0.98  fof(f16,plain,(
% 3.63/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.63/0.98    inference(ennf_transformation,[],[f13])).
% 3.63/0.98  
% 3.63/0.98  fof(f35,plain,(
% 3.63/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f16])).
% 3.63/0.98  
% 3.63/0.98  fof(f10,axiom,(
% 3.63/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 3.63/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f21,plain,(
% 3.63/0.98    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.63/0.98    inference(ennf_transformation,[],[f10])).
% 3.63/0.98  
% 3.63/0.98  fof(f22,plain,(
% 3.63/0.98    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.63/0.98    inference(flattening,[],[f21])).
% 3.63/0.98  
% 3.63/0.98  fof(f38,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f22])).
% 3.63/0.98  
% 3.63/0.98  fof(f46,plain,(
% 3.63/0.98    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 3.63/0.98    inference(cnf_transformation,[],[f28])).
% 3.63/0.98  
% 3.63/0.98  fof(f44,plain,(
% 3.63/0.98    v2_compts_1(sK1,sK0)),
% 3.63/0.98    inference(cnf_transformation,[],[f28])).
% 3.63/0.98  
% 3.63/0.98  fof(f41,plain,(
% 3.63/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.63/0.98    inference(cnf_transformation,[],[f28])).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1,plain,
% 3.63/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.63/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_597,plain,
% 3.63/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_0,plain,
% 3.63/0.98      ( k2_subset_1(X0) = X0 ),
% 3.63/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_608,plain,
% 3.63/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.63/0.98      inference(light_normalisation,[status(thm)],[c_597,c_0]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.63/0.98      | k1_setfam_1(k2_enumset1(X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_595,plain,
% 3.63/0.98      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.63/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1210,plain,
% 3.63/0.98      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_608,c_595]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_12,negated_conjecture,
% 3.63/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_591,plain,
% 3.63/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1208,plain,
% 3.63/0.98      ( k1_setfam_1(k2_enumset1(X0,X0,X0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_591,c_595]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1854,plain,
% 3.63/0.98      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_1210,c_1208]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5,plain,
% 3.63/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.63/0.98      | ~ v4_pre_topc(X2,X1)
% 3.63/0.98      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ v2_pre_topc(X1)
% 3.63/0.98      | ~ l1_pre_topc(X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_14,negated_conjecture,
% 3.63/0.98      ( l1_pre_topc(sK0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_253,plain,
% 3.63/0.98      ( ~ v4_pre_topc(X0,X1)
% 3.63/0.98      | ~ v4_pre_topc(X2,X1)
% 3.63/0.98      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ v2_pre_topc(X1)
% 3.63/0.98      | sK0 != X1 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_254,plain,
% 3.63/0.98      ( ~ v4_pre_topc(X0,sK0)
% 3.63/0.98      | ~ v4_pre_topc(X1,sK0)
% 3.63/0.98      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/0.98      | ~ v2_pre_topc(sK0) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_253]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_15,negated_conjecture,
% 3.63/0.98      ( v2_pre_topc(sK0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_258,plain,
% 3.63/0.98      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/0.98      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 3.63/0.98      | ~ v4_pre_topc(X1,sK0)
% 3.63/0.98      | ~ v4_pre_topc(X0,sK0) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_254,c_15]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_259,plain,
% 3.63/0.98      ( ~ v4_pre_topc(X0,sK0)
% 3.63/0.98      | ~ v4_pre_topc(X1,sK0)
% 3.63/0.98      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/0.98      inference(renaming,[status(thm)],[c_258]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_587,plain,
% 3.63/0.98      ( v4_pre_topc(X0,sK0) != iProver_top
% 3.63/0.98      | v4_pre_topc(X1,sK0) != iProver_top
% 3.63/0.98      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0) = iProver_top
% 3.63/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.63/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_259]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2345,plain,
% 3.63/0.98      ( v4_pre_topc(X0,sK0) != iProver_top
% 3.63/0.98      | v4_pre_topc(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 3.63/0.98      | v4_pre_topc(sK2,sK0) != iProver_top
% 3.63/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.63/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_1854,c_587]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_19,plain,
% 3.63/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_9,negated_conjecture,
% 3.63/0.98      ( v2_compts_1(sK2,sK0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_22,plain,
% 3.63/0.98      ( v2_compts_1(sK2,sK0) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6,plain,
% 3.63/0.98      ( ~ v2_compts_1(X0,X1)
% 3.63/0.98      | v4_pre_topc(X0,X1)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ v8_pre_topc(X1)
% 3.63/0.98      | ~ v2_pre_topc(X1)
% 3.63/0.98      | ~ l1_pre_topc(X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_11,negated_conjecture,
% 3.63/0.98      ( v8_pre_topc(sK0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_165,plain,
% 3.63/0.98      ( ~ v2_compts_1(X0,X1)
% 3.63/0.98      | v4_pre_topc(X0,X1)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ v2_pre_topc(X1)
% 3.63/0.98      | ~ l1_pre_topc(X1)
% 3.63/0.98      | sK0 != X1 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_166,plain,
% 3.63/0.98      ( ~ v2_compts_1(X0,sK0)
% 3.63/0.98      | v4_pre_topc(X0,sK0)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/0.98      | ~ v2_pre_topc(sK0)
% 3.63/0.98      | ~ l1_pre_topc(sK0) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_165]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_170,plain,
% 3.63/0.98      ( ~ v2_compts_1(X0,sK0)
% 3.63/0.98      | v4_pre_topc(X0,sK0)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_166,c_15,c_14]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_676,plain,
% 3.63/0.98      ( ~ v2_compts_1(sK2,sK0)
% 3.63/0.98      | v4_pre_topc(sK2,sK0)
% 3.63/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_170]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_677,plain,
% 3.63/0.98      ( v2_compts_1(sK2,sK0) != iProver_top
% 3.63/0.98      | v4_pre_topc(sK2,sK0) = iProver_top
% 3.63/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6115,plain,
% 3.63/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.63/0.98      | v4_pre_topc(X0,sK0) != iProver_top
% 3.63/0.98      | v4_pre_topc(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_2345,c_19,c_22,c_677]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6116,plain,
% 3.63/0.98      ( v4_pre_topc(X0,sK0) != iProver_top
% 3.63/0.98      | v4_pre_topc(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 3.63/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/0.98      inference(renaming,[status(thm)],[c_6115]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.63/0.98      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.63/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_596,plain,
% 3.63/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.63/0.98      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2344,plain,
% 3.63/0.98      ( m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.63/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_1854,c_596]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2896,plain,
% 3.63/0.98      ( m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_2344,c_19]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4,plain,
% 3.63/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.63/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7,plain,
% 3.63/0.98      ( ~ v2_compts_1(X0,X1)
% 3.63/0.98      | v2_compts_1(X2,X1)
% 3.63/0.98      | ~ v4_pre_topc(X2,X1)
% 3.63/0.98      | ~ r1_tarski(X2,X0)
% 3.63/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ v2_pre_topc(X1)
% 3.63/0.98      | ~ l1_pre_topc(X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_190,plain,
% 3.63/0.98      ( ~ v2_compts_1(X0,X1)
% 3.63/0.98      | v2_compts_1(X2,X1)
% 3.63/0.98      | ~ v4_pre_topc(X2,X1)
% 3.63/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 3.63/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ v2_pre_topc(X1)
% 3.63/0.98      | ~ l1_pre_topc(X1)
% 3.63/0.98      | X2 != X3
% 3.63/0.98      | X0 != X4 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_7]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_191,plain,
% 3.63/0.98      ( ~ v2_compts_1(X0,X1)
% 3.63/0.98      | v2_compts_1(X2,X1)
% 3.63/0.98      | ~ v4_pre_topc(X2,X1)
% 3.63/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 3.63/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ v2_pre_topc(X1)
% 3.63/0.98      | ~ l1_pre_topc(X1) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_190]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_227,plain,
% 3.63/0.98      ( ~ v2_compts_1(X0,X1)
% 3.63/0.98      | v2_compts_1(X2,X1)
% 3.63/0.98      | ~ v4_pre_topc(X2,X1)
% 3.63/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/0.98      | ~ v2_pre_topc(X1)
% 3.63/0.98      | sK0 != X1 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_191,c_14]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_228,plain,
% 3.63/0.98      ( ~ v2_compts_1(X0,sK0)
% 3.63/0.98      | v2_compts_1(X1,sK0)
% 3.63/0.98      | ~ v4_pre_topc(X1,sK0)
% 3.63/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/0.98      | ~ v2_pre_topc(sK0) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_227]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_230,plain,
% 3.63/0.98      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.63/0.98      | ~ v4_pre_topc(X1,sK0)
% 3.63/0.98      | v2_compts_1(X1,sK0)
% 3.63/0.98      | ~ v2_compts_1(X0,sK0) ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_228,c_15]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_231,plain,
% 3.63/0.98      ( ~ v2_compts_1(X0,sK0)
% 3.63/0.98      | v2_compts_1(X1,sK0)
% 3.63/0.98      | ~ v4_pre_topc(X1,sK0)
% 3.63/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/0.98      inference(renaming,[status(thm)],[c_230]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_588,plain,
% 3.63/0.98      ( v2_compts_1(X0,sK0) != iProver_top
% 3.63/0.98      | v2_compts_1(X1,sK0) = iProver_top
% 3.63/0.98      | v4_pre_topc(X1,sK0) != iProver_top
% 3.63/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.63/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.63/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_231]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1252,plain,
% 3.63/0.98      ( v2_compts_1(X0,sK0) = iProver_top
% 3.63/0.98      | v2_compts_1(sK2,sK0) != iProver_top
% 3.63/0.98      | v4_pre_topc(X0,sK0) != iProver_top
% 3.63/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.63/0.98      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_591,c_588]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_1411,plain,
% 3.63/0.98      ( v2_compts_1(X0,sK0) = iProver_top
% 3.63/0.98      | v4_pre_topc(X0,sK0) != iProver_top
% 3.63/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.63/0.98      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_1252,c_22]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2905,plain,
% 3.63/0.98      ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 3.63/0.98      | v4_pre_topc(k9_subset_1(sK2,X0,sK2),sK0) != iProver_top
% 3.63/0.98      | m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(sK2)) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_2896,c_1411]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4570,plain,
% 3.63/0.98      ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 3.63/0.98      | v4_pre_topc(k9_subset_1(sK2,X0,sK2),sK0) != iProver_top
% 3.63/0.98      | m1_subset_1(sK2,k1_zfmisc_1(sK2)) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_596,c_2905]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5739,plain,
% 3.63/0.98      ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 3.63/0.98      | v4_pre_topc(k9_subset_1(sK2,X0,sK2),sK0) != iProver_top ),
% 3.63/0.98      inference(forward_subsumption_resolution,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_4570,c_608]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6124,plain,
% 3.63/0.98      ( v2_compts_1(k9_subset_1(sK2,X0,sK2),sK0) = iProver_top
% 3.63/0.98      | v4_pre_topc(X0,sK0) != iProver_top
% 3.63/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_6116,c_5739]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8,negated_conjecture,
% 3.63/0.98      ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_594,plain,
% 3.63/0.98      ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2336,plain,
% 3.63/0.98      ( v2_compts_1(k9_subset_1(sK2,sK1,sK2),sK0) != iProver_top ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_1854,c_594]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_10207,plain,
% 3.63/0.98      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.63/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_6124,c_2336]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_679,plain,
% 3.63/0.98      ( ~ v2_compts_1(sK1,sK0)
% 3.63/0.98      | v4_pre_topc(sK1,sK0)
% 3.63/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_170]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_680,plain,
% 3.63/0.98      ( v2_compts_1(sK1,sK0) != iProver_top
% 3.63/0.98      | v4_pre_topc(sK1,sK0) = iProver_top
% 3.63/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_10,negated_conjecture,
% 3.63/0.98      ( v2_compts_1(sK1,sK0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_21,plain,
% 3.63/0.98      ( v2_compts_1(sK1,sK0) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_13,negated_conjecture,
% 3.63/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_18,plain,
% 3.63/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(contradiction,plain,
% 3.63/0.98      ( $false ),
% 3.63/0.98      inference(minisat,[status(thm)],[c_10207,c_680,c_21,c_18]) ).
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  ------                               Statistics
% 3.63/0.98  
% 3.63/0.98  ------ General
% 3.63/0.98  
% 3.63/0.98  abstr_ref_over_cycles:                  0
% 3.63/0.98  abstr_ref_under_cycles:                 0
% 3.63/0.98  gc_basic_clause_elim:                   0
% 3.63/0.98  forced_gc_time:                         0
% 3.63/0.98  parsing_time:                           0.008
% 3.63/0.98  unif_index_cands_time:                  0.
% 3.63/0.98  unif_index_add_time:                    0.
% 3.63/0.98  orderings_time:                         0.
% 3.63/0.98  out_proof_time:                         0.009
% 3.63/0.98  total_time:                             0.34
% 3.63/0.98  num_of_symbols:                         44
% 3.63/0.98  num_of_terms:                           12078
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing
% 3.63/0.98  
% 3.63/0.98  num_of_splits:                          0
% 3.63/0.98  num_of_split_atoms:                     0
% 3.63/0.98  num_of_reused_defs:                     0
% 3.63/0.98  num_eq_ax_congr_red:                    18
% 3.63/0.98  num_of_sem_filtered_clauses:            1
% 3.63/0.98  num_of_subtypes:                        0
% 3.63/0.98  monotx_restored_types:                  0
% 3.63/0.98  sat_num_of_epr_types:                   0
% 3.63/0.98  sat_num_of_non_cyclic_types:            0
% 3.63/0.98  sat_guarded_non_collapsed_types:        0
% 3.63/0.98  num_pure_diseq_elim:                    0
% 3.63/0.98  simp_replaced_by:                       0
% 3.63/0.98  res_preprocessed:                       71
% 3.63/0.98  prep_upred:                             0
% 3.63/0.98  prep_unflattend:                        5
% 3.63/0.98  smt_new_axioms:                         0
% 3.63/0.98  pred_elim_cands:                        3
% 3.63/0.98  pred_elim:                              4
% 3.63/0.98  pred_elim_cl:                           4
% 3.63/0.98  pred_elim_cycles:                       6
% 3.63/0.98  merged_defs:                            0
% 3.63/0.98  merged_defs_ncl:                        0
% 3.63/0.98  bin_hyper_res:                          0
% 3.63/0.98  prep_cycles:                            4
% 3.63/0.98  pred_elim_time:                         0.003
% 3.63/0.98  splitting_time:                         0.
% 3.63/0.98  sem_filter_time:                        0.
% 3.63/0.98  monotx_time:                            0.
% 3.63/0.98  subtype_inf_time:                       0.
% 3.63/0.98  
% 3.63/0.98  ------ Problem properties
% 3.63/0.98  
% 3.63/0.98  clauses:                                12
% 3.63/0.98  conjectures:                            5
% 3.63/0.98  epr:                                    2
% 3.63/0.98  horn:                                   12
% 3.63/0.98  ground:                                 5
% 3.63/0.98  unary:                                  7
% 3.63/0.98  binary:                                 2
% 3.63/0.98  lits:                                   25
% 3.63/0.98  lits_eq:                                2
% 3.63/0.98  fd_pure:                                0
% 3.63/0.98  fd_pseudo:                              0
% 3.63/0.98  fd_cond:                                0
% 3.63/0.98  fd_pseudo_cond:                         0
% 3.63/0.98  ac_symbols:                             0
% 3.63/0.98  
% 3.63/0.98  ------ Propositional Solver
% 3.63/0.98  
% 3.63/0.98  prop_solver_calls:                      30
% 3.63/0.98  prop_fast_solver_calls:                 708
% 3.63/0.98  smt_solver_calls:                       0
% 3.63/0.98  smt_fast_solver_calls:                  0
% 3.63/0.98  prop_num_of_clauses:                    4040
% 3.63/0.98  prop_preprocess_simplified:             6364
% 3.63/0.98  prop_fo_subsumed:                       23
% 3.63/0.98  prop_solver_time:                       0.
% 3.63/0.98  smt_solver_time:                        0.
% 3.63/0.98  smt_fast_solver_time:                   0.
% 3.63/0.98  prop_fast_solver_time:                  0.
% 3.63/0.98  prop_unsat_core_time:                   0.
% 3.63/0.98  
% 3.63/0.98  ------ QBF
% 3.63/0.98  
% 3.63/0.98  qbf_q_res:                              0
% 3.63/0.98  qbf_num_tautologies:                    0
% 3.63/0.98  qbf_prep_cycles:                        0
% 3.63/0.98  
% 3.63/0.98  ------ BMC1
% 3.63/0.98  
% 3.63/0.98  bmc1_current_bound:                     -1
% 3.63/0.98  bmc1_last_solved_bound:                 -1
% 3.63/0.98  bmc1_unsat_core_size:                   -1
% 3.63/0.98  bmc1_unsat_core_parents_size:           -1
% 3.63/0.98  bmc1_merge_next_fun:                    0
% 3.63/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.63/0.98  
% 3.63/0.98  ------ Instantiation
% 3.63/0.98  
% 3.63/0.98  inst_num_of_clauses:                    1029
% 3.63/0.98  inst_num_in_passive:                    268
% 3.63/0.98  inst_num_in_active:                     503
% 3.63/0.98  inst_num_in_unprocessed:                258
% 3.63/0.98  inst_num_of_loops:                      560
% 3.63/0.98  inst_num_of_learning_restarts:          0
% 3.63/0.98  inst_num_moves_active_passive:          54
% 3.63/0.98  inst_lit_activity:                      0
% 3.63/0.98  inst_lit_activity_moves:                1
% 3.63/0.98  inst_num_tautologies:                   0
% 3.63/0.98  inst_num_prop_implied:                  0
% 3.63/0.98  inst_num_existing_simplified:           0
% 3.63/0.98  inst_num_eq_res_simplified:             0
% 3.63/0.98  inst_num_child_elim:                    0
% 3.63/0.98  inst_num_of_dismatching_blockings:      689
% 3.63/0.98  inst_num_of_non_proper_insts:           983
% 3.63/0.98  inst_num_of_duplicates:                 0
% 3.63/0.98  inst_inst_num_from_inst_to_res:         0
% 3.63/0.98  inst_dismatching_checking_time:         0.
% 3.63/0.98  
% 3.63/0.98  ------ Resolution
% 3.63/0.98  
% 3.63/0.98  res_num_of_clauses:                     0
% 3.63/0.98  res_num_in_passive:                     0
% 3.63/0.98  res_num_in_active:                      0
% 3.63/0.98  res_num_of_loops:                       75
% 3.63/0.98  res_forward_subset_subsumed:            55
% 3.63/0.98  res_backward_subset_subsumed:           0
% 3.63/0.98  res_forward_subsumed:                   0
% 3.63/0.98  res_backward_subsumed:                  0
% 3.63/0.98  res_forward_subsumption_resolution:     0
% 3.63/0.98  res_backward_subsumption_resolution:    0
% 3.63/0.98  res_clause_to_clause_subsumption:       1760
% 3.63/0.98  res_orphan_elimination:                 0
% 3.63/0.98  res_tautology_del:                      30
% 3.63/0.98  res_num_eq_res_simplified:              0
% 3.63/0.98  res_num_sel_changes:                    0
% 3.63/0.98  res_moves_from_active_to_pass:          0
% 3.63/0.98  
% 3.63/0.98  ------ Superposition
% 3.63/0.98  
% 3.63/0.98  sup_time_total:                         0.
% 3.63/0.98  sup_time_generating:                    0.
% 3.63/0.98  sup_time_sim_full:                      0.
% 3.63/0.98  sup_time_sim_immed:                     0.
% 3.63/0.98  
% 3.63/0.98  sup_num_of_clauses:                     415
% 3.63/0.98  sup_num_in_active:                      87
% 3.63/0.98  sup_num_in_passive:                     328
% 3.63/0.98  sup_num_of_loops:                       110
% 3.63/0.98  sup_fw_superposition:                   273
% 3.63/0.98  sup_bw_superposition:                   296
% 3.63/0.98  sup_immediate_simplified:               81
% 3.63/0.98  sup_given_eliminated:                   4
% 3.63/0.98  comparisons_done:                       0
% 3.63/0.98  comparisons_avoided:                    0
% 3.63/0.98  
% 3.63/0.98  ------ Simplifications
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  sim_fw_subset_subsumed:                 11
% 3.63/0.98  sim_bw_subset_subsumed:                 21
% 3.63/0.98  sim_fw_subsumed:                        12
% 3.63/0.98  sim_bw_subsumed:                        0
% 3.63/0.98  sim_fw_subsumption_res:                 8
% 3.63/0.98  sim_bw_subsumption_res:                 0
% 3.63/0.98  sim_tautology_del:                      10
% 3.63/0.98  sim_eq_tautology_del:                   0
% 3.63/0.98  sim_eq_res_simp:                        0
% 3.63/0.98  sim_fw_demodulated:                     41
% 3.63/0.98  sim_bw_demodulated:                     34
% 3.63/0.98  sim_light_normalised:                   21
% 3.63/0.98  sim_joinable_taut:                      0
% 3.63/0.98  sim_joinable_simp:                      0
% 3.63/0.98  sim_ac_normalised:                      0
% 3.63/0.98  sim_smt_subsumption:                    0
% 3.63/0.98  
%------------------------------------------------------------------------------
