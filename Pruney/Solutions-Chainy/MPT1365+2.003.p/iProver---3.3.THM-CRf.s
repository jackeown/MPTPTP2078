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
% DateTime   : Thu Dec  3 12:17:57 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 514 expanded)
%              Number of clauses        :   81 ( 149 expanded)
%              Number of leaves         :   15 ( 151 expanded)
%              Depth                    :   19
%              Number of atoms          :  473 (3144 expanded)
%              Number of equality atoms :  119 ( 189 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f35,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34,f33,f32])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1148,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1671,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1148])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1142,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1146,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2221,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1146])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_142,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_143,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_142])).

cnf(c_180,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_143])).

cnf(c_1140,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_1151,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1140,c_4])).

cnf(c_2876,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_2221,c_1151])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_330,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_331,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ v4_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_19])).

cnf(c_336,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_335])).

cnf(c_1137,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_2992,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_1137])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,negated_conjecture,
    ( v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,plain,
    ( v2_compts_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,negated_conjecture,
    ( v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_279,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_280,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_284,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_280,c_20,c_19])).

cnf(c_1186,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_1187,plain,
    ( v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1186])).

cnf(c_4095,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2992,c_24,c_27,c_1187])).

cnf(c_4096,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4095])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_1135,plain,
    ( u1_struct_0(k1_pre_topc(sK0,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_1417,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1142,c_1135])).

cnf(c_7,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | X4 != X1
    | k1_pre_topc(X1,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_259,c_19])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_1136,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1)))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_1554,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1417,c_1136])).

cnf(c_2196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1554,c_24])).

cnf(c_2197,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2196])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1141,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_304,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_305,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_307,plain,
    ( ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(X1,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v2_compts_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_305,c_19])).

cnf(c_308,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0) ),
    inference(renaming,[status(thm)],[c_307])).

cnf(c_1138,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(X1,sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_1977,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1138])).

cnf(c_15,negated_conjecture,
    ( v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2038,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1977,c_26])).

cnf(c_2202,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_2038])).

cnf(c_23,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1418,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1141,c_1135])).

cnf(c_1147,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2305,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X1,u1_struct_0(k1_pre_topc(sK0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1136])).

cnf(c_3229,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_2305])).

cnf(c_3502,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v2_compts_1(X0,sK0) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2202,c_23,c_2038,c_3229])).

cnf(c_3503,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3502])).

cnf(c_4104,plain,
    ( v2_compts_1(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4096,c_3503])).

cnf(c_11366,plain,
    ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_4104])).

cnf(c_13,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1145,plain,
    ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2990,plain,
    ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2876,c_1145])).

cnf(c_1189,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_1190,plain,
    ( v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1189])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11366,c_2990,c_1190,c_26,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:20:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.73/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.73/1.03  
% 0.73/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.73/1.03  
% 0.73/1.03  ------  iProver source info
% 0.73/1.03  
% 0.73/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.73/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.73/1.03  git: non_committed_changes: false
% 0.73/1.03  git: last_make_outside_of_git: false
% 0.73/1.03  
% 0.73/1.03  ------ 
% 0.73/1.03  
% 0.73/1.03  ------ Input Options
% 0.73/1.03  
% 0.73/1.03  --out_options                           all
% 0.73/1.03  --tptp_safe_out                         true
% 0.73/1.03  --problem_path                          ""
% 0.73/1.03  --include_path                          ""
% 0.73/1.03  --clausifier                            res/vclausify_rel
% 0.73/1.03  --clausifier_options                    ""
% 0.73/1.03  --stdin                                 false
% 0.73/1.03  --stats_out                             all
% 0.73/1.03  
% 0.73/1.03  ------ General Options
% 0.73/1.03  
% 0.73/1.03  --fof                                   false
% 0.73/1.03  --time_out_real                         305.
% 0.73/1.03  --time_out_virtual                      -1.
% 0.73/1.03  --symbol_type_check                     false
% 0.73/1.03  --clausify_out                          false
% 0.73/1.03  --sig_cnt_out                           false
% 0.73/1.03  --trig_cnt_out                          false
% 0.73/1.03  --trig_cnt_out_tolerance                1.
% 0.73/1.03  --trig_cnt_out_sk_spl                   false
% 0.73/1.03  --abstr_cl_out                          false
% 0.73/1.03  
% 0.73/1.03  ------ Global Options
% 0.73/1.03  
% 0.73/1.03  --schedule                              default
% 0.73/1.03  --add_important_lit                     false
% 0.73/1.03  --prop_solver_per_cl                    1000
% 0.73/1.03  --min_unsat_core                        false
% 0.73/1.03  --soft_assumptions                      false
% 0.73/1.03  --soft_lemma_size                       3
% 0.73/1.03  --prop_impl_unit_size                   0
% 0.73/1.03  --prop_impl_unit                        []
% 0.73/1.03  --share_sel_clauses                     true
% 0.73/1.03  --reset_solvers                         false
% 0.73/1.03  --bc_imp_inh                            [conj_cone]
% 0.73/1.03  --conj_cone_tolerance                   3.
% 0.73/1.03  --extra_neg_conj                        none
% 0.73/1.03  --large_theory_mode                     true
% 0.73/1.03  --prolific_symb_bound                   200
% 0.73/1.03  --lt_threshold                          2000
% 0.73/1.03  --clause_weak_htbl                      true
% 0.73/1.03  --gc_record_bc_elim                     false
% 0.73/1.03  
% 0.73/1.03  ------ Preprocessing Options
% 0.73/1.03  
% 0.73/1.03  --preprocessing_flag                    true
% 0.73/1.03  --time_out_prep_mult                    0.1
% 0.73/1.03  --splitting_mode                        input
% 0.73/1.03  --splitting_grd                         true
% 0.73/1.03  --splitting_cvd                         false
% 0.73/1.03  --splitting_cvd_svl                     false
% 0.73/1.03  --splitting_nvd                         32
% 0.73/1.03  --sub_typing                            true
% 0.73/1.03  --prep_gs_sim                           true
% 0.73/1.03  --prep_unflatten                        true
% 0.73/1.03  --prep_res_sim                          true
% 0.73/1.03  --prep_upred                            true
% 0.73/1.03  --prep_sem_filter                       exhaustive
% 0.73/1.03  --prep_sem_filter_out                   false
% 0.73/1.03  --pred_elim                             true
% 0.73/1.03  --res_sim_input                         true
% 0.73/1.03  --eq_ax_congr_red                       true
% 0.73/1.03  --pure_diseq_elim                       true
% 0.73/1.03  --brand_transform                       false
% 0.73/1.03  --non_eq_to_eq                          false
% 0.73/1.03  --prep_def_merge                        true
% 0.73/1.03  --prep_def_merge_prop_impl              false
% 0.73/1.03  --prep_def_merge_mbd                    true
% 0.73/1.03  --prep_def_merge_tr_red                 false
% 0.73/1.03  --prep_def_merge_tr_cl                  false
% 0.73/1.03  --smt_preprocessing                     true
% 0.73/1.03  --smt_ac_axioms                         fast
% 0.73/1.03  --preprocessed_out                      false
% 0.73/1.03  --preprocessed_stats                    false
% 0.73/1.03  
% 0.73/1.03  ------ Abstraction refinement Options
% 0.73/1.03  
% 0.73/1.03  --abstr_ref                             []
% 0.73/1.03  --abstr_ref_prep                        false
% 0.73/1.03  --abstr_ref_until_sat                   false
% 0.73/1.03  --abstr_ref_sig_restrict                funpre
% 0.73/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.73/1.03  --abstr_ref_under                       []
% 0.73/1.03  
% 0.73/1.03  ------ SAT Options
% 0.73/1.03  
% 0.73/1.03  --sat_mode                              false
% 0.73/1.03  --sat_fm_restart_options                ""
% 0.73/1.03  --sat_gr_def                            false
% 0.73/1.03  --sat_epr_types                         true
% 0.73/1.03  --sat_non_cyclic_types                  false
% 0.73/1.03  --sat_finite_models                     false
% 0.73/1.03  --sat_fm_lemmas                         false
% 0.73/1.03  --sat_fm_prep                           false
% 0.73/1.03  --sat_fm_uc_incr                        true
% 0.73/1.03  --sat_out_model                         small
% 0.73/1.03  --sat_out_clauses                       false
% 0.73/1.03  
% 0.73/1.03  ------ QBF Options
% 0.73/1.03  
% 0.73/1.03  --qbf_mode                              false
% 0.73/1.03  --qbf_elim_univ                         false
% 0.73/1.03  --qbf_dom_inst                          none
% 0.73/1.03  --qbf_dom_pre_inst                      false
% 0.73/1.03  --qbf_sk_in                             false
% 0.73/1.03  --qbf_pred_elim                         true
% 0.73/1.03  --qbf_split                             512
% 0.73/1.03  
% 0.73/1.03  ------ BMC1 Options
% 0.73/1.03  
% 0.73/1.03  --bmc1_incremental                      false
% 0.73/1.03  --bmc1_axioms                           reachable_all
% 0.73/1.03  --bmc1_min_bound                        0
% 0.73/1.03  --bmc1_max_bound                        -1
% 0.73/1.03  --bmc1_max_bound_default                -1
% 0.73/1.03  --bmc1_symbol_reachability              true
% 0.73/1.03  --bmc1_property_lemmas                  false
% 0.73/1.03  --bmc1_k_induction                      false
% 0.73/1.03  --bmc1_non_equiv_states                 false
% 0.73/1.03  --bmc1_deadlock                         false
% 0.73/1.03  --bmc1_ucm                              false
% 0.73/1.03  --bmc1_add_unsat_core                   none
% 0.73/1.03  --bmc1_unsat_core_children              false
% 0.73/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.73/1.03  --bmc1_out_stat                         full
% 0.73/1.03  --bmc1_ground_init                      false
% 0.73/1.03  --bmc1_pre_inst_next_state              false
% 0.73/1.03  --bmc1_pre_inst_state                   false
% 0.73/1.03  --bmc1_pre_inst_reach_state             false
% 0.73/1.03  --bmc1_out_unsat_core                   false
% 0.73/1.03  --bmc1_aig_witness_out                  false
% 0.73/1.03  --bmc1_verbose                          false
% 0.73/1.03  --bmc1_dump_clauses_tptp                false
% 0.73/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.73/1.03  --bmc1_dump_file                        -
% 0.73/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.73/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.73/1.03  --bmc1_ucm_extend_mode                  1
% 0.73/1.03  --bmc1_ucm_init_mode                    2
% 0.73/1.03  --bmc1_ucm_cone_mode                    none
% 0.73/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.73/1.03  --bmc1_ucm_relax_model                  4
% 0.73/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.73/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.73/1.03  --bmc1_ucm_layered_model                none
% 0.73/1.03  --bmc1_ucm_max_lemma_size               10
% 0.73/1.03  
% 0.73/1.03  ------ AIG Options
% 0.73/1.03  
% 0.73/1.03  --aig_mode                              false
% 0.73/1.03  
% 0.73/1.03  ------ Instantiation Options
% 0.73/1.03  
% 0.73/1.03  --instantiation_flag                    true
% 0.73/1.03  --inst_sos_flag                         true
% 0.73/1.03  --inst_sos_phase                        true
% 0.73/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.73/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.73/1.03  --inst_lit_sel_side                     num_symb
% 0.73/1.03  --inst_solver_per_active                1400
% 0.73/1.03  --inst_solver_calls_frac                1.
% 0.73/1.03  --inst_passive_queue_type               priority_queues
% 0.73/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.73/1.03  --inst_passive_queues_freq              [25;2]
% 0.73/1.03  --inst_dismatching                      true
% 0.73/1.03  --inst_eager_unprocessed_to_passive     true
% 0.73/1.03  --inst_prop_sim_given                   true
% 0.73/1.03  --inst_prop_sim_new                     false
% 0.73/1.03  --inst_subs_new                         false
% 0.73/1.03  --inst_eq_res_simp                      false
% 0.73/1.03  --inst_subs_given                       false
% 0.73/1.03  --inst_orphan_elimination               true
% 0.73/1.03  --inst_learning_loop_flag               true
% 0.73/1.03  --inst_learning_start                   3000
% 0.73/1.03  --inst_learning_factor                  2
% 0.73/1.03  --inst_start_prop_sim_after_learn       3
% 0.73/1.03  --inst_sel_renew                        solver
% 0.73/1.03  --inst_lit_activity_flag                true
% 0.73/1.03  --inst_restr_to_given                   false
% 0.73/1.03  --inst_activity_threshold               500
% 0.73/1.03  --inst_out_proof                        true
% 0.73/1.03  
% 0.73/1.03  ------ Resolution Options
% 0.73/1.03  
% 0.73/1.03  --resolution_flag                       true
% 0.73/1.03  --res_lit_sel                           adaptive
% 0.73/1.03  --res_lit_sel_side                      none
% 0.73/1.03  --res_ordering                          kbo
% 0.73/1.03  --res_to_prop_solver                    active
% 0.73/1.03  --res_prop_simpl_new                    false
% 0.73/1.03  --res_prop_simpl_given                  true
% 0.73/1.03  --res_passive_queue_type                priority_queues
% 0.73/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.73/1.03  --res_passive_queues_freq               [15;5]
% 0.73/1.03  --res_forward_subs                      full
% 0.73/1.03  --res_backward_subs                     full
% 0.73/1.03  --res_forward_subs_resolution           true
% 0.73/1.03  --res_backward_subs_resolution          true
% 0.73/1.03  --res_orphan_elimination                true
% 0.73/1.03  --res_time_limit                        2.
% 0.73/1.03  --res_out_proof                         true
% 0.73/1.03  
% 0.73/1.03  ------ Superposition Options
% 0.73/1.03  
% 0.73/1.03  --superposition_flag                    true
% 0.73/1.03  --sup_passive_queue_type                priority_queues
% 0.73/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.73/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.73/1.03  --demod_completeness_check              fast
% 0.73/1.03  --demod_use_ground                      true
% 0.73/1.03  --sup_to_prop_solver                    passive
% 0.73/1.03  --sup_prop_simpl_new                    true
% 0.73/1.03  --sup_prop_simpl_given                  true
% 0.73/1.03  --sup_fun_splitting                     true
% 0.73/1.03  --sup_smt_interval                      50000
% 0.73/1.03  
% 0.73/1.03  ------ Superposition Simplification Setup
% 0.73/1.03  
% 0.73/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 0.73/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 0.73/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 0.73/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.73/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 0.73/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 0.73/1.03  --sup_immed_triv                        [TrivRules]
% 0.73/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.73/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.73/1.03  --sup_immed_bw_main                     []
% 0.73/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 0.73/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.73/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.73/1.03  --sup_input_bw                          []
% 0.73/1.03  
% 0.73/1.03  ------ Combination Options
% 0.73/1.03  
% 0.73/1.03  --comb_res_mult                         3
% 0.73/1.03  --comb_sup_mult                         2
% 0.73/1.03  --comb_inst_mult                        10
% 0.73/1.03  
% 0.73/1.03  ------ Debug Options
% 0.73/1.03  
% 0.73/1.03  --dbg_backtrace                         false
% 0.73/1.03  --dbg_dump_prop_clauses                 false
% 0.73/1.03  --dbg_dump_prop_clauses_file            -
% 0.73/1.03  --dbg_out_stat                          false
% 0.73/1.03  ------ Parsing...
% 0.73/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.73/1.03  
% 0.73/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 0.73/1.03  
% 0.73/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.73/1.03  
% 0.73/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.73/1.03  ------ Proving...
% 0.73/1.03  ------ Problem Properties 
% 0.73/1.03  
% 0.73/1.03  
% 0.73/1.03  clauses                                 17
% 0.73/1.03  conjectures                             5
% 0.73/1.03  EPR                                     2
% 0.73/1.03  Horn                                    17
% 0.73/1.03  unary                                   8
% 0.73/1.03  binary                                  5
% 0.73/1.03  lits                                    35
% 0.73/1.03  lits eq                                 5
% 0.73/1.03  fd_pure                                 0
% 0.73/1.03  fd_pseudo                               0
% 0.73/1.03  fd_cond                                 0
% 0.73/1.03  fd_pseudo_cond                          0
% 0.73/1.03  AC symbols                              0
% 0.73/1.03  
% 0.73/1.03  ------ Schedule dynamic 5 is on 
% 0.73/1.03  
% 0.73/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.73/1.03  
% 0.73/1.03  
% 0.73/1.03  ------ 
% 0.73/1.03  Current options:
% 0.73/1.03  ------ 
% 0.73/1.03  
% 0.73/1.03  ------ Input Options
% 0.73/1.03  
% 0.73/1.03  --out_options                           all
% 0.73/1.03  --tptp_safe_out                         true
% 0.73/1.03  --problem_path                          ""
% 0.73/1.03  --include_path                          ""
% 0.73/1.03  --clausifier                            res/vclausify_rel
% 0.73/1.03  --clausifier_options                    ""
% 0.73/1.03  --stdin                                 false
% 0.73/1.03  --stats_out                             all
% 0.73/1.03  
% 0.73/1.03  ------ General Options
% 0.73/1.03  
% 0.73/1.03  --fof                                   false
% 0.73/1.03  --time_out_real                         305.
% 0.73/1.03  --time_out_virtual                      -1.
% 0.73/1.03  --symbol_type_check                     false
% 0.73/1.03  --clausify_out                          false
% 0.73/1.03  --sig_cnt_out                           false
% 0.73/1.03  --trig_cnt_out                          false
% 0.73/1.03  --trig_cnt_out_tolerance                1.
% 0.73/1.03  --trig_cnt_out_sk_spl                   false
% 0.73/1.03  --abstr_cl_out                          false
% 0.73/1.03  
% 0.73/1.03  ------ Global Options
% 0.73/1.03  
% 0.73/1.03  --schedule                              default
% 0.73/1.03  --add_important_lit                     false
% 0.73/1.03  --prop_solver_per_cl                    1000
% 0.73/1.03  --min_unsat_core                        false
% 0.73/1.03  --soft_assumptions                      false
% 0.73/1.03  --soft_lemma_size                       3
% 0.73/1.03  --prop_impl_unit_size                   0
% 0.73/1.03  --prop_impl_unit                        []
% 0.73/1.03  --share_sel_clauses                     true
% 0.73/1.03  --reset_solvers                         false
% 0.73/1.03  --bc_imp_inh                            [conj_cone]
% 0.73/1.03  --conj_cone_tolerance                   3.
% 0.73/1.03  --extra_neg_conj                        none
% 0.73/1.03  --large_theory_mode                     true
% 0.73/1.03  --prolific_symb_bound                   200
% 0.73/1.03  --lt_threshold                          2000
% 0.73/1.03  --clause_weak_htbl                      true
% 0.73/1.03  --gc_record_bc_elim                     false
% 0.73/1.03  
% 0.73/1.03  ------ Preprocessing Options
% 0.73/1.03  
% 0.73/1.03  --preprocessing_flag                    true
% 0.73/1.03  --time_out_prep_mult                    0.1
% 0.73/1.03  --splitting_mode                        input
% 0.73/1.03  --splitting_grd                         true
% 0.73/1.03  --splitting_cvd                         false
% 0.73/1.03  --splitting_cvd_svl                     false
% 0.73/1.03  --splitting_nvd                         32
% 0.73/1.03  --sub_typing                            true
% 0.73/1.03  --prep_gs_sim                           true
% 0.73/1.03  --prep_unflatten                        true
% 0.73/1.03  --prep_res_sim                          true
% 0.73/1.03  --prep_upred                            true
% 0.73/1.03  --prep_sem_filter                       exhaustive
% 0.73/1.03  --prep_sem_filter_out                   false
% 0.73/1.03  --pred_elim                             true
% 0.73/1.03  --res_sim_input                         true
% 0.73/1.03  --eq_ax_congr_red                       true
% 0.73/1.03  --pure_diseq_elim                       true
% 0.73/1.03  --brand_transform                       false
% 0.73/1.03  --non_eq_to_eq                          false
% 0.73/1.03  --prep_def_merge                        true
% 0.73/1.03  --prep_def_merge_prop_impl              false
% 0.73/1.03  --prep_def_merge_mbd                    true
% 0.73/1.03  --prep_def_merge_tr_red                 false
% 0.73/1.03  --prep_def_merge_tr_cl                  false
% 0.73/1.03  --smt_preprocessing                     true
% 0.73/1.03  --smt_ac_axioms                         fast
% 0.73/1.03  --preprocessed_out                      false
% 0.73/1.03  --preprocessed_stats                    false
% 0.73/1.03  
% 0.73/1.03  ------ Abstraction refinement Options
% 0.73/1.03  
% 0.73/1.03  --abstr_ref                             []
% 0.73/1.03  --abstr_ref_prep                        false
% 0.73/1.03  --abstr_ref_until_sat                   false
% 0.73/1.03  --abstr_ref_sig_restrict                funpre
% 0.73/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.73/1.03  --abstr_ref_under                       []
% 0.73/1.03  
% 0.73/1.03  ------ SAT Options
% 0.73/1.03  
% 0.73/1.03  --sat_mode                              false
% 0.73/1.03  --sat_fm_restart_options                ""
% 0.73/1.03  --sat_gr_def                            false
% 0.73/1.03  --sat_epr_types                         true
% 0.73/1.03  --sat_non_cyclic_types                  false
% 0.73/1.03  --sat_finite_models                     false
% 0.73/1.03  --sat_fm_lemmas                         false
% 0.73/1.03  --sat_fm_prep                           false
% 0.73/1.03  --sat_fm_uc_incr                        true
% 0.73/1.03  --sat_out_model                         small
% 0.73/1.03  --sat_out_clauses                       false
% 0.73/1.03  
% 0.73/1.03  ------ QBF Options
% 0.73/1.03  
% 0.73/1.03  --qbf_mode                              false
% 0.73/1.03  --qbf_elim_univ                         false
% 0.73/1.03  --qbf_dom_inst                          none
% 0.73/1.03  --qbf_dom_pre_inst                      false
% 0.73/1.03  --qbf_sk_in                             false
% 0.73/1.03  --qbf_pred_elim                         true
% 0.73/1.03  --qbf_split                             512
% 0.73/1.03  
% 0.73/1.03  ------ BMC1 Options
% 0.73/1.03  
% 0.73/1.03  --bmc1_incremental                      false
% 0.73/1.03  --bmc1_axioms                           reachable_all
% 0.73/1.03  --bmc1_min_bound                        0
% 0.73/1.03  --bmc1_max_bound                        -1
% 0.73/1.03  --bmc1_max_bound_default                -1
% 0.73/1.03  --bmc1_symbol_reachability              true
% 0.73/1.03  --bmc1_property_lemmas                  false
% 0.73/1.03  --bmc1_k_induction                      false
% 0.73/1.03  --bmc1_non_equiv_states                 false
% 0.73/1.03  --bmc1_deadlock                         false
% 0.73/1.03  --bmc1_ucm                              false
% 0.73/1.03  --bmc1_add_unsat_core                   none
% 0.73/1.03  --bmc1_unsat_core_children              false
% 0.73/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.73/1.03  --bmc1_out_stat                         full
% 0.73/1.03  --bmc1_ground_init                      false
% 0.73/1.03  --bmc1_pre_inst_next_state              false
% 0.73/1.03  --bmc1_pre_inst_state                   false
% 0.73/1.03  --bmc1_pre_inst_reach_state             false
% 0.73/1.03  --bmc1_out_unsat_core                   false
% 0.73/1.03  --bmc1_aig_witness_out                  false
% 0.73/1.03  --bmc1_verbose                          false
% 0.73/1.03  --bmc1_dump_clauses_tptp                false
% 0.73/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.73/1.03  --bmc1_dump_file                        -
% 0.73/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.73/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.73/1.03  --bmc1_ucm_extend_mode                  1
% 0.73/1.03  --bmc1_ucm_init_mode                    2
% 0.73/1.03  --bmc1_ucm_cone_mode                    none
% 0.73/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.73/1.03  --bmc1_ucm_relax_model                  4
% 0.73/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.73/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.73/1.03  --bmc1_ucm_layered_model                none
% 0.73/1.03  --bmc1_ucm_max_lemma_size               10
% 0.73/1.03  
% 0.73/1.03  ------ AIG Options
% 0.73/1.03  
% 0.73/1.03  --aig_mode                              false
% 0.73/1.03  
% 0.73/1.03  ------ Instantiation Options
% 0.73/1.03  
% 0.73/1.03  --instantiation_flag                    true
% 0.73/1.03  --inst_sos_flag                         true
% 0.73/1.03  --inst_sos_phase                        true
% 0.73/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.73/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.73/1.03  --inst_lit_sel_side                     none
% 0.73/1.03  --inst_solver_per_active                1400
% 0.73/1.03  --inst_solver_calls_frac                1.
% 0.73/1.03  --inst_passive_queue_type               priority_queues
% 0.73/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.73/1.03  --inst_passive_queues_freq              [25;2]
% 0.73/1.03  --inst_dismatching                      true
% 0.73/1.03  --inst_eager_unprocessed_to_passive     true
% 0.73/1.03  --inst_prop_sim_given                   true
% 0.73/1.03  --inst_prop_sim_new                     false
% 0.73/1.03  --inst_subs_new                         false
% 0.73/1.03  --inst_eq_res_simp                      false
% 0.73/1.03  --inst_subs_given                       false
% 0.73/1.03  --inst_orphan_elimination               true
% 0.73/1.03  --inst_learning_loop_flag               true
% 0.73/1.03  --inst_learning_start                   3000
% 0.73/1.03  --inst_learning_factor                  2
% 0.73/1.03  --inst_start_prop_sim_after_learn       3
% 0.73/1.03  --inst_sel_renew                        solver
% 0.73/1.03  --inst_lit_activity_flag                true
% 0.73/1.03  --inst_restr_to_given                   false
% 0.73/1.03  --inst_activity_threshold               500
% 0.73/1.03  --inst_out_proof                        true
% 0.73/1.03  
% 0.73/1.03  ------ Resolution Options
% 0.73/1.03  
% 0.73/1.03  --resolution_flag                       false
% 0.73/1.03  --res_lit_sel                           adaptive
% 0.73/1.03  --res_lit_sel_side                      none
% 0.73/1.03  --res_ordering                          kbo
% 0.73/1.03  --res_to_prop_solver                    active
% 0.73/1.03  --res_prop_simpl_new                    false
% 0.73/1.03  --res_prop_simpl_given                  true
% 0.73/1.03  --res_passive_queue_type                priority_queues
% 0.73/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.73/1.03  --res_passive_queues_freq               [15;5]
% 0.73/1.03  --res_forward_subs                      full
% 0.73/1.03  --res_backward_subs                     full
% 0.73/1.03  --res_forward_subs_resolution           true
% 0.73/1.03  --res_backward_subs_resolution          true
% 0.73/1.03  --res_orphan_elimination                true
% 0.73/1.03  --res_time_limit                        2.
% 0.73/1.03  --res_out_proof                         true
% 0.73/1.03  
% 0.73/1.03  ------ Superposition Options
% 0.73/1.03  
% 0.73/1.03  --superposition_flag                    true
% 0.73/1.03  --sup_passive_queue_type                priority_queues
% 0.73/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.73/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.73/1.03  --demod_completeness_check              fast
% 0.73/1.03  --demod_use_ground                      true
% 0.73/1.03  --sup_to_prop_solver                    passive
% 0.73/1.03  --sup_prop_simpl_new                    true
% 0.73/1.03  --sup_prop_simpl_given                  true
% 0.73/1.03  --sup_fun_splitting                     true
% 0.73/1.03  --sup_smt_interval                      50000
% 0.73/1.03  
% 0.73/1.03  ------ Superposition Simplification Setup
% 0.73/1.03  
% 0.73/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 0.73/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 0.73/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 0.73/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 0.73/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.73/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 0.73/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 0.73/1.03  --sup_immed_triv                        [TrivRules]
% 0.73/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.73/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.73/1.03  --sup_immed_bw_main                     []
% 0.73/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 0.73/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.73/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.73/1.03  --sup_input_bw                          []
% 0.73/1.03  
% 0.73/1.03  ------ Combination Options
% 0.73/1.03  
% 0.73/1.03  --comb_res_mult                         3
% 0.73/1.03  --comb_sup_mult                         2
% 0.73/1.03  --comb_inst_mult                        10
% 0.73/1.03  
% 0.73/1.03  ------ Debug Options
% 0.73/1.03  
% 0.73/1.03  --dbg_backtrace                         false
% 0.73/1.03  --dbg_dump_prop_clauses                 false
% 0.73/1.03  --dbg_dump_prop_clauses_file            -
% 0.73/1.03  --dbg_out_stat                          false
% 0.73/1.03  
% 0.73/1.03  
% 0.73/1.03  
% 0.73/1.03  
% 0.73/1.03  ------ Proving...
% 0.73/1.03  
% 0.73/1.03  
% 0.73/1.03  % SZS status Theorem for theBenchmark.p
% 0.73/1.03  
% 0.73/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.73/1.03  
% 0.73/1.03  fof(f6,axiom,(
% 0.73/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.73/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.03  
% 0.73/1.03  fof(f41,plain,(
% 0.73/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.73/1.03    inference(cnf_transformation,[],[f6])).
% 0.73/1.03  
% 0.73/1.03  fof(f3,axiom,(
% 0.73/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.73/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.03  
% 0.73/1.03  fof(f38,plain,(
% 0.73/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.73/1.03    inference(cnf_transformation,[],[f3])).
% 0.73/1.03  
% 0.73/1.03  fof(f60,plain,(
% 0.73/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.73/1.03    inference(definition_unfolding,[],[f41,f38])).
% 0.73/1.03  
% 0.73/1.03  fof(f2,axiom,(
% 0.73/1.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.73/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.03  
% 0.73/1.03  fof(f37,plain,(
% 0.73/1.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.73/1.03    inference(cnf_transformation,[],[f2])).
% 0.73/1.03  
% 0.73/1.03  fof(f14,conjecture,(
% 0.73/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.73/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.03  
% 0.73/1.03  fof(f15,negated_conjecture,(
% 0.73/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.73/1.03    inference(negated_conjecture,[],[f14])).
% 0.73/1.03  
% 0.73/1.03  fof(f29,plain,(
% 0.73/1.03    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.73/1.03    inference(ennf_transformation,[],[f15])).
% 0.73/1.03  
% 0.73/1.03  fof(f30,plain,(
% 0.73/1.03    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.73/1.03    inference(flattening,[],[f29])).
% 0.73/1.03  
% 0.73/1.03  fof(f34,plain,(
% 0.73/1.03    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v2_compts_1(sK2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.73/1.03    introduced(choice_axiom,[])).
% 0.73/1.03  
% 0.73/1.03  fof(f33,plain,(
% 0.73/1.03    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(sK1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.73/1.03    introduced(choice_axiom,[])).
% 0.73/1.03  
% 0.73/1.03  fof(f32,plain,(
% 0.73/1.03    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.73/1.03    introduced(choice_axiom,[])).
% 0.73/1.03  
% 0.73/1.03  fof(f35,plain,(
% 0.73/1.03    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.73/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34,f33,f32])).
% 0.73/1.03  
% 0.73/1.03  fof(f53,plain,(
% 0.73/1.03    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.73/1.03    inference(cnf_transformation,[],[f35])).
% 0.73/1.03  
% 0.73/1.03  fof(f7,axiom,(
% 0.73/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.73/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.03  
% 0.73/1.03  fof(f31,plain,(
% 0.73/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.73/1.03    inference(nnf_transformation,[],[f7])).
% 0.73/1.03  
% 0.73/1.03  fof(f42,plain,(
% 0.73/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.73/1.03    inference(cnf_transformation,[],[f31])).
% 0.73/1.03  
% 0.73/1.03  fof(f5,axiom,(
% 0.73/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 0.73/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.03  
% 0.73/1.03  fof(f18,plain,(
% 0.73/1.03    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.73/1.03    inference(ennf_transformation,[],[f5])).
% 0.73/1.03  
% 0.73/1.03  fof(f40,plain,(
% 0.73/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.73/1.03    inference(cnf_transformation,[],[f18])).
% 0.73/1.03  
% 0.73/1.03  fof(f59,plain,(
% 0.73/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.73/1.03    inference(definition_unfolding,[],[f40,f38])).
% 0.73/1.03  
% 0.73/1.03  fof(f43,plain,(
% 0.73/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.73/1.03    inference(cnf_transformation,[],[f31])).
% 0.73/1.03  
% 0.73/1.03  fof(f11,axiom,(
% 0.73/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.73/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.03  
% 0.73/1.03  fof(f23,plain,(
% 0.73/1.03    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.73/1.03    inference(ennf_transformation,[],[f11])).
% 0.73/1.03  
% 0.73/1.03  fof(f24,plain,(
% 0.73/1.03    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.73/1.03    inference(flattening,[],[f23])).
% 0.73/1.03  
% 0.73/1.03  fof(f47,plain,(
% 0.73/1.03    ( ! [X2,X0,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.73/1.03    inference(cnf_transformation,[],[f24])).
% 0.73/1.03  
% 0.73/1.03  fof(f50,plain,(
% 0.73/1.03    v2_pre_topc(sK0)),
% 0.73/1.03    inference(cnf_transformation,[],[f35])).
% 0.73/1.03  
% 0.73/1.03  fof(f51,plain,(
% 0.73/1.03    l1_pre_topc(sK0)),
% 0.73/1.03    inference(cnf_transformation,[],[f35])).
% 0.73/1.03  
% 0.73/1.03  fof(f56,plain,(
% 0.73/1.03    v2_compts_1(sK2,sK0)),
% 0.73/1.03    inference(cnf_transformation,[],[f35])).
% 0.73/1.03  
% 0.73/1.03  fof(f12,axiom,(
% 0.73/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.73/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.03  
% 0.73/1.03  fof(f25,plain,(
% 0.73/1.03    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.73/1.03    inference(ennf_transformation,[],[f12])).
% 0.73/1.03  
% 0.73/1.03  fof(f26,plain,(
% 0.73/1.03    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.73/1.03    inference(flattening,[],[f25])).
% 0.73/1.03  
% 0.73/1.03  fof(f48,plain,(
% 0.73/1.03    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.73/1.03    inference(cnf_transformation,[],[f26])).
% 0.73/1.03  
% 0.73/1.03  fof(f54,plain,(
% 0.73/1.03    v8_pre_topc(sK0)),
% 0.73/1.03    inference(cnf_transformation,[],[f35])).
% 0.73/1.03  
% 0.73/1.03  fof(f9,axiom,(
% 0.73/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.73/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.03  
% 0.73/1.03  fof(f21,plain,(
% 0.73/1.03    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.73/1.03    inference(ennf_transformation,[],[f9])).
% 0.73/1.03  
% 0.73/1.03  fof(f45,plain,(
% 0.73/1.03    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.73/1.03    inference(cnf_transformation,[],[f21])).
% 0.73/1.03  
% 0.73/1.03  fof(f8,axiom,(
% 0.73/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.73/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.03  
% 0.73/1.03  fof(f16,plain,(
% 0.73/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.73/1.03    inference(pure_predicate_removal,[],[f8])).
% 0.73/1.03  
% 0.73/1.03  fof(f19,plain,(
% 0.73/1.03    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.73/1.03    inference(ennf_transformation,[],[f16])).
% 0.73/1.03  
% 0.73/1.03  fof(f20,plain,(
% 0.73/1.03    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.73/1.03    inference(flattening,[],[f19])).
% 0.73/1.03  
% 0.73/1.03  fof(f44,plain,(
% 0.73/1.03    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.73/1.03    inference(cnf_transformation,[],[f20])).
% 0.73/1.03  
% 0.73/1.03  fof(f10,axiom,(
% 0.73/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.73/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.03  
% 0.73/1.03  fof(f22,plain,(
% 0.73/1.03    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.73/1.03    inference(ennf_transformation,[],[f10])).
% 0.73/1.03  
% 0.73/1.03  fof(f46,plain,(
% 0.73/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.73/1.03    inference(cnf_transformation,[],[f22])).
% 0.73/1.03  
% 0.73/1.03  fof(f52,plain,(
% 0.73/1.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.73/1.03    inference(cnf_transformation,[],[f35])).
% 0.73/1.03  
% 0.73/1.03  fof(f13,axiom,(
% 0.73/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.73/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.73/1.03  
% 0.73/1.03  fof(f27,plain,(
% 0.73/1.03    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.73/1.03    inference(ennf_transformation,[],[f13])).
% 0.73/1.03  
% 0.73/1.03  fof(f28,plain,(
% 0.73/1.03    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.73/1.03    inference(flattening,[],[f27])).
% 0.73/1.03  
% 0.73/1.03  fof(f49,plain,(
% 0.73/1.03    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.73/1.03    inference(cnf_transformation,[],[f28])).
% 0.73/1.03  
% 0.73/1.03  fof(f55,plain,(
% 0.73/1.03    v2_compts_1(sK1,sK0)),
% 0.73/1.03    inference(cnf_transformation,[],[f35])).
% 0.73/1.03  
% 0.73/1.03  fof(f57,plain,(
% 0.73/1.03    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.73/1.03    inference(cnf_transformation,[],[f35])).
% 0.73/1.03  
% 0.73/1.03  cnf(c_4,plain,
% 0.73/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 0.73/1.03      inference(cnf_transformation,[],[f60]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1,plain,
% 0.73/1.03      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 0.73/1.03      inference(cnf_transformation,[],[f37]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1148,plain,
% 0.73/1.03      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1671,plain,
% 0.73/1.03      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_4,c_1148]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_17,negated_conjecture,
% 0.73/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.73/1.03      inference(cnf_transformation,[],[f53]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1142,plain,
% 0.73/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_6,plain,
% 0.73/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 0.73/1.03      inference(cnf_transformation,[],[f42]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1146,plain,
% 0.73/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 0.73/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_2221,plain,
% 0.73/1.03      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_1142,c_1146]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_3,plain,
% 0.73/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.73/1.03      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 0.73/1.03      inference(cnf_transformation,[],[f59]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_5,plain,
% 0.73/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 0.73/1.03      inference(cnf_transformation,[],[f43]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_142,plain,
% 0.73/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 0.73/1.03      inference(prop_impl,[status(thm)],[c_5]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_143,plain,
% 0.73/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 0.73/1.03      inference(renaming,[status(thm)],[c_142]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_180,plain,
% 0.73/1.03      ( ~ r1_tarski(X0,X1)
% 0.73/1.03      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 0.73/1.03      inference(bin_hyper_res,[status(thm)],[c_3,c_143]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1140,plain,
% 0.73/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 0.73/1.03      | r1_tarski(X1,X2) != iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_180]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1151,plain,
% 0.73/1.03      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 0.73/1.03      | r1_tarski(X2,X0) != iProver_top ),
% 0.73/1.03      inference(light_normalisation,[status(thm)],[c_1140,c_4]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_2876,plain,
% 0.73/1.03      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_2221,c_1151]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_10,plain,
% 0.73/1.03      ( ~ v4_pre_topc(X0,X1)
% 0.73/1.03      | ~ v4_pre_topc(X2,X1)
% 0.73/1.03      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 0.73/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ v2_pre_topc(X1)
% 0.73/1.03      | ~ l1_pre_topc(X1) ),
% 0.73/1.03      inference(cnf_transformation,[],[f47]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_20,negated_conjecture,
% 0.73/1.03      ( v2_pre_topc(sK0) ),
% 0.73/1.03      inference(cnf_transformation,[],[f50]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_330,plain,
% 0.73/1.03      ( ~ v4_pre_topc(X0,X1)
% 0.73/1.03      | ~ v4_pre_topc(X2,X1)
% 0.73/1.03      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ l1_pre_topc(X1)
% 0.73/1.03      | sK0 != X1 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_331,plain,
% 0.73/1.03      ( ~ v4_pre_topc(X0,sK0)
% 0.73/1.03      | ~ v4_pre_topc(X1,sK0)
% 0.73/1.03      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | ~ l1_pre_topc(sK0) ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_330]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_19,negated_conjecture,
% 0.73/1.03      ( l1_pre_topc(sK0) ),
% 0.73/1.03      inference(cnf_transformation,[],[f51]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_335,plain,
% 0.73/1.03      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 0.73/1.03      | ~ v4_pre_topc(X1,sK0)
% 0.73/1.03      | ~ v4_pre_topc(X0,sK0) ),
% 0.73/1.03      inference(global_propositional_subsumption,
% 0.73/1.03                [status(thm)],
% 0.73/1.03                [c_331,c_19]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_336,plain,
% 0.73/1.03      ( ~ v4_pre_topc(X0,sK0)
% 0.73/1.03      | ~ v4_pre_topc(X1,sK0)
% 0.73/1.03      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.73/1.03      inference(renaming,[status(thm)],[c_335]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1137,plain,
% 0.73/1.03      ( v4_pre_topc(X0,sK0) != iProver_top
% 0.73/1.03      | v4_pre_topc(X1,sK0) != iProver_top
% 0.73/1.03      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0) = iProver_top
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.73/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_2992,plain,
% 0.73/1.03      ( v4_pre_topc(X0,sK0) != iProver_top
% 0.73/1.03      | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 0.73/1.03      | v4_pre_topc(sK2,sK0) != iProver_top
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.73/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_2876,c_1137]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_24,plain,
% 0.73/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_14,negated_conjecture,
% 0.73/1.03      ( v2_compts_1(sK2,sK0) ),
% 0.73/1.03      inference(cnf_transformation,[],[f56]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_27,plain,
% 0.73/1.03      ( v2_compts_1(sK2,sK0) = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_11,plain,
% 0.73/1.03      ( ~ v2_compts_1(X0,X1)
% 0.73/1.03      | v4_pre_topc(X0,X1)
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ v8_pre_topc(X1)
% 0.73/1.03      | ~ v2_pre_topc(X1)
% 0.73/1.03      | ~ l1_pre_topc(X1) ),
% 0.73/1.03      inference(cnf_transformation,[],[f48]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_16,negated_conjecture,
% 0.73/1.03      ( v8_pre_topc(sK0) ),
% 0.73/1.03      inference(cnf_transformation,[],[f54]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_279,plain,
% 0.73/1.03      ( ~ v2_compts_1(X0,X1)
% 0.73/1.03      | v4_pre_topc(X0,X1)
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ v2_pre_topc(X1)
% 0.73/1.03      | ~ l1_pre_topc(X1)
% 0.73/1.03      | sK0 != X1 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_280,plain,
% 0.73/1.03      ( ~ v2_compts_1(X0,sK0)
% 0.73/1.03      | v4_pre_topc(X0,sK0)
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | ~ v2_pre_topc(sK0)
% 0.73/1.03      | ~ l1_pre_topc(sK0) ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_279]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_284,plain,
% 0.73/1.03      ( ~ v2_compts_1(X0,sK0)
% 0.73/1.03      | v4_pre_topc(X0,sK0)
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.73/1.03      inference(global_propositional_subsumption,
% 0.73/1.03                [status(thm)],
% 0.73/1.03                [c_280,c_20,c_19]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1186,plain,
% 0.73/1.03      ( ~ v2_compts_1(sK2,sK0)
% 0.73/1.03      | v4_pre_topc(sK2,sK0)
% 0.73/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.73/1.03      inference(instantiation,[status(thm)],[c_284]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1187,plain,
% 0.73/1.03      ( v2_compts_1(sK2,sK0) != iProver_top
% 0.73/1.03      | v4_pre_topc(sK2,sK0) = iProver_top
% 0.73/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_1186]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_4095,plain,
% 0.73/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.73/1.03      | v4_pre_topc(X0,sK0) != iProver_top
% 0.73/1.03      | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top ),
% 0.73/1.03      inference(global_propositional_subsumption,
% 0.73/1.03                [status(thm)],
% 0.73/1.03                [c_2992,c_24,c_27,c_1187]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_4096,plain,
% 0.73/1.03      ( v4_pre_topc(X0,sK0) != iProver_top
% 0.73/1.03      | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.73/1.03      inference(renaming,[status(thm)],[c_4095]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_8,plain,
% 0.73/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ l1_pre_topc(X1)
% 0.73/1.03      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 0.73/1.03      inference(cnf_transformation,[],[f45]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_383,plain,
% 0.73/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | u1_struct_0(k1_pre_topc(X1,X0)) = X0
% 0.73/1.03      | sK0 != X1 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_384,plain,
% 0.73/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_383]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1135,plain,
% 0.73/1.03      ( u1_struct_0(k1_pre_topc(sK0,X0)) = X0
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1417,plain,
% 0.73/1.03      ( u1_struct_0(k1_pre_topc(sK0,sK2)) = sK2 ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_1142,c_1135]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_7,plain,
% 0.73/1.03      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 0.73/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.73/1.03      | ~ l1_pre_topc(X0) ),
% 0.73/1.03      inference(cnf_transformation,[],[f44]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_9,plain,
% 0.73/1.03      ( ~ m1_pre_topc(X0,X1)
% 0.73/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 0.73/1.03      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ l1_pre_topc(X1) ),
% 0.73/1.03      inference(cnf_transformation,[],[f46]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_258,plain,
% 0.73/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 0.73/1.03      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
% 0.73/1.03      | ~ l1_pre_topc(X1)
% 0.73/1.03      | ~ l1_pre_topc(X4)
% 0.73/1.03      | X4 != X1
% 0.73/1.03      | k1_pre_topc(X1,X0) != X3 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_9]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_259,plain,
% 0.73/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
% 0.73/1.03      | ~ l1_pre_topc(X1) ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_258]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_370,plain,
% 0.73/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X0))))
% 0.73/1.03      | sK0 != X1 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_259,c_19]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_371,plain,
% 0.73/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
% 0.73/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_370]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1136,plain,
% 0.73/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1)))) != iProver_top
% 0.73/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1554,plain,
% 0.73/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 0.73/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_1417,c_1136]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_2196,plain,
% 0.73/1.03      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.73/1.03      inference(global_propositional_subsumption,
% 0.73/1.03                [status(thm)],
% 0.73/1.03                [c_1554,c_24]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_2197,plain,
% 0.73/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
% 0.73/1.03      inference(renaming,[status(thm)],[c_2196]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_18,negated_conjecture,
% 0.73/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.73/1.03      inference(cnf_transformation,[],[f52]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1141,plain,
% 0.73/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_12,plain,
% 0.73/1.03      ( ~ v2_compts_1(X0,X1)
% 0.73/1.03      | v2_compts_1(X2,X1)
% 0.73/1.03      | ~ v4_pre_topc(X2,X1)
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ r1_tarski(X2,X0)
% 0.73/1.03      | ~ v2_pre_topc(X1)
% 0.73/1.03      | ~ l1_pre_topc(X1) ),
% 0.73/1.03      inference(cnf_transformation,[],[f49]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_304,plain,
% 0.73/1.03      ( ~ v2_compts_1(X0,X1)
% 0.73/1.03      | v2_compts_1(X2,X1)
% 0.73/1.03      | ~ v4_pre_topc(X2,X1)
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.73/1.03      | ~ r1_tarski(X2,X0)
% 0.73/1.03      | ~ l1_pre_topc(X1)
% 0.73/1.03      | sK0 != X1 ),
% 0.73/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_305,plain,
% 0.73/1.03      ( ~ v2_compts_1(X0,sK0)
% 0.73/1.03      | v2_compts_1(X1,sK0)
% 0.73/1.03      | ~ v4_pre_topc(X1,sK0)
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | ~ r1_tarski(X1,X0)
% 0.73/1.03      | ~ l1_pre_topc(sK0) ),
% 0.73/1.03      inference(unflattening,[status(thm)],[c_304]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_307,plain,
% 0.73/1.03      ( ~ r1_tarski(X1,X0)
% 0.73/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | ~ v4_pre_topc(X1,sK0)
% 0.73/1.03      | v2_compts_1(X1,sK0)
% 0.73/1.03      | ~ v2_compts_1(X0,sK0) ),
% 0.73/1.03      inference(global_propositional_subsumption,
% 0.73/1.03                [status(thm)],
% 0.73/1.03                [c_305,c_19]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_308,plain,
% 0.73/1.03      ( ~ v2_compts_1(X0,sK0)
% 0.73/1.03      | v2_compts_1(X1,sK0)
% 0.73/1.03      | ~ v4_pre_topc(X1,sK0)
% 0.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.73/1.03      | ~ r1_tarski(X1,X0) ),
% 0.73/1.03      inference(renaming,[status(thm)],[c_307]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1138,plain,
% 0.73/1.03      ( v2_compts_1(X0,sK0) != iProver_top
% 0.73/1.03      | v2_compts_1(X1,sK0) = iProver_top
% 0.73/1.03      | v4_pre_topc(X1,sK0) != iProver_top
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.73/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.73/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1977,plain,
% 0.73/1.03      ( v2_compts_1(X0,sK0) = iProver_top
% 0.73/1.03      | v2_compts_1(sK1,sK0) != iProver_top
% 0.73/1.03      | v4_pre_topc(X0,sK0) != iProver_top
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.73/1.03      | r1_tarski(X0,sK1) != iProver_top ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_1141,c_1138]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_15,negated_conjecture,
% 0.73/1.03      ( v2_compts_1(sK1,sK0) ),
% 0.73/1.03      inference(cnf_transformation,[],[f55]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_26,plain,
% 0.73/1.03      ( v2_compts_1(sK1,sK0) = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_2038,plain,
% 0.73/1.03      ( v2_compts_1(X0,sK0) = iProver_top
% 0.73/1.03      | v4_pre_topc(X0,sK0) != iProver_top
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.73/1.03      | r1_tarski(X0,sK1) != iProver_top ),
% 0.73/1.03      inference(global_propositional_subsumption,
% 0.73/1.03                [status(thm)],
% 0.73/1.03                [c_1977,c_26]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_2202,plain,
% 0.73/1.03      ( v2_compts_1(X0,sK0) = iProver_top
% 0.73/1.03      | v4_pre_topc(X0,sK0) != iProver_top
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 0.73/1.03      | r1_tarski(X0,sK1) != iProver_top ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_2197,c_2038]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_23,plain,
% 0.73/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1418,plain,
% 0.73/1.03      ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_1141,c_1135]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1147,plain,
% 0.73/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 0.73/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_2305,plain,
% 0.73/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.73/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 0.73/1.03      | r1_tarski(X1,u1_struct_0(k1_pre_topc(sK0,X0))) != iProver_top ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_1147,c_1136]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_3229,plain,
% 0.73/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 0.73/1.03      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.73/1.03      | r1_tarski(X0,sK1) != iProver_top ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_1418,c_2305]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_3502,plain,
% 0.73/1.03      ( v4_pre_topc(X0,sK0) != iProver_top
% 0.73/1.03      | v2_compts_1(X0,sK0) = iProver_top
% 0.73/1.03      | r1_tarski(X0,sK1) != iProver_top ),
% 0.73/1.03      inference(global_propositional_subsumption,
% 0.73/1.03                [status(thm)],
% 0.73/1.03                [c_2202,c_23,c_2038,c_3229]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_3503,plain,
% 0.73/1.03      ( v2_compts_1(X0,sK0) = iProver_top
% 0.73/1.03      | v4_pre_topc(X0,sK0) != iProver_top
% 0.73/1.03      | r1_tarski(X0,sK1) != iProver_top ),
% 0.73/1.03      inference(renaming,[status(thm)],[c_3502]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_4104,plain,
% 0.73/1.03      ( v2_compts_1(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 0.73/1.03      | v4_pre_topc(X0,sK0) != iProver_top
% 0.73/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.73/1.03      | r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),sK1) != iProver_top ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_4096,c_3503]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_11366,plain,
% 0.73/1.03      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top
% 0.73/1.03      | v4_pre_topc(sK1,sK0) != iProver_top
% 0.73/1.03      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.73/1.03      inference(superposition,[status(thm)],[c_1671,c_4104]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_13,negated_conjecture,
% 0.73/1.03      ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 0.73/1.03      inference(cnf_transformation,[],[f57]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1145,plain,
% 0.73/1.03      ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_2990,plain,
% 0.73/1.03      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
% 0.73/1.03      inference(demodulation,[status(thm)],[c_2876,c_1145]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1189,plain,
% 0.73/1.03      ( ~ v2_compts_1(sK1,sK0)
% 0.73/1.03      | v4_pre_topc(sK1,sK0)
% 0.73/1.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.73/1.03      inference(instantiation,[status(thm)],[c_284]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(c_1190,plain,
% 0.73/1.03      ( v2_compts_1(sK1,sK0) != iProver_top
% 0.73/1.03      | v4_pre_topc(sK1,sK0) = iProver_top
% 0.73/1.03      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.73/1.03      inference(predicate_to_equality,[status(thm)],[c_1189]) ).
% 0.73/1.03  
% 0.73/1.03  cnf(contradiction,plain,
% 0.73/1.03      ( $false ),
% 0.73/1.03      inference(minisat,[status(thm)],[c_11366,c_2990,c_1190,c_26,c_23]) ).
% 0.73/1.03  
% 0.73/1.03  
% 0.73/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.73/1.03  
% 0.73/1.03  ------                               Statistics
% 0.73/1.03  
% 0.73/1.03  ------ General
% 0.73/1.03  
% 0.73/1.03  abstr_ref_over_cycles:                  0
% 0.73/1.03  abstr_ref_under_cycles:                 0
% 0.73/1.03  gc_basic_clause_elim:                   0
% 0.73/1.03  forced_gc_time:                         0
% 0.73/1.03  parsing_time:                           0.009
% 0.73/1.03  unif_index_cands_time:                  0.
% 0.73/1.03  unif_index_add_time:                    0.
% 0.73/1.03  orderings_time:                         0.
% 0.73/1.03  out_proof_time:                         0.013
% 0.73/1.03  total_time:                             0.363
% 0.73/1.03  num_of_symbols:                         49
% 0.73/1.03  num_of_terms:                           11818
% 0.73/1.03  
% 0.73/1.03  ------ Preprocessing
% 0.73/1.03  
% 0.73/1.03  num_of_splits:                          0
% 0.73/1.03  num_of_split_atoms:                     0
% 0.73/1.03  num_of_reused_defs:                     0
% 0.73/1.03  num_eq_ax_congr_red:                    18
% 0.73/1.03  num_of_sem_filtered_clauses:            1
% 0.73/1.03  num_of_subtypes:                        0
% 0.73/1.03  monotx_restored_types:                  0
% 0.73/1.03  sat_num_of_epr_types:                   0
% 0.73/1.03  sat_num_of_non_cyclic_types:            0
% 0.73/1.03  sat_guarded_non_collapsed_types:        0
% 0.73/1.03  num_pure_diseq_elim:                    0
% 0.73/1.03  simp_replaced_by:                       0
% 0.73/1.03  res_preprocessed:                       97
% 0.73/1.03  prep_upred:                             0
% 0.73/1.03  prep_unflattend:                        27
% 0.73/1.03  smt_new_axioms:                         0
% 0.73/1.03  pred_elim_cands:                        4
% 0.73/1.03  pred_elim:                              4
% 0.73/1.03  pred_elim_cl:                           4
% 0.73/1.03  pred_elim_cycles:                       6
% 0.73/1.03  merged_defs:                            8
% 0.73/1.03  merged_defs_ncl:                        0
% 0.73/1.03  bin_hyper_res:                          9
% 0.73/1.03  prep_cycles:                            4
% 0.73/1.03  pred_elim_time:                         0.004
% 0.73/1.03  splitting_time:                         0.
% 0.73/1.03  sem_filter_time:                        0.
% 0.73/1.03  monotx_time:                            0.
% 0.73/1.03  subtype_inf_time:                       0.
% 0.73/1.03  
% 0.73/1.03  ------ Problem properties
% 0.73/1.03  
% 0.73/1.03  clauses:                                17
% 0.73/1.03  conjectures:                            5
% 0.73/1.03  epr:                                    2
% 0.73/1.03  horn:                                   17
% 0.73/1.03  ground:                                 5
% 0.73/1.03  unary:                                  8
% 0.73/1.03  binary:                                 5
% 0.73/1.03  lits:                                   35
% 0.73/1.03  lits_eq:                                5
% 0.73/1.03  fd_pure:                                0
% 0.73/1.03  fd_pseudo:                              0
% 0.73/1.03  fd_cond:                                0
% 0.73/1.03  fd_pseudo_cond:                         0
% 0.73/1.03  ac_symbols:                             0
% 0.73/1.03  
% 0.73/1.03  ------ Propositional Solver
% 0.73/1.03  
% 0.73/1.03  prop_solver_calls:                      31
% 0.73/1.03  prop_fast_solver_calls:                 996
% 0.73/1.03  smt_solver_calls:                       0
% 0.73/1.03  smt_fast_solver_calls:                  0
% 0.73/1.03  prop_num_of_clauses:                    5733
% 0.73/1.03  prop_preprocess_simplified:             10135
% 0.73/1.03  prop_fo_subsumed:                       24
% 0.73/1.03  prop_solver_time:                       0.
% 0.73/1.03  smt_solver_time:                        0.
% 0.73/1.03  smt_fast_solver_time:                   0.
% 0.73/1.03  prop_fast_solver_time:                  0.
% 0.73/1.03  prop_unsat_core_time:                   0.
% 0.73/1.03  
% 0.73/1.03  ------ QBF
% 0.73/1.03  
% 0.73/1.03  qbf_q_res:                              0
% 0.73/1.03  qbf_num_tautologies:                    0
% 0.73/1.03  qbf_prep_cycles:                        0
% 0.73/1.03  
% 0.73/1.03  ------ BMC1
% 0.73/1.03  
% 0.73/1.03  bmc1_current_bound:                     -1
% 0.73/1.03  bmc1_last_solved_bound:                 -1
% 0.73/1.03  bmc1_unsat_core_size:                   -1
% 0.73/1.03  bmc1_unsat_core_parents_size:           -1
% 0.73/1.03  bmc1_merge_next_fun:                    0
% 0.73/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.73/1.03  
% 0.73/1.03  ------ Instantiation
% 0.73/1.03  
% 0.73/1.03  inst_num_of_clauses:                    1528
% 0.73/1.03  inst_num_in_passive:                    52
% 0.73/1.03  inst_num_in_active:                     797
% 0.73/1.03  inst_num_in_unprocessed:                679
% 0.73/1.03  inst_num_of_loops:                      840
% 0.73/1.03  inst_num_of_learning_restarts:          0
% 0.73/1.03  inst_num_moves_active_passive:          40
% 0.73/1.03  inst_lit_activity:                      0
% 0.73/1.03  inst_lit_activity_moves:                1
% 0.73/1.03  inst_num_tautologies:                   0
% 0.73/1.03  inst_num_prop_implied:                  0
% 0.73/1.03  inst_num_existing_simplified:           0
% 0.73/1.03  inst_num_eq_res_simplified:             0
% 0.73/1.03  inst_num_child_elim:                    0
% 0.73/1.03  inst_num_of_dismatching_blockings:      392
% 0.73/1.03  inst_num_of_non_proper_insts:           1582
% 0.73/1.03  inst_num_of_duplicates:                 0
% 0.73/1.03  inst_inst_num_from_inst_to_res:         0
% 0.73/1.03  inst_dismatching_checking_time:         0.
% 0.73/1.03  
% 0.73/1.03  ------ Resolution
% 0.73/1.03  
% 0.73/1.03  res_num_of_clauses:                     0
% 0.73/1.03  res_num_in_passive:                     0
% 0.73/1.03  res_num_in_active:                      0
% 0.73/1.03  res_num_of_loops:                       101
% 0.73/1.03  res_forward_subset_subsumed:            135
% 0.73/1.03  res_backward_subset_subsumed:           0
% 0.73/1.03  res_forward_subsumed:                   0
% 0.73/1.03  res_backward_subsumed:                  0
% 0.73/1.03  res_forward_subsumption_resolution:     0
% 0.73/1.03  res_backward_subsumption_resolution:    0
% 0.73/1.03  res_clause_to_clause_subsumption:       1534
% 0.73/1.03  res_orphan_elimination:                 0
% 0.73/1.03  res_tautology_del:                      159
% 0.73/1.03  res_num_eq_res_simplified:              0
% 0.73/1.03  res_num_sel_changes:                    0
% 0.73/1.03  res_moves_from_active_to_pass:          0
% 0.73/1.03  
% 0.73/1.03  ------ Superposition
% 0.73/1.03  
% 0.73/1.03  sup_time_total:                         0.
% 0.73/1.03  sup_time_generating:                    0.
% 0.73/1.03  sup_time_sim_full:                      0.
% 0.73/1.03  sup_time_sim_immed:                     0.
% 0.73/1.03  
% 0.73/1.03  sup_num_of_clauses:                     458
% 0.73/1.03  sup_num_in_active:                      158
% 0.73/1.03  sup_num_in_passive:                     300
% 0.73/1.03  sup_num_of_loops:                       167
% 0.73/1.03  sup_fw_superposition:                   725
% 0.73/1.03  sup_bw_superposition:                   292
% 0.73/1.03  sup_immediate_simplified:               341
% 0.73/1.03  sup_given_eliminated:                   1
% 0.73/1.03  comparisons_done:                       0
% 0.73/1.03  comparisons_avoided:                    0
% 0.73/1.03  
% 0.73/1.03  ------ Simplifications
% 0.73/1.03  
% 0.73/1.03  
% 0.73/1.03  sim_fw_subset_subsumed:                 33
% 0.73/1.03  sim_bw_subset_subsumed:                 0
% 0.73/1.03  sim_fw_subsumed:                        63
% 0.73/1.03  sim_bw_subsumed:                        2
% 0.73/1.03  sim_fw_subsumption_res:                 0
% 0.73/1.03  sim_bw_subsumption_res:                 0
% 0.73/1.03  sim_tautology_del:                      16
% 0.73/1.03  sim_eq_tautology_del:                   49
% 0.73/1.03  sim_eq_res_simp:                        0
% 0.73/1.03  sim_fw_demodulated:                     129
% 0.73/1.03  sim_bw_demodulated:                     16
% 0.73/1.03  sim_light_normalised:                   154
% 0.73/1.03  sim_joinable_taut:                      0
% 0.73/1.03  sim_joinable_simp:                      0
% 0.73/1.03  sim_ac_normalised:                      0
% 0.73/1.03  sim_smt_subsumption:                    0
% 0.73/1.03  
%------------------------------------------------------------------------------
