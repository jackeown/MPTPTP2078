%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:57 EST 2020

% Result     : Theorem 7.24s
% Output     : CNFRefutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 833 expanded)
%              Number of clauses        :  103 ( 314 expanded)
%              Number of leaves         :   19 ( 210 expanded)
%              Depth                    :   19
%              Number of atoms          :  508 (3928 expanded)
%              Number of equality atoms :  148 ( 333 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
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
    inference(flattening,[],[f28])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33,f32,f31])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f56,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_966,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_971,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1478,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_966,c_971])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_151,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_152,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_151])).

cnf(c_188,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_152])).

cnf(c_963,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_3333,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1478,c_963])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_967,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1477,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_971])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_186,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_152])).

cnf(c_965,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_3163,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_965,c_971])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_152])).

cnf(c_427,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_428,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_427])).

cnf(c_458,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_190,c_428])).

cnf(c_958,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_3235,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,k3_subset_1(X0,X2))) = k7_subset_1(X0,X1,k3_subset_1(X0,X2))
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3163,c_958])).

cnf(c_10356,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) = k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK2))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1477,c_3235])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_189,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_152])).

cnf(c_962,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_2134,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1477,c_962])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_187,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_152])).

cnf(c_964,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_2536,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1477,c_964])).

cnf(c_10365,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK2)) = k1_setfam_1(k2_tarski(X0,sK2))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10356,c_2134,c_2536])).

cnf(c_18415,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1478,c_10365])).

cnf(c_18549,plain,
    ( k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3333,c_18415])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_974,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_972,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_301,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_302,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_304,plain,
    ( ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(X1,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v2_compts_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_20])).

cnf(c_305,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0) ),
    inference(renaming,[status(thm)],[c_304])).

cnf(c_960,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(X1,sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_1787,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_966,c_960])).

cnf(c_15,negated_conjecture,
    ( v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2007,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1787,c_26])).

cnf(c_2017,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_972,c_2007])).

cnf(c_4009,plain,
    ( v2_compts_1(k4_xboole_0(X0,X1),sK0) = iProver_top
    | v4_pre_topc(k4_xboole_0(X0,X1),sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_974,c_2017])).

cnf(c_18879,plain,
    ( v2_compts_1(k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK2)),sK0) = iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top
    | r1_tarski(k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK2)),sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18549,c_4009])).

cnf(c_19126,plain,
    ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18879,c_18549])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_973,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18890,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_18549,c_973])).

cnf(c_19131,plain,
    ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19126,c_18890])).

cnf(c_534,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1550,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | X0 != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_9870,plain,
    ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),X0)
    | X0 != sK0
    | k1_setfam_1(k2_tarski(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_9871,plain,
    ( X0 != sK0
    | k1_setfam_1(k2_tarski(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9870])).

cnf(c_9873,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
    | sK0 != sK0
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9871])).

cnf(c_525,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5178,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_526,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2203,plain,
    ( X0 != X1
    | X0 = k9_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_3857,plain,
    ( X0 = k9_subset_1(u1_struct_0(sK0),sK1,sK2)
    | X0 != k1_setfam_1(k2_tarski(sK1,sK2))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2203])).

cnf(c_5177,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))
    | k1_setfam_1(k2_tarski(sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k1_setfam_1(k2_tarski(sK1,sK2)) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3857])).

cnf(c_1231,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_189])).

cnf(c_3858,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_13,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_970,plain,
    ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2807,plain,
    ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2134,c_970])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_327,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_328,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ v4_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_20])).

cnf(c_333,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_332])).

cnf(c_1212,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X0,sK2),sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_1355,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1212])).

cnf(c_1356,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1355])).

cnf(c_1108,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1109,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_1105,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16,negated_conjecture,
    ( v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_276,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_277,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_281,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_277,c_20,c_19])).

cnf(c_1092,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1093,plain,
    ( v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1092])).

cnf(c_1089,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1090,plain,
    ( v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1089])).

cnf(c_546,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_14,negated_conjecture,
    ( v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,plain,
    ( v2_compts_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_23,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19131,c_9873,c_5178,c_5177,c_3858,c_2807,c_1356,c_1109,c_1105,c_1093,c_1090,c_546,c_27,c_26,c_24,c_17,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:14:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.24/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.24/1.50  
% 7.24/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.24/1.50  
% 7.24/1.50  ------  iProver source info
% 7.24/1.50  
% 7.24/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.24/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.24/1.50  git: non_committed_changes: false
% 7.24/1.50  git: last_make_outside_of_git: false
% 7.24/1.50  
% 7.24/1.50  ------ 
% 7.24/1.50  
% 7.24/1.50  ------ Input Options
% 7.24/1.50  
% 7.24/1.50  --out_options                           all
% 7.24/1.50  --tptp_safe_out                         true
% 7.24/1.50  --problem_path                          ""
% 7.24/1.50  --include_path                          ""
% 7.24/1.50  --clausifier                            res/vclausify_rel
% 7.24/1.50  --clausifier_options                    --mode clausify
% 7.24/1.50  --stdin                                 false
% 7.24/1.50  --stats_out                             all
% 7.24/1.50  
% 7.24/1.50  ------ General Options
% 7.24/1.50  
% 7.24/1.50  --fof                                   false
% 7.24/1.50  --time_out_real                         305.
% 7.24/1.50  --time_out_virtual                      -1.
% 7.24/1.50  --symbol_type_check                     false
% 7.24/1.50  --clausify_out                          false
% 7.24/1.50  --sig_cnt_out                           false
% 7.24/1.50  --trig_cnt_out                          false
% 7.24/1.50  --trig_cnt_out_tolerance                1.
% 7.24/1.50  --trig_cnt_out_sk_spl                   false
% 7.24/1.50  --abstr_cl_out                          false
% 7.24/1.50  
% 7.24/1.50  ------ Global Options
% 7.24/1.50  
% 7.24/1.50  --schedule                              default
% 7.24/1.50  --add_important_lit                     false
% 7.24/1.50  --prop_solver_per_cl                    1000
% 7.24/1.50  --min_unsat_core                        false
% 7.24/1.50  --soft_assumptions                      false
% 7.24/1.50  --soft_lemma_size                       3
% 7.24/1.50  --prop_impl_unit_size                   0
% 7.24/1.50  --prop_impl_unit                        []
% 7.24/1.50  --share_sel_clauses                     true
% 7.24/1.50  --reset_solvers                         false
% 7.24/1.50  --bc_imp_inh                            [conj_cone]
% 7.24/1.50  --conj_cone_tolerance                   3.
% 7.24/1.50  --extra_neg_conj                        none
% 7.24/1.50  --large_theory_mode                     true
% 7.24/1.50  --prolific_symb_bound                   200
% 7.24/1.50  --lt_threshold                          2000
% 7.24/1.50  --clause_weak_htbl                      true
% 7.24/1.50  --gc_record_bc_elim                     false
% 7.24/1.50  
% 7.24/1.50  ------ Preprocessing Options
% 7.24/1.50  
% 7.24/1.50  --preprocessing_flag                    true
% 7.24/1.50  --time_out_prep_mult                    0.1
% 7.24/1.50  --splitting_mode                        input
% 7.24/1.50  --splitting_grd                         true
% 7.24/1.50  --splitting_cvd                         false
% 7.24/1.50  --splitting_cvd_svl                     false
% 7.24/1.50  --splitting_nvd                         32
% 7.24/1.50  --sub_typing                            true
% 7.24/1.50  --prep_gs_sim                           true
% 7.24/1.50  --prep_unflatten                        true
% 7.24/1.50  --prep_res_sim                          true
% 7.24/1.50  --prep_upred                            true
% 7.24/1.50  --prep_sem_filter                       exhaustive
% 7.24/1.50  --prep_sem_filter_out                   false
% 7.24/1.50  --pred_elim                             true
% 7.24/1.50  --res_sim_input                         true
% 7.24/1.50  --eq_ax_congr_red                       true
% 7.24/1.50  --pure_diseq_elim                       true
% 7.24/1.50  --brand_transform                       false
% 7.24/1.50  --non_eq_to_eq                          false
% 7.24/1.50  --prep_def_merge                        true
% 7.24/1.50  --prep_def_merge_prop_impl              false
% 7.24/1.50  --prep_def_merge_mbd                    true
% 7.24/1.50  --prep_def_merge_tr_red                 false
% 7.24/1.50  --prep_def_merge_tr_cl                  false
% 7.24/1.50  --smt_preprocessing                     true
% 7.24/1.50  --smt_ac_axioms                         fast
% 7.24/1.50  --preprocessed_out                      false
% 7.24/1.50  --preprocessed_stats                    false
% 7.24/1.50  
% 7.24/1.50  ------ Abstraction refinement Options
% 7.24/1.50  
% 7.24/1.50  --abstr_ref                             []
% 7.24/1.50  --abstr_ref_prep                        false
% 7.24/1.50  --abstr_ref_until_sat                   false
% 7.24/1.50  --abstr_ref_sig_restrict                funpre
% 7.24/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.24/1.50  --abstr_ref_under                       []
% 7.24/1.50  
% 7.24/1.50  ------ SAT Options
% 7.24/1.50  
% 7.24/1.50  --sat_mode                              false
% 7.24/1.50  --sat_fm_restart_options                ""
% 7.24/1.50  --sat_gr_def                            false
% 7.24/1.50  --sat_epr_types                         true
% 7.24/1.50  --sat_non_cyclic_types                  false
% 7.24/1.50  --sat_finite_models                     false
% 7.24/1.50  --sat_fm_lemmas                         false
% 7.24/1.50  --sat_fm_prep                           false
% 7.24/1.50  --sat_fm_uc_incr                        true
% 7.24/1.50  --sat_out_model                         small
% 7.24/1.50  --sat_out_clauses                       false
% 7.24/1.50  
% 7.24/1.50  ------ QBF Options
% 7.24/1.50  
% 7.24/1.50  --qbf_mode                              false
% 7.24/1.50  --qbf_elim_univ                         false
% 7.24/1.50  --qbf_dom_inst                          none
% 7.24/1.50  --qbf_dom_pre_inst                      false
% 7.24/1.50  --qbf_sk_in                             false
% 7.24/1.50  --qbf_pred_elim                         true
% 7.24/1.50  --qbf_split                             512
% 7.24/1.50  
% 7.24/1.50  ------ BMC1 Options
% 7.24/1.50  
% 7.24/1.50  --bmc1_incremental                      false
% 7.24/1.50  --bmc1_axioms                           reachable_all
% 7.24/1.50  --bmc1_min_bound                        0
% 7.24/1.50  --bmc1_max_bound                        -1
% 7.24/1.50  --bmc1_max_bound_default                -1
% 7.24/1.50  --bmc1_symbol_reachability              true
% 7.24/1.50  --bmc1_property_lemmas                  false
% 7.24/1.50  --bmc1_k_induction                      false
% 7.24/1.50  --bmc1_non_equiv_states                 false
% 7.24/1.50  --bmc1_deadlock                         false
% 7.24/1.50  --bmc1_ucm                              false
% 7.24/1.50  --bmc1_add_unsat_core                   none
% 7.24/1.50  --bmc1_unsat_core_children              false
% 7.24/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.24/1.50  --bmc1_out_stat                         full
% 7.24/1.50  --bmc1_ground_init                      false
% 7.24/1.50  --bmc1_pre_inst_next_state              false
% 7.24/1.50  --bmc1_pre_inst_state                   false
% 7.24/1.50  --bmc1_pre_inst_reach_state             false
% 7.24/1.50  --bmc1_out_unsat_core                   false
% 7.24/1.50  --bmc1_aig_witness_out                  false
% 7.24/1.50  --bmc1_verbose                          false
% 7.24/1.50  --bmc1_dump_clauses_tptp                false
% 7.24/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.24/1.50  --bmc1_dump_file                        -
% 7.24/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.24/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.24/1.50  --bmc1_ucm_extend_mode                  1
% 7.24/1.50  --bmc1_ucm_init_mode                    2
% 7.24/1.50  --bmc1_ucm_cone_mode                    none
% 7.24/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.24/1.50  --bmc1_ucm_relax_model                  4
% 7.24/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.24/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.24/1.50  --bmc1_ucm_layered_model                none
% 7.24/1.50  --bmc1_ucm_max_lemma_size               10
% 7.24/1.50  
% 7.24/1.50  ------ AIG Options
% 7.24/1.50  
% 7.24/1.50  --aig_mode                              false
% 7.24/1.50  
% 7.24/1.50  ------ Instantiation Options
% 7.24/1.50  
% 7.24/1.50  --instantiation_flag                    true
% 7.24/1.50  --inst_sos_flag                         false
% 7.24/1.50  --inst_sos_phase                        true
% 7.24/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.24/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.24/1.50  --inst_lit_sel_side                     num_symb
% 7.24/1.50  --inst_solver_per_active                1400
% 7.24/1.50  --inst_solver_calls_frac                1.
% 7.24/1.50  --inst_passive_queue_type               priority_queues
% 7.24/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.24/1.50  --inst_passive_queues_freq              [25;2]
% 7.24/1.50  --inst_dismatching                      true
% 7.24/1.50  --inst_eager_unprocessed_to_passive     true
% 7.24/1.50  --inst_prop_sim_given                   true
% 7.24/1.50  --inst_prop_sim_new                     false
% 7.24/1.50  --inst_subs_new                         false
% 7.24/1.50  --inst_eq_res_simp                      false
% 7.24/1.50  --inst_subs_given                       false
% 7.24/1.50  --inst_orphan_elimination               true
% 7.24/1.50  --inst_learning_loop_flag               true
% 7.24/1.50  --inst_learning_start                   3000
% 7.24/1.50  --inst_learning_factor                  2
% 7.24/1.50  --inst_start_prop_sim_after_learn       3
% 7.24/1.50  --inst_sel_renew                        solver
% 7.24/1.50  --inst_lit_activity_flag                true
% 7.24/1.50  --inst_restr_to_given                   false
% 7.24/1.50  --inst_activity_threshold               500
% 7.24/1.50  --inst_out_proof                        true
% 7.24/1.50  
% 7.24/1.50  ------ Resolution Options
% 7.24/1.50  
% 7.24/1.50  --resolution_flag                       true
% 7.24/1.50  --res_lit_sel                           adaptive
% 7.24/1.50  --res_lit_sel_side                      none
% 7.24/1.50  --res_ordering                          kbo
% 7.24/1.50  --res_to_prop_solver                    active
% 7.24/1.50  --res_prop_simpl_new                    false
% 7.24/1.50  --res_prop_simpl_given                  true
% 7.24/1.50  --res_passive_queue_type                priority_queues
% 7.24/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.24/1.50  --res_passive_queues_freq               [15;5]
% 7.24/1.50  --res_forward_subs                      full
% 7.24/1.50  --res_backward_subs                     full
% 7.24/1.50  --res_forward_subs_resolution           true
% 7.24/1.50  --res_backward_subs_resolution          true
% 7.24/1.50  --res_orphan_elimination                true
% 7.24/1.50  --res_time_limit                        2.
% 7.24/1.50  --res_out_proof                         true
% 7.24/1.50  
% 7.24/1.50  ------ Superposition Options
% 7.24/1.50  
% 7.24/1.50  --superposition_flag                    true
% 7.24/1.50  --sup_passive_queue_type                priority_queues
% 7.24/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.24/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.24/1.50  --demod_completeness_check              fast
% 7.24/1.50  --demod_use_ground                      true
% 7.24/1.50  --sup_to_prop_solver                    passive
% 7.24/1.50  --sup_prop_simpl_new                    true
% 7.24/1.50  --sup_prop_simpl_given                  true
% 7.24/1.50  --sup_fun_splitting                     false
% 7.24/1.50  --sup_smt_interval                      50000
% 7.24/1.50  
% 7.24/1.50  ------ Superposition Simplification Setup
% 7.24/1.50  
% 7.24/1.50  --sup_indices_passive                   []
% 7.24/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.24/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.50  --sup_full_bw                           [BwDemod]
% 7.24/1.50  --sup_immed_triv                        [TrivRules]
% 7.24/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.24/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.50  --sup_immed_bw_main                     []
% 7.24/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.24/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.50  
% 7.24/1.50  ------ Combination Options
% 7.24/1.50  
% 7.24/1.50  --comb_res_mult                         3
% 7.24/1.50  --comb_sup_mult                         2
% 7.24/1.50  --comb_inst_mult                        10
% 7.24/1.50  
% 7.24/1.50  ------ Debug Options
% 7.24/1.50  
% 7.24/1.50  --dbg_backtrace                         false
% 7.24/1.50  --dbg_dump_prop_clauses                 false
% 7.24/1.50  --dbg_dump_prop_clauses_file            -
% 7.24/1.50  --dbg_out_stat                          false
% 7.24/1.50  ------ Parsing...
% 7.24/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.24/1.50  
% 7.24/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.24/1.50  
% 7.24/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.24/1.50  
% 7.24/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.24/1.50  ------ Proving...
% 7.24/1.50  ------ Problem Properties 
% 7.24/1.50  
% 7.24/1.50  
% 7.24/1.50  clauses                                 18
% 7.24/1.50  conjectures                             5
% 7.24/1.50  EPR                                     2
% 7.24/1.50  Horn                                    18
% 7.24/1.50  unary                                   7
% 7.24/1.50  binary                                  7
% 7.24/1.50  lits                                    38
% 7.24/1.50  lits eq                                 5
% 7.24/1.50  fd_pure                                 0
% 7.24/1.50  fd_pseudo                               0
% 7.24/1.50  fd_cond                                 0
% 7.24/1.50  fd_pseudo_cond                          0
% 7.24/1.50  AC symbols                              0
% 7.24/1.50  
% 7.24/1.50  ------ Schedule dynamic 5 is on 
% 7.24/1.50  
% 7.24/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.24/1.50  
% 7.24/1.50  
% 7.24/1.50  ------ 
% 7.24/1.50  Current options:
% 7.24/1.50  ------ 
% 7.24/1.50  
% 7.24/1.50  ------ Input Options
% 7.24/1.50  
% 7.24/1.50  --out_options                           all
% 7.24/1.50  --tptp_safe_out                         true
% 7.24/1.50  --problem_path                          ""
% 7.24/1.50  --include_path                          ""
% 7.24/1.50  --clausifier                            res/vclausify_rel
% 7.24/1.50  --clausifier_options                    --mode clausify
% 7.24/1.50  --stdin                                 false
% 7.24/1.50  --stats_out                             all
% 7.24/1.50  
% 7.24/1.50  ------ General Options
% 7.24/1.50  
% 7.24/1.50  --fof                                   false
% 7.24/1.50  --time_out_real                         305.
% 7.24/1.50  --time_out_virtual                      -1.
% 7.24/1.50  --symbol_type_check                     false
% 7.24/1.50  --clausify_out                          false
% 7.24/1.50  --sig_cnt_out                           false
% 7.24/1.50  --trig_cnt_out                          false
% 7.24/1.50  --trig_cnt_out_tolerance                1.
% 7.24/1.50  --trig_cnt_out_sk_spl                   false
% 7.24/1.50  --abstr_cl_out                          false
% 7.24/1.50  
% 7.24/1.50  ------ Global Options
% 7.24/1.50  
% 7.24/1.50  --schedule                              default
% 7.24/1.50  --add_important_lit                     false
% 7.24/1.50  --prop_solver_per_cl                    1000
% 7.24/1.50  --min_unsat_core                        false
% 7.24/1.50  --soft_assumptions                      false
% 7.24/1.50  --soft_lemma_size                       3
% 7.24/1.50  --prop_impl_unit_size                   0
% 7.24/1.50  --prop_impl_unit                        []
% 7.24/1.50  --share_sel_clauses                     true
% 7.24/1.50  --reset_solvers                         false
% 7.24/1.50  --bc_imp_inh                            [conj_cone]
% 7.24/1.50  --conj_cone_tolerance                   3.
% 7.24/1.50  --extra_neg_conj                        none
% 7.24/1.50  --large_theory_mode                     true
% 7.24/1.50  --prolific_symb_bound                   200
% 7.24/1.50  --lt_threshold                          2000
% 7.24/1.50  --clause_weak_htbl                      true
% 7.24/1.50  --gc_record_bc_elim                     false
% 7.24/1.50  
% 7.24/1.50  ------ Preprocessing Options
% 7.24/1.50  
% 7.24/1.50  --preprocessing_flag                    true
% 7.24/1.50  --time_out_prep_mult                    0.1
% 7.24/1.50  --splitting_mode                        input
% 7.24/1.50  --splitting_grd                         true
% 7.24/1.50  --splitting_cvd                         false
% 7.24/1.50  --splitting_cvd_svl                     false
% 7.24/1.50  --splitting_nvd                         32
% 7.24/1.50  --sub_typing                            true
% 7.24/1.50  --prep_gs_sim                           true
% 7.24/1.50  --prep_unflatten                        true
% 7.24/1.50  --prep_res_sim                          true
% 7.24/1.50  --prep_upred                            true
% 7.24/1.50  --prep_sem_filter                       exhaustive
% 7.24/1.50  --prep_sem_filter_out                   false
% 7.24/1.50  --pred_elim                             true
% 7.24/1.50  --res_sim_input                         true
% 7.24/1.50  --eq_ax_congr_red                       true
% 7.24/1.50  --pure_diseq_elim                       true
% 7.24/1.50  --brand_transform                       false
% 7.24/1.50  --non_eq_to_eq                          false
% 7.24/1.50  --prep_def_merge                        true
% 7.24/1.50  --prep_def_merge_prop_impl              false
% 7.24/1.50  --prep_def_merge_mbd                    true
% 7.24/1.50  --prep_def_merge_tr_red                 false
% 7.24/1.50  --prep_def_merge_tr_cl                  false
% 7.24/1.50  --smt_preprocessing                     true
% 7.24/1.50  --smt_ac_axioms                         fast
% 7.24/1.50  --preprocessed_out                      false
% 7.24/1.50  --preprocessed_stats                    false
% 7.24/1.50  
% 7.24/1.50  ------ Abstraction refinement Options
% 7.24/1.50  
% 7.24/1.50  --abstr_ref                             []
% 7.24/1.50  --abstr_ref_prep                        false
% 7.24/1.50  --abstr_ref_until_sat                   false
% 7.24/1.50  --abstr_ref_sig_restrict                funpre
% 7.24/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.24/1.50  --abstr_ref_under                       []
% 7.24/1.50  
% 7.24/1.50  ------ SAT Options
% 7.24/1.50  
% 7.24/1.50  --sat_mode                              false
% 7.24/1.50  --sat_fm_restart_options                ""
% 7.24/1.50  --sat_gr_def                            false
% 7.24/1.50  --sat_epr_types                         true
% 7.24/1.50  --sat_non_cyclic_types                  false
% 7.24/1.50  --sat_finite_models                     false
% 7.24/1.50  --sat_fm_lemmas                         false
% 7.24/1.50  --sat_fm_prep                           false
% 7.24/1.50  --sat_fm_uc_incr                        true
% 7.24/1.50  --sat_out_model                         small
% 7.24/1.50  --sat_out_clauses                       false
% 7.24/1.50  
% 7.24/1.50  ------ QBF Options
% 7.24/1.50  
% 7.24/1.50  --qbf_mode                              false
% 7.24/1.50  --qbf_elim_univ                         false
% 7.24/1.50  --qbf_dom_inst                          none
% 7.24/1.50  --qbf_dom_pre_inst                      false
% 7.24/1.50  --qbf_sk_in                             false
% 7.24/1.50  --qbf_pred_elim                         true
% 7.24/1.50  --qbf_split                             512
% 7.24/1.50  
% 7.24/1.50  ------ BMC1 Options
% 7.24/1.50  
% 7.24/1.50  --bmc1_incremental                      false
% 7.24/1.50  --bmc1_axioms                           reachable_all
% 7.24/1.50  --bmc1_min_bound                        0
% 7.24/1.50  --bmc1_max_bound                        -1
% 7.24/1.50  --bmc1_max_bound_default                -1
% 7.24/1.50  --bmc1_symbol_reachability              true
% 7.24/1.50  --bmc1_property_lemmas                  false
% 7.24/1.50  --bmc1_k_induction                      false
% 7.24/1.50  --bmc1_non_equiv_states                 false
% 7.24/1.50  --bmc1_deadlock                         false
% 7.24/1.50  --bmc1_ucm                              false
% 7.24/1.50  --bmc1_add_unsat_core                   none
% 7.24/1.50  --bmc1_unsat_core_children              false
% 7.24/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.24/1.50  --bmc1_out_stat                         full
% 7.24/1.50  --bmc1_ground_init                      false
% 7.24/1.50  --bmc1_pre_inst_next_state              false
% 7.24/1.50  --bmc1_pre_inst_state                   false
% 7.24/1.50  --bmc1_pre_inst_reach_state             false
% 7.24/1.50  --bmc1_out_unsat_core                   false
% 7.24/1.50  --bmc1_aig_witness_out                  false
% 7.24/1.50  --bmc1_verbose                          false
% 7.24/1.50  --bmc1_dump_clauses_tptp                false
% 7.24/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.24/1.50  --bmc1_dump_file                        -
% 7.24/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.24/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.24/1.50  --bmc1_ucm_extend_mode                  1
% 7.24/1.50  --bmc1_ucm_init_mode                    2
% 7.24/1.50  --bmc1_ucm_cone_mode                    none
% 7.24/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.24/1.50  --bmc1_ucm_relax_model                  4
% 7.24/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.24/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.24/1.50  --bmc1_ucm_layered_model                none
% 7.24/1.50  --bmc1_ucm_max_lemma_size               10
% 7.24/1.50  
% 7.24/1.50  ------ AIG Options
% 7.24/1.50  
% 7.24/1.50  --aig_mode                              false
% 7.24/1.50  
% 7.24/1.50  ------ Instantiation Options
% 7.24/1.50  
% 7.24/1.50  --instantiation_flag                    true
% 7.24/1.50  --inst_sos_flag                         false
% 7.24/1.50  --inst_sos_phase                        true
% 7.24/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.24/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.24/1.50  --inst_lit_sel_side                     none
% 7.24/1.50  --inst_solver_per_active                1400
% 7.24/1.50  --inst_solver_calls_frac                1.
% 7.24/1.50  --inst_passive_queue_type               priority_queues
% 7.24/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.24/1.50  --inst_passive_queues_freq              [25;2]
% 7.24/1.50  --inst_dismatching                      true
% 7.24/1.50  --inst_eager_unprocessed_to_passive     true
% 7.24/1.50  --inst_prop_sim_given                   true
% 7.24/1.50  --inst_prop_sim_new                     false
% 7.24/1.50  --inst_subs_new                         false
% 7.24/1.50  --inst_eq_res_simp                      false
% 7.24/1.50  --inst_subs_given                       false
% 7.24/1.50  --inst_orphan_elimination               true
% 7.24/1.50  --inst_learning_loop_flag               true
% 7.24/1.50  --inst_learning_start                   3000
% 7.24/1.50  --inst_learning_factor                  2
% 7.24/1.50  --inst_start_prop_sim_after_learn       3
% 7.24/1.50  --inst_sel_renew                        solver
% 7.24/1.50  --inst_lit_activity_flag                true
% 7.24/1.50  --inst_restr_to_given                   false
% 7.24/1.50  --inst_activity_threshold               500
% 7.24/1.50  --inst_out_proof                        true
% 7.24/1.50  
% 7.24/1.50  ------ Resolution Options
% 7.24/1.50  
% 7.24/1.50  --resolution_flag                       false
% 7.24/1.50  --res_lit_sel                           adaptive
% 7.24/1.50  --res_lit_sel_side                      none
% 7.24/1.50  --res_ordering                          kbo
% 7.24/1.50  --res_to_prop_solver                    active
% 7.24/1.50  --res_prop_simpl_new                    false
% 7.24/1.50  --res_prop_simpl_given                  true
% 7.24/1.50  --res_passive_queue_type                priority_queues
% 7.24/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.24/1.50  --res_passive_queues_freq               [15;5]
% 7.24/1.50  --res_forward_subs                      full
% 7.24/1.50  --res_backward_subs                     full
% 7.24/1.50  --res_forward_subs_resolution           true
% 7.24/1.50  --res_backward_subs_resolution          true
% 7.24/1.50  --res_orphan_elimination                true
% 7.24/1.50  --res_time_limit                        2.
% 7.24/1.50  --res_out_proof                         true
% 7.24/1.50  
% 7.24/1.50  ------ Superposition Options
% 7.24/1.50  
% 7.24/1.50  --superposition_flag                    true
% 7.24/1.50  --sup_passive_queue_type                priority_queues
% 7.24/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.24/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.24/1.50  --demod_completeness_check              fast
% 7.24/1.50  --demod_use_ground                      true
% 7.24/1.50  --sup_to_prop_solver                    passive
% 7.24/1.50  --sup_prop_simpl_new                    true
% 7.24/1.50  --sup_prop_simpl_given                  true
% 7.24/1.50  --sup_fun_splitting                     false
% 7.24/1.50  --sup_smt_interval                      50000
% 7.24/1.50  
% 7.24/1.50  ------ Superposition Simplification Setup
% 7.24/1.50  
% 7.24/1.50  --sup_indices_passive                   []
% 7.24/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.24/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.24/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.50  --sup_full_bw                           [BwDemod]
% 7.24/1.50  --sup_immed_triv                        [TrivRules]
% 7.24/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.24/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.50  --sup_immed_bw_main                     []
% 7.24/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.24/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.24/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.24/1.50  
% 7.24/1.50  ------ Combination Options
% 7.24/1.50  
% 7.24/1.50  --comb_res_mult                         3
% 7.24/1.50  --comb_sup_mult                         2
% 7.24/1.50  --comb_inst_mult                        10
% 7.24/1.50  
% 7.24/1.50  ------ Debug Options
% 7.24/1.50  
% 7.24/1.50  --dbg_backtrace                         false
% 7.24/1.50  --dbg_dump_prop_clauses                 false
% 7.24/1.50  --dbg_dump_prop_clauses_file            -
% 7.24/1.50  --dbg_out_stat                          false
% 7.24/1.50  
% 7.24/1.50  
% 7.24/1.50  
% 7.24/1.50  
% 7.24/1.50  ------ Proving...
% 7.24/1.50  
% 7.24/1.50  
% 7.24/1.50  % SZS status Theorem for theBenchmark.p
% 7.24/1.50  
% 7.24/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.24/1.50  
% 7.24/1.50  fof(f14,conjecture,(
% 7.24/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f15,negated_conjecture,(
% 7.24/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.24/1.50    inference(negated_conjecture,[],[f14])).
% 7.24/1.50  
% 7.24/1.50  fof(f28,plain,(
% 7.24/1.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.24/1.50    inference(ennf_transformation,[],[f15])).
% 7.24/1.50  
% 7.24/1.50  fof(f29,plain,(
% 7.24/1.50    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.24/1.50    inference(flattening,[],[f28])).
% 7.24/1.50  
% 7.24/1.50  fof(f33,plain,(
% 7.24/1.50    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v2_compts_1(sK2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.24/1.50    introduced(choice_axiom,[])).
% 7.24/1.50  
% 7.24/1.50  fof(f32,plain,(
% 7.24/1.50    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(sK1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.24/1.50    introduced(choice_axiom,[])).
% 7.24/1.50  
% 7.24/1.50  fof(f31,plain,(
% 7.24/1.50    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.24/1.50    introduced(choice_axiom,[])).
% 7.24/1.50  
% 7.24/1.50  fof(f34,plain,(
% 7.24/1.50    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.24/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33,f32,f31])).
% 7.24/1.50  
% 7.24/1.50  fof(f51,plain,(
% 7.24/1.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.24/1.50    inference(cnf_transformation,[],[f34])).
% 7.24/1.50  
% 7.24/1.50  fof(f10,axiom,(
% 7.24/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f30,plain,(
% 7.24/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.24/1.50    inference(nnf_transformation,[],[f10])).
% 7.24/1.50  
% 7.24/1.50  fof(f44,plain,(
% 7.24/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.24/1.50    inference(cnf_transformation,[],[f30])).
% 7.24/1.50  
% 7.24/1.50  fof(f6,axiom,(
% 7.24/1.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f19,plain,(
% 7.24/1.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.24/1.50    inference(ennf_transformation,[],[f6])).
% 7.24/1.50  
% 7.24/1.50  fof(f40,plain,(
% 7.24/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.24/1.50    inference(cnf_transformation,[],[f19])).
% 7.24/1.50  
% 7.24/1.50  fof(f45,plain,(
% 7.24/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.24/1.50    inference(cnf_transformation,[],[f30])).
% 7.24/1.50  
% 7.24/1.50  fof(f52,plain,(
% 7.24/1.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.24/1.50    inference(cnf_transformation,[],[f34])).
% 7.24/1.50  
% 7.24/1.50  fof(f4,axiom,(
% 7.24/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f17,plain,(
% 7.24/1.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.24/1.50    inference(ennf_transformation,[],[f4])).
% 7.24/1.50  
% 7.24/1.50  fof(f38,plain,(
% 7.24/1.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.24/1.50    inference(cnf_transformation,[],[f17])).
% 7.24/1.50  
% 7.24/1.50  fof(f8,axiom,(
% 7.24/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f21,plain,(
% 7.24/1.50    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.24/1.50    inference(ennf_transformation,[],[f8])).
% 7.24/1.50  
% 7.24/1.50  fof(f42,plain,(
% 7.24/1.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.24/1.50    inference(cnf_transformation,[],[f21])).
% 7.24/1.50  
% 7.24/1.50  fof(f7,axiom,(
% 7.24/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f20,plain,(
% 7.24/1.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.24/1.50    inference(ennf_transformation,[],[f7])).
% 7.24/1.50  
% 7.24/1.50  fof(f41,plain,(
% 7.24/1.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.24/1.50    inference(cnf_transformation,[],[f20])).
% 7.24/1.50  
% 7.24/1.50  fof(f9,axiom,(
% 7.24/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f43,plain,(
% 7.24/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.24/1.50    inference(cnf_transformation,[],[f9])).
% 7.24/1.50  
% 7.24/1.50  fof(f57,plain,(
% 7.24/1.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.24/1.50    inference(definition_unfolding,[],[f41,f43])).
% 7.24/1.50  
% 7.24/1.50  fof(f5,axiom,(
% 7.24/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f18,plain,(
% 7.24/1.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.24/1.50    inference(ennf_transformation,[],[f5])).
% 7.24/1.50  
% 7.24/1.50  fof(f39,plain,(
% 7.24/1.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.24/1.50    inference(cnf_transformation,[],[f18])).
% 7.24/1.50  
% 7.24/1.50  fof(f1,axiom,(
% 7.24/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f16,plain,(
% 7.24/1.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 7.24/1.50    inference(ennf_transformation,[],[f1])).
% 7.24/1.50  
% 7.24/1.50  fof(f35,plain,(
% 7.24/1.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 7.24/1.50    inference(cnf_transformation,[],[f16])).
% 7.24/1.50  
% 7.24/1.50  fof(f13,axiom,(
% 7.24/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f26,plain,(
% 7.24/1.50    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.24/1.50    inference(ennf_transformation,[],[f13])).
% 7.24/1.50  
% 7.24/1.50  fof(f27,plain,(
% 7.24/1.50    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.24/1.50    inference(flattening,[],[f26])).
% 7.24/1.50  
% 7.24/1.50  fof(f48,plain,(
% 7.24/1.50    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.24/1.50    inference(cnf_transformation,[],[f27])).
% 7.24/1.50  
% 7.24/1.50  fof(f50,plain,(
% 7.24/1.50    l1_pre_topc(sK0)),
% 7.24/1.50    inference(cnf_transformation,[],[f34])).
% 7.24/1.50  
% 7.24/1.50  fof(f49,plain,(
% 7.24/1.50    v2_pre_topc(sK0)),
% 7.24/1.50    inference(cnf_transformation,[],[f34])).
% 7.24/1.50  
% 7.24/1.50  fof(f54,plain,(
% 7.24/1.50    v2_compts_1(sK1,sK0)),
% 7.24/1.50    inference(cnf_transformation,[],[f34])).
% 7.24/1.50  
% 7.24/1.50  fof(f2,axiom,(
% 7.24/1.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f36,plain,(
% 7.24/1.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.24/1.50    inference(cnf_transformation,[],[f2])).
% 7.24/1.50  
% 7.24/1.50  fof(f56,plain,(
% 7.24/1.50    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 7.24/1.50    inference(cnf_transformation,[],[f34])).
% 7.24/1.50  
% 7.24/1.50  fof(f11,axiom,(
% 7.24/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f22,plain,(
% 7.24/1.50    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.24/1.50    inference(ennf_transformation,[],[f11])).
% 7.24/1.50  
% 7.24/1.50  fof(f23,plain,(
% 7.24/1.50    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.24/1.50    inference(flattening,[],[f22])).
% 7.24/1.50  
% 7.24/1.50  fof(f46,plain,(
% 7.24/1.50    ( ! [X2,X0,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.24/1.50    inference(cnf_transformation,[],[f23])).
% 7.24/1.50  
% 7.24/1.50  fof(f12,axiom,(
% 7.24/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 7.24/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.24/1.50  
% 7.24/1.50  fof(f24,plain,(
% 7.24/1.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.24/1.50    inference(ennf_transformation,[],[f12])).
% 7.24/1.50  
% 7.24/1.50  fof(f25,plain,(
% 7.24/1.50    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.24/1.50    inference(flattening,[],[f24])).
% 7.24/1.50  
% 7.24/1.50  fof(f47,plain,(
% 7.24/1.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.24/1.50    inference(cnf_transformation,[],[f25])).
% 7.24/1.50  
% 7.24/1.50  fof(f53,plain,(
% 7.24/1.50    v8_pre_topc(sK0)),
% 7.24/1.50    inference(cnf_transformation,[],[f34])).
% 7.24/1.50  
% 7.24/1.50  fof(f55,plain,(
% 7.24/1.50    v2_compts_1(sK2,sK0)),
% 7.24/1.50    inference(cnf_transformation,[],[f34])).
% 7.24/1.50  
% 7.24/1.50  cnf(c_18,negated_conjecture,
% 7.24/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.24/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_966,plain,
% 7.24/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_9,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_971,plain,
% 7.24/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.24/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1478,plain,
% 7.24/1.50      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_966,c_971]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_5,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.24/1.50      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.24/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_8,plain,
% 7.24/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_151,plain,
% 7.24/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.24/1.50      inference(prop_impl,[status(thm)],[c_8]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_152,plain,
% 7.24/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.24/1.50      inference(renaming,[status(thm)],[c_151]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_188,plain,
% 7.24/1.50      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.24/1.50      inference(bin_hyper_res,[status(thm)],[c_5,c_152]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_963,plain,
% 7.24/1.50      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 7.24/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_188]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3333,plain,
% 7.24/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_1478,c_963]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_17,negated_conjecture,
% 7.24/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.24/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_967,plain,
% 7.24/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1477,plain,
% 7.24/1.50      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_967,c_971]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.24/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.24/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_186,plain,
% 7.24/1.50      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 7.24/1.50      | ~ r1_tarski(X1,X0) ),
% 7.24/1.50      inference(bin_hyper_res,[status(thm)],[c_3,c_152]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_965,plain,
% 7.24/1.50      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 7.24/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3163,plain,
% 7.24/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.24/1.50      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_965,c_971]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_7,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.24/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.24/1.50      | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
% 7.24/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_190,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.24/1.50      | ~ r1_tarski(X2,X1)
% 7.24/1.50      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 7.24/1.50      inference(bin_hyper_res,[status(thm)],[c_7,c_152]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_427,plain,
% 7.24/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.24/1.50      inference(prop_impl,[status(thm)],[c_8]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_428,plain,
% 7.24/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.24/1.50      inference(renaming,[status(thm)],[c_427]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_458,plain,
% 7.24/1.50      ( ~ r1_tarski(X0,X1)
% 7.24/1.50      | ~ r1_tarski(X2,X1)
% 7.24/1.50      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 7.24/1.50      inference(bin_hyper_res,[status(thm)],[c_190,c_428]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_958,plain,
% 7.24/1.50      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 7.24/1.50      | r1_tarski(X2,X0) != iProver_top
% 7.24/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3235,plain,
% 7.24/1.50      ( k9_subset_1(X0,X1,k3_subset_1(X0,k3_subset_1(X0,X2))) = k7_subset_1(X0,X1,k3_subset_1(X0,X2))
% 7.24/1.50      | r1_tarski(X2,X0) != iProver_top
% 7.24/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_3163,c_958]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_10356,plain,
% 7.24/1.50      ( k9_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) = k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK2))
% 7.24/1.50      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_1477,c_3235]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_6,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.24/1.50      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.24/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_189,plain,
% 7.24/1.50      ( ~ r1_tarski(X0,X1)
% 7.24/1.50      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.24/1.50      inference(bin_hyper_res,[status(thm)],[c_6,c_152]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_962,plain,
% 7.24/1.50      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 7.24/1.50      | r1_tarski(X2,X0) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2134,plain,
% 7.24/1.50      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_1477,c_962]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4,plain,
% 7.24/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.24/1.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.24/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_187,plain,
% 7.24/1.50      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.24/1.50      inference(bin_hyper_res,[status(thm)],[c_4,c_152]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_964,plain,
% 7.24/1.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 7.24/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2536,plain,
% 7.24/1.50      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_1477,c_964]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_10365,plain,
% 7.24/1.50      ( k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK2)) = k1_setfam_1(k2_tarski(X0,sK2))
% 7.24/1.50      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 7.24/1.50      inference(light_normalisation,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_10356,c_2134,c_2536]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_18415,plain,
% 7.24/1.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_1478,c_10365]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_18549,plain,
% 7.24/1.50      ( k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_3333,c_18415]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_0,plain,
% 7.24/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_974,plain,
% 7.24/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.24/1.50      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_972,plain,
% 7.24/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.24/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_12,plain,
% 7.24/1.50      ( ~ v2_compts_1(X0,X1)
% 7.24/1.50      | v2_compts_1(X2,X1)
% 7.24/1.50      | ~ v4_pre_topc(X2,X1)
% 7.24/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.24/1.50      | ~ r1_tarski(X2,X0)
% 7.24/1.50      | ~ v2_pre_topc(X1)
% 7.24/1.50      | ~ l1_pre_topc(X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_19,negated_conjecture,
% 7.24/1.50      ( l1_pre_topc(sK0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_301,plain,
% 7.24/1.50      ( ~ v2_compts_1(X0,X1)
% 7.24/1.50      | v2_compts_1(X2,X1)
% 7.24/1.50      | ~ v4_pre_topc(X2,X1)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.24/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.24/1.50      | ~ r1_tarski(X2,X0)
% 7.24/1.50      | ~ v2_pre_topc(X1)
% 7.24/1.50      | sK0 != X1 ),
% 7.24/1.50      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_302,plain,
% 7.24/1.50      ( ~ v2_compts_1(X0,sK0)
% 7.24/1.50      | v2_compts_1(X1,sK0)
% 7.24/1.50      | ~ v4_pre_topc(X1,sK0)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ r1_tarski(X1,X0)
% 7.24/1.50      | ~ v2_pre_topc(sK0) ),
% 7.24/1.50      inference(unflattening,[status(thm)],[c_301]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_20,negated_conjecture,
% 7.24/1.50      ( v2_pre_topc(sK0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_304,plain,
% 7.24/1.50      ( ~ r1_tarski(X1,X0)
% 7.24/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ v4_pre_topc(X1,sK0)
% 7.24/1.50      | v2_compts_1(X1,sK0)
% 7.24/1.50      | ~ v2_compts_1(X0,sK0) ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_302,c_20]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_305,plain,
% 7.24/1.50      ( ~ v2_compts_1(X0,sK0)
% 7.24/1.50      | v2_compts_1(X1,sK0)
% 7.24/1.50      | ~ v4_pre_topc(X1,sK0)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ r1_tarski(X1,X0) ),
% 7.24/1.50      inference(renaming,[status(thm)],[c_304]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_960,plain,
% 7.24/1.50      ( v2_compts_1(X0,sK0) != iProver_top
% 7.24/1.50      | v2_compts_1(X1,sK0) = iProver_top
% 7.24/1.50      | v4_pre_topc(X1,sK0) != iProver_top
% 7.24/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.24/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.24/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1787,plain,
% 7.24/1.50      ( v2_compts_1(X0,sK0) = iProver_top
% 7.24/1.50      | v2_compts_1(sK1,sK0) != iProver_top
% 7.24/1.50      | v4_pre_topc(X0,sK0) != iProver_top
% 7.24/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.24/1.50      | r1_tarski(X0,sK1) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_966,c_960]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_15,negated_conjecture,
% 7.24/1.50      ( v2_compts_1(sK1,sK0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_26,plain,
% 7.24/1.50      ( v2_compts_1(sK1,sK0) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2007,plain,
% 7.24/1.50      ( v2_compts_1(X0,sK0) = iProver_top
% 7.24/1.50      | v4_pre_topc(X0,sK0) != iProver_top
% 7.24/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.24/1.50      | r1_tarski(X0,sK1) != iProver_top ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_1787,c_26]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2017,plain,
% 7.24/1.50      ( v2_compts_1(X0,sK0) = iProver_top
% 7.24/1.50      | v4_pre_topc(X0,sK0) != iProver_top
% 7.24/1.50      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 7.24/1.50      | r1_tarski(X0,sK1) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_972,c_2007]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_4009,plain,
% 7.24/1.50      ( v2_compts_1(k4_xboole_0(X0,X1),sK0) = iProver_top
% 7.24/1.50      | v4_pre_topc(k4_xboole_0(X0,X1),sK0) != iProver_top
% 7.24/1.50      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 7.24/1.50      | r1_tarski(k4_xboole_0(X0,X1),sK1) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_974,c_2017]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_18879,plain,
% 7.24/1.50      ( v2_compts_1(k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK2)),sK0) = iProver_top
% 7.24/1.50      | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top
% 7.24/1.50      | r1_tarski(k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK2)),sK1) != iProver_top
% 7.24/1.50      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_18549,c_4009]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_19126,plain,
% 7.24/1.50      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top
% 7.24/1.50      | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top
% 7.24/1.50      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) != iProver_top
% 7.24/1.50      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 7.24/1.50      inference(light_normalisation,[status(thm)],[c_18879,c_18549]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1,plain,
% 7.24/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_973,plain,
% 7.24/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_18890,plain,
% 7.24/1.50      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) = iProver_top ),
% 7.24/1.50      inference(superposition,[status(thm)],[c_18549,c_973]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_19131,plain,
% 7.24/1.50      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top
% 7.24/1.50      | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top
% 7.24/1.50      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 7.24/1.50      inference(forward_subsumption_resolution,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_19126,c_18890]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_534,plain,
% 7.24/1.50      ( ~ v4_pre_topc(X0,X1) | v4_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.24/1.50      theory(equality) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1550,plain,
% 7.24/1.50      ( v4_pre_topc(X0,X1)
% 7.24/1.50      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 7.24/1.50      | X0 != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
% 7.24/1.50      | X1 != sK0 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_534]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_9870,plain,
% 7.24/1.50      ( ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 7.24/1.50      | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),X0)
% 7.24/1.50      | X0 != sK0
% 7.24/1.50      | k1_setfam_1(k2_tarski(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_1550]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_9871,plain,
% 7.24/1.50      ( X0 != sK0
% 7.24/1.50      | k1_setfam_1(k2_tarski(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
% 7.24/1.50      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top
% 7.24/1.50      | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),X0) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_9870]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_9873,plain,
% 7.24/1.50      ( k1_setfam_1(k2_tarski(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
% 7.24/1.50      | sK0 != sK0
% 7.24/1.50      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top
% 7.24/1.50      | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_9871]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_525,plain,( X0 = X0 ),theory(equality) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_5178,plain,
% 7.24/1.50      ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_525]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_526,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2203,plain,
% 7.24/1.50      ( X0 != X1
% 7.24/1.50      | X0 = k9_subset_1(u1_struct_0(sK0),sK1,sK2)
% 7.24/1.50      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X1 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_526]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3857,plain,
% 7.24/1.50      ( X0 = k9_subset_1(u1_struct_0(sK0),sK1,sK2)
% 7.24/1.50      | X0 != k1_setfam_1(k2_tarski(sK1,sK2))
% 7.24/1.50      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_2203]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_5177,plain,
% 7.24/1.50      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))
% 7.24/1.50      | k1_setfam_1(k2_tarski(sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,sK2)
% 7.24/1.50      | k1_setfam_1(k2_tarski(sK1,sK2)) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_3857]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1231,plain,
% 7.24/1.50      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 7.24/1.50      | k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_189]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_3858,plain,
% 7.24/1.50      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 7.24/1.50      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_1231]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_13,negated_conjecture,
% 7.24/1.50      ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_970,plain,
% 7.24/1.50      ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_2807,plain,
% 7.24/1.50      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
% 7.24/1.50      inference(demodulation,[status(thm)],[c_2134,c_970]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_10,plain,
% 7.24/1.50      ( ~ v4_pre_topc(X0,X1)
% 7.24/1.50      | ~ v4_pre_topc(X2,X1)
% 7.24/1.50      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.24/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.24/1.50      | ~ v2_pre_topc(X1)
% 7.24/1.50      | ~ l1_pre_topc(X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_327,plain,
% 7.24/1.50      ( ~ v4_pre_topc(X0,X1)
% 7.24/1.50      | ~ v4_pre_topc(X2,X1)
% 7.24/1.50      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.24/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.24/1.50      | ~ v2_pre_topc(X1)
% 7.24/1.50      | sK0 != X1 ),
% 7.24/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_328,plain,
% 7.24/1.50      ( ~ v4_pre_topc(X0,sK0)
% 7.24/1.50      | ~ v4_pre_topc(X1,sK0)
% 7.24/1.50      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ v2_pre_topc(sK0) ),
% 7.24/1.50      inference(unflattening,[status(thm)],[c_327]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_332,plain,
% 7.24/1.50      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 7.24/1.50      | ~ v4_pre_topc(X1,sK0)
% 7.24/1.50      | ~ v4_pre_topc(X0,sK0) ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_328,c_20]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_333,plain,
% 7.24/1.50      ( ~ v4_pre_topc(X0,sK0)
% 7.24/1.50      | ~ v4_pre_topc(X1,sK0)
% 7.24/1.50      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.24/1.50      inference(renaming,[status(thm)],[c_332]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1212,plain,
% 7.24/1.50      ( ~ v4_pre_topc(X0,sK0)
% 7.24/1.50      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X0,sK2),sK0)
% 7.24/1.50      | ~ v4_pre_topc(sK2,sK0)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_333]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1355,plain,
% 7.24/1.50      ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 7.24/1.50      | ~ v4_pre_topc(sK2,sK0)
% 7.24/1.50      | ~ v4_pre_topc(sK1,sK0)
% 7.24/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_1212]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1356,plain,
% 7.24/1.50      ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
% 7.24/1.50      | v4_pre_topc(sK2,sK0) != iProver_top
% 7.24/1.50      | v4_pre_topc(sK1,sK0) != iProver_top
% 7.24/1.50      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.24/1.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_1355]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1108,plain,
% 7.24/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1109,plain,
% 7.24/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.24/1.50      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_1108]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1105,plain,
% 7.24/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_11,plain,
% 7.24/1.50      ( ~ v2_compts_1(X0,X1)
% 7.24/1.50      | v4_pre_topc(X0,X1)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.24/1.50      | ~ v8_pre_topc(X1)
% 7.24/1.50      | ~ v2_pre_topc(X1)
% 7.24/1.50      | ~ l1_pre_topc(X1) ),
% 7.24/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_16,negated_conjecture,
% 7.24/1.50      ( v8_pre_topc(sK0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_276,plain,
% 7.24/1.50      ( ~ v2_compts_1(X0,X1)
% 7.24/1.50      | v4_pre_topc(X0,X1)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.24/1.50      | ~ v2_pre_topc(X1)
% 7.24/1.50      | ~ l1_pre_topc(X1)
% 7.24/1.50      | sK0 != X1 ),
% 7.24/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_277,plain,
% 7.24/1.50      ( ~ v2_compts_1(X0,sK0)
% 7.24/1.50      | v4_pre_topc(X0,sK0)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.24/1.50      | ~ v2_pre_topc(sK0)
% 7.24/1.50      | ~ l1_pre_topc(sK0) ),
% 7.24/1.50      inference(unflattening,[status(thm)],[c_276]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_281,plain,
% 7.24/1.50      ( ~ v2_compts_1(X0,sK0)
% 7.24/1.50      | v4_pre_topc(X0,sK0)
% 7.24/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.24/1.50      inference(global_propositional_subsumption,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_277,c_20,c_19]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1092,plain,
% 7.24/1.50      ( ~ v2_compts_1(sK1,sK0)
% 7.24/1.50      | v4_pre_topc(sK1,sK0)
% 7.24/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_281]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1093,plain,
% 7.24/1.50      ( v2_compts_1(sK1,sK0) != iProver_top
% 7.24/1.50      | v4_pre_topc(sK1,sK0) = iProver_top
% 7.24/1.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_1092]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1089,plain,
% 7.24/1.50      ( ~ v2_compts_1(sK2,sK0)
% 7.24/1.50      | v4_pre_topc(sK2,sK0)
% 7.24/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_281]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_1090,plain,
% 7.24/1.50      ( v2_compts_1(sK2,sK0) != iProver_top
% 7.24/1.50      | v4_pre_topc(sK2,sK0) = iProver_top
% 7.24/1.50      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_1089]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_546,plain,
% 7.24/1.50      ( sK0 = sK0 ),
% 7.24/1.50      inference(instantiation,[status(thm)],[c_525]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_14,negated_conjecture,
% 7.24/1.50      ( v2_compts_1(sK2,sK0) ),
% 7.24/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_27,plain,
% 7.24/1.50      ( v2_compts_1(sK2,sK0) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_24,plain,
% 7.24/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(c_23,plain,
% 7.24/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.24/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.24/1.50  
% 7.24/1.50  cnf(contradiction,plain,
% 7.24/1.50      ( $false ),
% 7.24/1.50      inference(minisat,
% 7.24/1.50                [status(thm)],
% 7.24/1.50                [c_19131,c_9873,c_5178,c_5177,c_3858,c_2807,c_1356,
% 7.24/1.50                 c_1109,c_1105,c_1093,c_1090,c_546,c_27,c_26,c_24,c_17,
% 7.24/1.50                 c_23]) ).
% 7.24/1.50  
% 7.24/1.50  
% 7.24/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.24/1.50  
% 7.24/1.50  ------                               Statistics
% 7.24/1.50  
% 7.24/1.50  ------ General
% 7.24/1.50  
% 7.24/1.50  abstr_ref_over_cycles:                  0
% 7.24/1.50  abstr_ref_under_cycles:                 0
% 7.24/1.50  gc_basic_clause_elim:                   0
% 7.24/1.50  forced_gc_time:                         0
% 7.24/1.50  parsing_time:                           0.01
% 7.24/1.50  unif_index_cands_time:                  0.
% 7.24/1.50  unif_index_add_time:                    0.
% 7.24/1.50  orderings_time:                         0.
% 7.24/1.50  out_proof_time:                         0.01
% 7.24/1.50  total_time:                             0.61
% 7.24/1.50  num_of_symbols:                         49
% 7.24/1.50  num_of_terms:                           25855
% 7.24/1.50  
% 7.24/1.50  ------ Preprocessing
% 7.24/1.50  
% 7.24/1.50  num_of_splits:                          0
% 7.24/1.50  num_of_split_atoms:                     0
% 7.24/1.50  num_of_reused_defs:                     0
% 7.24/1.50  num_eq_ax_congr_red:                    28
% 7.24/1.50  num_of_sem_filtered_clauses:            1
% 7.24/1.50  num_of_subtypes:                        0
% 7.24/1.50  monotx_restored_types:                  0
% 7.24/1.50  sat_num_of_epr_types:                   0
% 7.24/1.50  sat_num_of_non_cyclic_types:            0
% 7.24/1.50  sat_guarded_non_collapsed_types:        0
% 7.24/1.50  num_pure_diseq_elim:                    0
% 7.24/1.50  simp_replaced_by:                       0
% 7.24/1.50  res_preprocessed:                       98
% 7.24/1.50  prep_upred:                             0
% 7.24/1.50  prep_unflattend:                        3
% 7.24/1.50  smt_new_axioms:                         0
% 7.24/1.50  pred_elim_cands:                        4
% 7.24/1.50  pred_elim:                              3
% 7.24/1.50  pred_elim_cl:                           3
% 7.24/1.50  pred_elim_cycles:                       5
% 7.24/1.50  merged_defs:                            8
% 7.24/1.50  merged_defs_ncl:                        0
% 7.24/1.50  bin_hyper_res:                          14
% 7.24/1.50  prep_cycles:                            4
% 7.24/1.50  pred_elim_time:                         0.002
% 7.24/1.50  splitting_time:                         0.
% 7.24/1.50  sem_filter_time:                        0.
% 7.24/1.50  monotx_time:                            0.001
% 7.24/1.50  subtype_inf_time:                       0.
% 7.24/1.50  
% 7.24/1.50  ------ Problem properties
% 7.24/1.50  
% 7.24/1.50  clauses:                                18
% 7.24/1.50  conjectures:                            5
% 7.24/1.50  epr:                                    2
% 7.24/1.50  horn:                                   18
% 7.24/1.50  ground:                                 5
% 7.24/1.50  unary:                                  7
% 7.24/1.50  binary:                                 7
% 7.24/1.50  lits:                                   38
% 7.24/1.50  lits_eq:                                5
% 7.24/1.50  fd_pure:                                0
% 7.24/1.50  fd_pseudo:                              0
% 7.24/1.50  fd_cond:                                0
% 7.24/1.50  fd_pseudo_cond:                         0
% 7.24/1.50  ac_symbols:                             0
% 7.24/1.50  
% 7.24/1.50  ------ Propositional Solver
% 7.24/1.50  
% 7.24/1.50  prop_solver_calls:                      28
% 7.24/1.50  prop_fast_solver_calls:                 1062
% 7.24/1.50  smt_solver_calls:                       0
% 7.24/1.50  smt_fast_solver_calls:                  0
% 7.24/1.50  prop_num_of_clauses:                    8990
% 7.24/1.50  prop_preprocess_simplified:             17566
% 7.24/1.50  prop_fo_subsumed:                       59
% 7.24/1.50  prop_solver_time:                       0.
% 7.24/1.50  smt_solver_time:                        0.
% 7.24/1.50  smt_fast_solver_time:                   0.
% 7.24/1.50  prop_fast_solver_time:                  0.
% 7.24/1.50  prop_unsat_core_time:                   0.001
% 7.24/1.50  
% 7.24/1.50  ------ QBF
% 7.24/1.50  
% 7.24/1.50  qbf_q_res:                              0
% 7.24/1.50  qbf_num_tautologies:                    0
% 7.24/1.50  qbf_prep_cycles:                        0
% 7.24/1.50  
% 7.24/1.50  ------ BMC1
% 7.24/1.50  
% 7.24/1.50  bmc1_current_bound:                     -1
% 7.24/1.50  bmc1_last_solved_bound:                 -1
% 7.24/1.50  bmc1_unsat_core_size:                   -1
% 7.24/1.50  bmc1_unsat_core_parents_size:           -1
% 7.24/1.50  bmc1_merge_next_fun:                    0
% 7.24/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.24/1.50  
% 7.24/1.50  ------ Instantiation
% 7.24/1.50  
% 7.24/1.50  inst_num_of_clauses:                    2354
% 7.24/1.50  inst_num_in_passive:                    1042
% 7.24/1.50  inst_num_in_active:                     1063
% 7.24/1.50  inst_num_in_unprocessed:                249
% 7.24/1.50  inst_num_of_loops:                      1080
% 7.24/1.50  inst_num_of_learning_restarts:          0
% 7.24/1.50  inst_num_moves_active_passive:          13
% 7.24/1.50  inst_lit_activity:                      0
% 7.24/1.50  inst_lit_activity_moves:                0
% 7.24/1.50  inst_num_tautologies:                   0
% 7.24/1.50  inst_num_prop_implied:                  0
% 7.24/1.50  inst_num_existing_simplified:           0
% 7.24/1.50  inst_num_eq_res_simplified:             0
% 7.24/1.50  inst_num_child_elim:                    0
% 7.24/1.50  inst_num_of_dismatching_blockings:      829
% 7.24/1.50  inst_num_of_non_proper_insts:           1975
% 7.24/1.50  inst_num_of_duplicates:                 0
% 7.24/1.50  inst_inst_num_from_inst_to_res:         0
% 7.24/1.50  inst_dismatching_checking_time:         0.
% 7.24/1.50  
% 7.24/1.50  ------ Resolution
% 7.24/1.50  
% 7.24/1.50  res_num_of_clauses:                     0
% 7.24/1.50  res_num_in_passive:                     0
% 7.24/1.50  res_num_in_active:                      0
% 7.24/1.50  res_num_of_loops:                       102
% 7.24/1.50  res_forward_subset_subsumed:            105
% 7.24/1.50  res_backward_subset_subsumed:           6
% 7.24/1.50  res_forward_subsumed:                   0
% 7.24/1.50  res_backward_subsumed:                  0
% 7.24/1.50  res_forward_subsumption_resolution:     0
% 7.24/1.50  res_backward_subsumption_resolution:    0
% 7.24/1.50  res_clause_to_clause_subsumption:       1523
% 7.24/1.50  res_orphan_elimination:                 0
% 7.24/1.50  res_tautology_del:                      146
% 7.24/1.50  res_num_eq_res_simplified:              0
% 7.24/1.50  res_num_sel_changes:                    0
% 7.24/1.50  res_moves_from_active_to_pass:          0
% 7.24/1.50  
% 7.24/1.50  ------ Superposition
% 7.24/1.50  
% 7.24/1.50  sup_time_total:                         0.
% 7.24/1.50  sup_time_generating:                    0.
% 7.24/1.50  sup_time_sim_full:                      0.
% 7.24/1.50  sup_time_sim_immed:                     0.
% 7.24/1.50  
% 7.24/1.50  sup_num_of_clauses:                     558
% 7.24/1.50  sup_num_in_active:                      203
% 7.24/1.50  sup_num_in_passive:                     355
% 7.24/1.50  sup_num_of_loops:                       215
% 7.24/1.50  sup_fw_superposition:                   343
% 7.24/1.50  sup_bw_superposition:                   425
% 7.24/1.50  sup_immediate_simplified:               301
% 7.24/1.50  sup_given_eliminated:                   0
% 7.24/1.50  comparisons_done:                       0
% 7.24/1.50  comparisons_avoided:                    0
% 7.24/1.50  
% 7.24/1.50  ------ Simplifications
% 7.24/1.50  
% 7.24/1.50  
% 7.24/1.50  sim_fw_subset_subsumed:                 33
% 7.24/1.50  sim_bw_subset_subsumed:                 5
% 7.24/1.50  sim_fw_subsumed:                        24
% 7.24/1.50  sim_bw_subsumed:                        4
% 7.24/1.50  sim_fw_subsumption_res:                 4
% 7.24/1.50  sim_bw_subsumption_res:                 0
% 7.24/1.50  sim_tautology_del:                      1
% 7.24/1.50  sim_eq_tautology_del:                   0
% 7.24/1.50  sim_eq_res_simp:                        0
% 7.24/1.50  sim_fw_demodulated:                     57
% 7.24/1.50  sim_bw_demodulated:                     15
% 7.24/1.50  sim_light_normalised:                   212
% 7.24/1.50  sim_joinable_taut:                      0
% 7.24/1.50  sim_joinable_simp:                      0
% 7.24/1.50  sim_ac_normalised:                      0
% 7.24/1.50  sim_smt_subsumption:                    0
% 7.24/1.50  
%------------------------------------------------------------------------------
