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
% DateTime   : Thu Dec  3 12:18:01 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 524 expanded)
%              Number of clauses        :   80 ( 157 expanded)
%              Number of leaves         :   17 ( 153 expanded)
%              Depth                    :   18
%              Number of atoms          :  447 (3031 expanded)
%              Number of equality atoms :  114 ( 211 expanded)
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
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f44])).

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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_721,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_726,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1735,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_721,c_726])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_301,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_302,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ v4_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_19])).

cnf(c_307,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_306])).

cnf(c_717,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_1980,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_717])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,negated_conjecture,
    ( v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,plain,
    ( v2_compts_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,negated_conjecture,
    ( v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_213,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_214,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_218,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_214,c_19,c_18])).

cnf(c_763,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_764,plain,
    ( v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_3244,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1980,c_23,c_26,c_764])).

cnf(c_3245,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3244])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_730,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_720,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_725,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1867,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X0)) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_725])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_727,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1320,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_720,c_727])).

cnf(c_1870,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X0)) = k4_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1867,c_1320])).

cnf(c_2199,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0))) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_1870])).

cnf(c_8675,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_721,c_2199])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_728,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1284,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_721,c_728])).

cnf(c_8697,plain,
    ( k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_8675,c_1284])).

cnf(c_8698,plain,
    ( k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_8697,c_1735])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_729,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1609,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1320,c_729])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2120,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1609,c_22])).

cnf(c_9292,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8698,c_2120])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_11,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_238,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_239,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_275,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_239,c_18])).

cnf(c_276,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ v4_pre_topc(X1,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v2_compts_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_276,c_19])).

cnf(c_279,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_718,plain,
    ( v2_compts_1(X0,sK0) != iProver_top
    | v2_compts_1(X1,sK0) = iProver_top
    | v4_pre_topc(X1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_1505,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_718])).

cnf(c_14,negated_conjecture,
    ( v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1567,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1505,c_25])).

cnf(c_12201,plain,
    ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top
    | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9292,c_1567])).

cnf(c_12,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_724,plain,
    ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1978,plain,
    ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1735,c_724])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_731,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_732,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_731,c_0])).

cnf(c_1321,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_732,c_727])).

cnf(c_2258,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_729])).

cnf(c_3838,plain,
    ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2258,c_732])).

cnf(c_9298,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8698,c_3838])).

cnf(c_12385,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12201,c_1978,c_9298])).

cnf(c_12389,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3245,c_12385])).

cnf(c_766,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_767,plain,
    ( v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12389,c_767,c_25,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:24:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.13/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.01  
% 4.13/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.13/1.01  
% 4.13/1.01  ------  iProver source info
% 4.13/1.01  
% 4.13/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.13/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.13/1.01  git: non_committed_changes: false
% 4.13/1.01  git: last_make_outside_of_git: false
% 4.13/1.01  
% 4.13/1.01  ------ 
% 4.13/1.01  
% 4.13/1.01  ------ Input Options
% 4.13/1.01  
% 4.13/1.01  --out_options                           all
% 4.13/1.01  --tptp_safe_out                         true
% 4.13/1.01  --problem_path                          ""
% 4.13/1.01  --include_path                          ""
% 4.13/1.01  --clausifier                            res/vclausify_rel
% 4.13/1.01  --clausifier_options                    ""
% 4.13/1.01  --stdin                                 false
% 4.13/1.01  --stats_out                             all
% 4.13/1.01  
% 4.13/1.01  ------ General Options
% 4.13/1.01  
% 4.13/1.01  --fof                                   false
% 4.13/1.01  --time_out_real                         305.
% 4.13/1.01  --time_out_virtual                      -1.
% 4.13/1.01  --symbol_type_check                     false
% 4.13/1.01  --clausify_out                          false
% 4.13/1.01  --sig_cnt_out                           false
% 4.13/1.01  --trig_cnt_out                          false
% 4.13/1.01  --trig_cnt_out_tolerance                1.
% 4.13/1.01  --trig_cnt_out_sk_spl                   false
% 4.13/1.01  --abstr_cl_out                          false
% 4.13/1.01  
% 4.13/1.01  ------ Global Options
% 4.13/1.01  
% 4.13/1.01  --schedule                              default
% 4.13/1.01  --add_important_lit                     false
% 4.13/1.01  --prop_solver_per_cl                    1000
% 4.13/1.01  --min_unsat_core                        false
% 4.13/1.01  --soft_assumptions                      false
% 4.13/1.01  --soft_lemma_size                       3
% 4.13/1.01  --prop_impl_unit_size                   0
% 4.13/1.01  --prop_impl_unit                        []
% 4.13/1.01  --share_sel_clauses                     true
% 4.13/1.01  --reset_solvers                         false
% 4.13/1.01  --bc_imp_inh                            [conj_cone]
% 4.13/1.01  --conj_cone_tolerance                   3.
% 4.13/1.01  --extra_neg_conj                        none
% 4.13/1.01  --large_theory_mode                     true
% 4.13/1.01  --prolific_symb_bound                   200
% 4.13/1.01  --lt_threshold                          2000
% 4.13/1.01  --clause_weak_htbl                      true
% 4.13/1.01  --gc_record_bc_elim                     false
% 4.13/1.01  
% 4.13/1.01  ------ Preprocessing Options
% 4.13/1.01  
% 4.13/1.01  --preprocessing_flag                    true
% 4.13/1.01  --time_out_prep_mult                    0.1
% 4.13/1.01  --splitting_mode                        input
% 4.13/1.01  --splitting_grd                         true
% 4.13/1.01  --splitting_cvd                         false
% 4.13/1.01  --splitting_cvd_svl                     false
% 4.13/1.01  --splitting_nvd                         32
% 4.13/1.01  --sub_typing                            true
% 4.13/1.01  --prep_gs_sim                           true
% 4.13/1.01  --prep_unflatten                        true
% 4.13/1.01  --prep_res_sim                          true
% 4.13/1.01  --prep_upred                            true
% 4.13/1.01  --prep_sem_filter                       exhaustive
% 4.13/1.01  --prep_sem_filter_out                   false
% 4.13/1.01  --pred_elim                             true
% 4.13/1.01  --res_sim_input                         true
% 4.13/1.01  --eq_ax_congr_red                       true
% 4.13/1.01  --pure_diseq_elim                       true
% 4.13/1.01  --brand_transform                       false
% 4.13/1.01  --non_eq_to_eq                          false
% 4.13/1.01  --prep_def_merge                        true
% 4.13/1.01  --prep_def_merge_prop_impl              false
% 4.13/1.02  --prep_def_merge_mbd                    true
% 4.13/1.02  --prep_def_merge_tr_red                 false
% 4.13/1.02  --prep_def_merge_tr_cl                  false
% 4.13/1.02  --smt_preprocessing                     true
% 4.13/1.02  --smt_ac_axioms                         fast
% 4.13/1.02  --preprocessed_out                      false
% 4.13/1.02  --preprocessed_stats                    false
% 4.13/1.02  
% 4.13/1.02  ------ Abstraction refinement Options
% 4.13/1.02  
% 4.13/1.02  --abstr_ref                             []
% 4.13/1.02  --abstr_ref_prep                        false
% 4.13/1.02  --abstr_ref_until_sat                   false
% 4.13/1.02  --abstr_ref_sig_restrict                funpre
% 4.13/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 4.13/1.02  --abstr_ref_under                       []
% 4.13/1.02  
% 4.13/1.02  ------ SAT Options
% 4.13/1.02  
% 4.13/1.02  --sat_mode                              false
% 4.13/1.02  --sat_fm_restart_options                ""
% 4.13/1.02  --sat_gr_def                            false
% 4.13/1.02  --sat_epr_types                         true
% 4.13/1.02  --sat_non_cyclic_types                  false
% 4.13/1.02  --sat_finite_models                     false
% 4.13/1.02  --sat_fm_lemmas                         false
% 4.13/1.02  --sat_fm_prep                           false
% 4.13/1.02  --sat_fm_uc_incr                        true
% 4.13/1.02  --sat_out_model                         small
% 4.13/1.02  --sat_out_clauses                       false
% 4.13/1.02  
% 4.13/1.02  ------ QBF Options
% 4.13/1.02  
% 4.13/1.02  --qbf_mode                              false
% 4.13/1.02  --qbf_elim_univ                         false
% 4.13/1.02  --qbf_dom_inst                          none
% 4.13/1.02  --qbf_dom_pre_inst                      false
% 4.13/1.02  --qbf_sk_in                             false
% 4.13/1.02  --qbf_pred_elim                         true
% 4.13/1.02  --qbf_split                             512
% 4.13/1.02  
% 4.13/1.02  ------ BMC1 Options
% 4.13/1.02  
% 4.13/1.02  --bmc1_incremental                      false
% 4.13/1.02  --bmc1_axioms                           reachable_all
% 4.13/1.02  --bmc1_min_bound                        0
% 4.13/1.02  --bmc1_max_bound                        -1
% 4.13/1.02  --bmc1_max_bound_default                -1
% 4.13/1.02  --bmc1_symbol_reachability              true
% 4.13/1.02  --bmc1_property_lemmas                  false
% 4.13/1.02  --bmc1_k_induction                      false
% 4.13/1.02  --bmc1_non_equiv_states                 false
% 4.13/1.02  --bmc1_deadlock                         false
% 4.13/1.02  --bmc1_ucm                              false
% 4.13/1.02  --bmc1_add_unsat_core                   none
% 4.13/1.02  --bmc1_unsat_core_children              false
% 4.13/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 4.13/1.02  --bmc1_out_stat                         full
% 4.13/1.02  --bmc1_ground_init                      false
% 4.13/1.02  --bmc1_pre_inst_next_state              false
% 4.13/1.02  --bmc1_pre_inst_state                   false
% 4.13/1.02  --bmc1_pre_inst_reach_state             false
% 4.13/1.02  --bmc1_out_unsat_core                   false
% 4.13/1.02  --bmc1_aig_witness_out                  false
% 4.13/1.02  --bmc1_verbose                          false
% 4.13/1.02  --bmc1_dump_clauses_tptp                false
% 4.13/1.02  --bmc1_dump_unsat_core_tptp             false
% 4.13/1.02  --bmc1_dump_file                        -
% 4.13/1.02  --bmc1_ucm_expand_uc_limit              128
% 4.13/1.02  --bmc1_ucm_n_expand_iterations          6
% 4.13/1.02  --bmc1_ucm_extend_mode                  1
% 4.13/1.02  --bmc1_ucm_init_mode                    2
% 4.13/1.02  --bmc1_ucm_cone_mode                    none
% 4.13/1.02  --bmc1_ucm_reduced_relation_type        0
% 4.13/1.02  --bmc1_ucm_relax_model                  4
% 4.13/1.02  --bmc1_ucm_full_tr_after_sat            true
% 4.13/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 4.13/1.02  --bmc1_ucm_layered_model                none
% 4.13/1.02  --bmc1_ucm_max_lemma_size               10
% 4.13/1.02  
% 4.13/1.02  ------ AIG Options
% 4.13/1.02  
% 4.13/1.02  --aig_mode                              false
% 4.13/1.02  
% 4.13/1.02  ------ Instantiation Options
% 4.13/1.02  
% 4.13/1.02  --instantiation_flag                    true
% 4.13/1.02  --inst_sos_flag                         true
% 4.13/1.02  --inst_sos_phase                        true
% 4.13/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.13/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.13/1.02  --inst_lit_sel_side                     num_symb
% 4.13/1.02  --inst_solver_per_active                1400
% 4.13/1.02  --inst_solver_calls_frac                1.
% 4.13/1.02  --inst_passive_queue_type               priority_queues
% 4.13/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.13/1.02  --inst_passive_queues_freq              [25;2]
% 4.13/1.02  --inst_dismatching                      true
% 4.13/1.02  --inst_eager_unprocessed_to_passive     true
% 4.13/1.02  --inst_prop_sim_given                   true
% 4.13/1.02  --inst_prop_sim_new                     false
% 4.13/1.02  --inst_subs_new                         false
% 4.13/1.02  --inst_eq_res_simp                      false
% 4.13/1.02  --inst_subs_given                       false
% 4.13/1.02  --inst_orphan_elimination               true
% 4.13/1.02  --inst_learning_loop_flag               true
% 4.13/1.02  --inst_learning_start                   3000
% 4.13/1.02  --inst_learning_factor                  2
% 4.13/1.02  --inst_start_prop_sim_after_learn       3
% 4.13/1.02  --inst_sel_renew                        solver
% 4.13/1.02  --inst_lit_activity_flag                true
% 4.13/1.02  --inst_restr_to_given                   false
% 4.13/1.02  --inst_activity_threshold               500
% 4.13/1.02  --inst_out_proof                        true
% 4.13/1.02  
% 4.13/1.02  ------ Resolution Options
% 4.13/1.02  
% 4.13/1.02  --resolution_flag                       true
% 4.13/1.02  --res_lit_sel                           adaptive
% 4.13/1.02  --res_lit_sel_side                      none
% 4.13/1.02  --res_ordering                          kbo
% 4.13/1.02  --res_to_prop_solver                    active
% 4.13/1.02  --res_prop_simpl_new                    false
% 4.13/1.02  --res_prop_simpl_given                  true
% 4.13/1.02  --res_passive_queue_type                priority_queues
% 4.13/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.13/1.02  --res_passive_queues_freq               [15;5]
% 4.13/1.02  --res_forward_subs                      full
% 4.13/1.02  --res_backward_subs                     full
% 4.13/1.02  --res_forward_subs_resolution           true
% 4.13/1.02  --res_backward_subs_resolution          true
% 4.13/1.02  --res_orphan_elimination                true
% 4.13/1.02  --res_time_limit                        2.
% 4.13/1.02  --res_out_proof                         true
% 4.13/1.02  
% 4.13/1.02  ------ Superposition Options
% 4.13/1.02  
% 4.13/1.02  --superposition_flag                    true
% 4.13/1.02  --sup_passive_queue_type                priority_queues
% 4.13/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.13/1.02  --sup_passive_queues_freq               [8;1;4]
% 4.13/1.02  --demod_completeness_check              fast
% 4.13/1.02  --demod_use_ground                      true
% 4.13/1.02  --sup_to_prop_solver                    passive
% 4.13/1.02  --sup_prop_simpl_new                    true
% 4.13/1.02  --sup_prop_simpl_given                  true
% 4.13/1.02  --sup_fun_splitting                     true
% 4.13/1.02  --sup_smt_interval                      50000
% 4.13/1.02  
% 4.13/1.02  ------ Superposition Simplification Setup
% 4.13/1.02  
% 4.13/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.13/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.13/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.13/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.13/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 4.13/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.13/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.13/1.02  --sup_immed_triv                        [TrivRules]
% 4.13/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.13/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.13/1.02  --sup_immed_bw_main                     []
% 4.13/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.13/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 4.13/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.13/1.02  --sup_input_bw                          []
% 4.13/1.02  
% 4.13/1.02  ------ Combination Options
% 4.13/1.02  
% 4.13/1.02  --comb_res_mult                         3
% 4.13/1.02  --comb_sup_mult                         2
% 4.13/1.02  --comb_inst_mult                        10
% 4.13/1.02  
% 4.13/1.02  ------ Debug Options
% 4.13/1.02  
% 4.13/1.02  --dbg_backtrace                         false
% 4.13/1.02  --dbg_dump_prop_clauses                 false
% 4.13/1.02  --dbg_dump_prop_clauses_file            -
% 4.13/1.02  --dbg_out_stat                          false
% 4.13/1.02  ------ Parsing...
% 4.13/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.13/1.02  
% 4.13/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.13/1.02  
% 4.13/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.13/1.02  
% 4.13/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.02  ------ Proving...
% 4.13/1.02  ------ Problem Properties 
% 4.13/1.02  
% 4.13/1.02  
% 4.13/1.02  clauses                                 16
% 4.13/1.02  conjectures                             5
% 4.13/1.02  EPR                                     2
% 4.13/1.02  Horn                                    16
% 4.13/1.02  unary                                   7
% 4.13/1.02  binary                                  5
% 4.13/1.02  lits                                    34
% 4.13/1.02  lits eq                                 5
% 4.13/1.02  fd_pure                                 0
% 4.13/1.02  fd_pseudo                               0
% 4.13/1.02  fd_cond                                 0
% 4.13/1.02  fd_pseudo_cond                          0
% 4.13/1.02  AC symbols                              0
% 4.13/1.02  
% 4.13/1.02  ------ Schedule dynamic 5 is on 
% 4.13/1.02  
% 4.13/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.13/1.02  
% 4.13/1.02  
% 4.13/1.02  ------ 
% 4.13/1.02  Current options:
% 4.13/1.02  ------ 
% 4.13/1.02  
% 4.13/1.02  ------ Input Options
% 4.13/1.02  
% 4.13/1.02  --out_options                           all
% 4.13/1.02  --tptp_safe_out                         true
% 4.13/1.02  --problem_path                          ""
% 4.13/1.02  --include_path                          ""
% 4.13/1.02  --clausifier                            res/vclausify_rel
% 4.13/1.02  --clausifier_options                    ""
% 4.13/1.02  --stdin                                 false
% 4.13/1.02  --stats_out                             all
% 4.13/1.02  
% 4.13/1.02  ------ General Options
% 4.13/1.02  
% 4.13/1.02  --fof                                   false
% 4.13/1.02  --time_out_real                         305.
% 4.13/1.02  --time_out_virtual                      -1.
% 4.13/1.02  --symbol_type_check                     false
% 4.13/1.02  --clausify_out                          false
% 4.13/1.02  --sig_cnt_out                           false
% 4.13/1.02  --trig_cnt_out                          false
% 4.13/1.02  --trig_cnt_out_tolerance                1.
% 4.13/1.02  --trig_cnt_out_sk_spl                   false
% 4.13/1.02  --abstr_cl_out                          false
% 4.13/1.02  
% 4.13/1.02  ------ Global Options
% 4.13/1.02  
% 4.13/1.02  --schedule                              default
% 4.13/1.02  --add_important_lit                     false
% 4.13/1.02  --prop_solver_per_cl                    1000
% 4.13/1.02  --min_unsat_core                        false
% 4.13/1.02  --soft_assumptions                      false
% 4.13/1.02  --soft_lemma_size                       3
% 4.13/1.02  --prop_impl_unit_size                   0
% 4.13/1.02  --prop_impl_unit                        []
% 4.13/1.02  --share_sel_clauses                     true
% 4.13/1.02  --reset_solvers                         false
% 4.13/1.02  --bc_imp_inh                            [conj_cone]
% 4.13/1.02  --conj_cone_tolerance                   3.
% 4.13/1.02  --extra_neg_conj                        none
% 4.13/1.02  --large_theory_mode                     true
% 4.13/1.02  --prolific_symb_bound                   200
% 4.13/1.02  --lt_threshold                          2000
% 4.13/1.02  --clause_weak_htbl                      true
% 4.13/1.02  --gc_record_bc_elim                     false
% 4.13/1.02  
% 4.13/1.02  ------ Preprocessing Options
% 4.13/1.02  
% 4.13/1.02  --preprocessing_flag                    true
% 4.13/1.02  --time_out_prep_mult                    0.1
% 4.13/1.02  --splitting_mode                        input
% 4.13/1.02  --splitting_grd                         true
% 4.13/1.02  --splitting_cvd                         false
% 4.13/1.02  --splitting_cvd_svl                     false
% 4.13/1.02  --splitting_nvd                         32
% 4.13/1.02  --sub_typing                            true
% 4.13/1.02  --prep_gs_sim                           true
% 4.13/1.02  --prep_unflatten                        true
% 4.13/1.02  --prep_res_sim                          true
% 4.13/1.02  --prep_upred                            true
% 4.13/1.02  --prep_sem_filter                       exhaustive
% 4.13/1.02  --prep_sem_filter_out                   false
% 4.13/1.02  --pred_elim                             true
% 4.13/1.02  --res_sim_input                         true
% 4.13/1.02  --eq_ax_congr_red                       true
% 4.13/1.02  --pure_diseq_elim                       true
% 4.13/1.02  --brand_transform                       false
% 4.13/1.02  --non_eq_to_eq                          false
% 4.13/1.02  --prep_def_merge                        true
% 4.13/1.02  --prep_def_merge_prop_impl              false
% 4.13/1.02  --prep_def_merge_mbd                    true
% 4.13/1.02  --prep_def_merge_tr_red                 false
% 4.13/1.02  --prep_def_merge_tr_cl                  false
% 4.13/1.02  --smt_preprocessing                     true
% 4.13/1.02  --smt_ac_axioms                         fast
% 4.13/1.02  --preprocessed_out                      false
% 4.13/1.02  --preprocessed_stats                    false
% 4.13/1.02  
% 4.13/1.02  ------ Abstraction refinement Options
% 4.13/1.02  
% 4.13/1.02  --abstr_ref                             []
% 4.13/1.02  --abstr_ref_prep                        false
% 4.13/1.02  --abstr_ref_until_sat                   false
% 4.13/1.02  --abstr_ref_sig_restrict                funpre
% 4.13/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 4.13/1.02  --abstr_ref_under                       []
% 4.13/1.02  
% 4.13/1.02  ------ SAT Options
% 4.13/1.02  
% 4.13/1.02  --sat_mode                              false
% 4.13/1.02  --sat_fm_restart_options                ""
% 4.13/1.02  --sat_gr_def                            false
% 4.13/1.02  --sat_epr_types                         true
% 4.13/1.02  --sat_non_cyclic_types                  false
% 4.13/1.02  --sat_finite_models                     false
% 4.13/1.02  --sat_fm_lemmas                         false
% 4.13/1.02  --sat_fm_prep                           false
% 4.13/1.02  --sat_fm_uc_incr                        true
% 4.13/1.02  --sat_out_model                         small
% 4.13/1.02  --sat_out_clauses                       false
% 4.13/1.02  
% 4.13/1.02  ------ QBF Options
% 4.13/1.02  
% 4.13/1.02  --qbf_mode                              false
% 4.13/1.02  --qbf_elim_univ                         false
% 4.13/1.02  --qbf_dom_inst                          none
% 4.13/1.02  --qbf_dom_pre_inst                      false
% 4.13/1.02  --qbf_sk_in                             false
% 4.13/1.02  --qbf_pred_elim                         true
% 4.13/1.02  --qbf_split                             512
% 4.13/1.02  
% 4.13/1.02  ------ BMC1 Options
% 4.13/1.02  
% 4.13/1.02  --bmc1_incremental                      false
% 4.13/1.02  --bmc1_axioms                           reachable_all
% 4.13/1.02  --bmc1_min_bound                        0
% 4.13/1.02  --bmc1_max_bound                        -1
% 4.13/1.02  --bmc1_max_bound_default                -1
% 4.13/1.02  --bmc1_symbol_reachability              true
% 4.13/1.02  --bmc1_property_lemmas                  false
% 4.13/1.02  --bmc1_k_induction                      false
% 4.13/1.02  --bmc1_non_equiv_states                 false
% 4.13/1.02  --bmc1_deadlock                         false
% 4.13/1.02  --bmc1_ucm                              false
% 4.13/1.02  --bmc1_add_unsat_core                   none
% 4.13/1.02  --bmc1_unsat_core_children              false
% 4.13/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 4.13/1.02  --bmc1_out_stat                         full
% 4.13/1.02  --bmc1_ground_init                      false
% 4.13/1.02  --bmc1_pre_inst_next_state              false
% 4.13/1.02  --bmc1_pre_inst_state                   false
% 4.13/1.02  --bmc1_pre_inst_reach_state             false
% 4.13/1.02  --bmc1_out_unsat_core                   false
% 4.13/1.02  --bmc1_aig_witness_out                  false
% 4.13/1.02  --bmc1_verbose                          false
% 4.13/1.02  --bmc1_dump_clauses_tptp                false
% 4.13/1.02  --bmc1_dump_unsat_core_tptp             false
% 4.13/1.02  --bmc1_dump_file                        -
% 4.13/1.02  --bmc1_ucm_expand_uc_limit              128
% 4.13/1.02  --bmc1_ucm_n_expand_iterations          6
% 4.13/1.02  --bmc1_ucm_extend_mode                  1
% 4.13/1.02  --bmc1_ucm_init_mode                    2
% 4.13/1.02  --bmc1_ucm_cone_mode                    none
% 4.13/1.02  --bmc1_ucm_reduced_relation_type        0
% 4.13/1.02  --bmc1_ucm_relax_model                  4
% 4.13/1.02  --bmc1_ucm_full_tr_after_sat            true
% 4.13/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 4.13/1.02  --bmc1_ucm_layered_model                none
% 4.13/1.02  --bmc1_ucm_max_lemma_size               10
% 4.13/1.02  
% 4.13/1.02  ------ AIG Options
% 4.13/1.02  
% 4.13/1.02  --aig_mode                              false
% 4.13/1.02  
% 4.13/1.02  ------ Instantiation Options
% 4.13/1.02  
% 4.13/1.02  --instantiation_flag                    true
% 4.13/1.02  --inst_sos_flag                         true
% 4.13/1.02  --inst_sos_phase                        true
% 4.13/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.13/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.13/1.02  --inst_lit_sel_side                     none
% 4.13/1.02  --inst_solver_per_active                1400
% 4.13/1.02  --inst_solver_calls_frac                1.
% 4.13/1.02  --inst_passive_queue_type               priority_queues
% 4.13/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.13/1.02  --inst_passive_queues_freq              [25;2]
% 4.13/1.02  --inst_dismatching                      true
% 4.13/1.02  --inst_eager_unprocessed_to_passive     true
% 4.13/1.02  --inst_prop_sim_given                   true
% 4.13/1.02  --inst_prop_sim_new                     false
% 4.13/1.02  --inst_subs_new                         false
% 4.13/1.02  --inst_eq_res_simp                      false
% 4.13/1.02  --inst_subs_given                       false
% 4.13/1.02  --inst_orphan_elimination               true
% 4.13/1.02  --inst_learning_loop_flag               true
% 4.13/1.02  --inst_learning_start                   3000
% 4.13/1.02  --inst_learning_factor                  2
% 4.13/1.02  --inst_start_prop_sim_after_learn       3
% 4.13/1.02  --inst_sel_renew                        solver
% 4.13/1.02  --inst_lit_activity_flag                true
% 4.13/1.02  --inst_restr_to_given                   false
% 4.13/1.02  --inst_activity_threshold               500
% 4.13/1.02  --inst_out_proof                        true
% 4.13/1.02  
% 4.13/1.02  ------ Resolution Options
% 4.13/1.02  
% 4.13/1.02  --resolution_flag                       false
% 4.13/1.02  --res_lit_sel                           adaptive
% 4.13/1.02  --res_lit_sel_side                      none
% 4.13/1.02  --res_ordering                          kbo
% 4.13/1.02  --res_to_prop_solver                    active
% 4.13/1.02  --res_prop_simpl_new                    false
% 4.13/1.02  --res_prop_simpl_given                  true
% 4.13/1.02  --res_passive_queue_type                priority_queues
% 4.13/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.13/1.02  --res_passive_queues_freq               [15;5]
% 4.13/1.02  --res_forward_subs                      full
% 4.13/1.02  --res_backward_subs                     full
% 4.13/1.02  --res_forward_subs_resolution           true
% 4.13/1.02  --res_backward_subs_resolution          true
% 4.13/1.02  --res_orphan_elimination                true
% 4.13/1.02  --res_time_limit                        2.
% 4.13/1.02  --res_out_proof                         true
% 4.13/1.02  
% 4.13/1.02  ------ Superposition Options
% 4.13/1.02  
% 4.13/1.02  --superposition_flag                    true
% 4.13/1.02  --sup_passive_queue_type                priority_queues
% 4.13/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.13/1.02  --sup_passive_queues_freq               [8;1;4]
% 4.13/1.02  --demod_completeness_check              fast
% 4.13/1.02  --demod_use_ground                      true
% 4.13/1.02  --sup_to_prop_solver                    passive
% 4.13/1.02  --sup_prop_simpl_new                    true
% 4.13/1.02  --sup_prop_simpl_given                  true
% 4.13/1.02  --sup_fun_splitting                     true
% 4.13/1.02  --sup_smt_interval                      50000
% 4.13/1.02  
% 4.13/1.02  ------ Superposition Simplification Setup
% 4.13/1.02  
% 4.13/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.13/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.13/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.13/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.13/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 4.13/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.13/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.13/1.02  --sup_immed_triv                        [TrivRules]
% 4.13/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.13/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.13/1.02  --sup_immed_bw_main                     []
% 4.13/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.13/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 4.13/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.13/1.02  --sup_input_bw                          []
% 4.13/1.02  
% 4.13/1.02  ------ Combination Options
% 4.13/1.02  
% 4.13/1.02  --comb_res_mult                         3
% 4.13/1.02  --comb_sup_mult                         2
% 4.13/1.02  --comb_inst_mult                        10
% 4.13/1.02  
% 4.13/1.02  ------ Debug Options
% 4.13/1.02  
% 4.13/1.02  --dbg_backtrace                         false
% 4.13/1.02  --dbg_dump_prop_clauses                 false
% 4.13/1.02  --dbg_dump_prop_clauses_file            -
% 4.13/1.02  --dbg_out_stat                          false
% 4.13/1.02  
% 4.13/1.02  
% 4.13/1.02  
% 4.13/1.02  
% 4.13/1.02  ------ Proving...
% 4.13/1.02  
% 4.13/1.02  
% 4.13/1.02  % SZS status Theorem for theBenchmark.p
% 4.13/1.02  
% 4.13/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 4.13/1.02  
% 4.13/1.02  fof(f14,conjecture,(
% 4.13/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f15,negated_conjecture,(
% 4.13/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 4.13/1.02    inference(negated_conjecture,[],[f14])).
% 4.13/1.02  
% 4.13/1.02  fof(f30,plain,(
% 4.13/1.02    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.13/1.02    inference(ennf_transformation,[],[f15])).
% 4.13/1.02  
% 4.13/1.02  fof(f31,plain,(
% 4.13/1.02    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.13/1.02    inference(flattening,[],[f30])).
% 4.13/1.02  
% 4.13/1.02  fof(f34,plain,(
% 4.13/1.02    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v2_compts_1(sK2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.13/1.02    introduced(choice_axiom,[])).
% 4.13/1.02  
% 4.13/1.02  fof(f33,plain,(
% 4.13/1.02    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(sK1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.13/1.02    introduced(choice_axiom,[])).
% 4.13/1.02  
% 4.13/1.02  fof(f32,plain,(
% 4.13/1.02    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 4.13/1.02    introduced(choice_axiom,[])).
% 4.13/1.02  
% 4.13/1.02  fof(f35,plain,(
% 4.13/1.02    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 4.13/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).
% 4.13/1.02  
% 4.13/1.02  fof(f52,plain,(
% 4.13/1.02    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.13/1.02    inference(cnf_transformation,[],[f35])).
% 4.13/1.02  
% 4.13/1.02  fof(f7,axiom,(
% 4.13/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f21,plain,(
% 4.13/1.02    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.13/1.02    inference(ennf_transformation,[],[f7])).
% 4.13/1.02  
% 4.13/1.02  fof(f42,plain,(
% 4.13/1.02    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.13/1.02    inference(cnf_transformation,[],[f21])).
% 4.13/1.02  
% 4.13/1.02  fof(f9,axiom,(
% 4.13/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f44,plain,(
% 4.13/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.13/1.02    inference(cnf_transformation,[],[f9])).
% 4.13/1.02  
% 4.13/1.02  fof(f57,plain,(
% 4.13/1.02    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.13/1.02    inference(definition_unfolding,[],[f42,f44])).
% 4.13/1.02  
% 4.13/1.02  fof(f11,axiom,(
% 4.13/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f24,plain,(
% 4.13/1.02    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.13/1.02    inference(ennf_transformation,[],[f11])).
% 4.13/1.02  
% 4.13/1.02  fof(f25,plain,(
% 4.13/1.02    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.13/1.02    inference(flattening,[],[f24])).
% 4.13/1.02  
% 4.13/1.02  fof(f46,plain,(
% 4.13/1.02    ( ! [X2,X0,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.13/1.02    inference(cnf_transformation,[],[f25])).
% 4.13/1.02  
% 4.13/1.02  fof(f50,plain,(
% 4.13/1.02    l1_pre_topc(sK0)),
% 4.13/1.02    inference(cnf_transformation,[],[f35])).
% 4.13/1.02  
% 4.13/1.02  fof(f49,plain,(
% 4.13/1.02    v2_pre_topc(sK0)),
% 4.13/1.02    inference(cnf_transformation,[],[f35])).
% 4.13/1.02  
% 4.13/1.02  fof(f55,plain,(
% 4.13/1.02    v2_compts_1(sK2,sK0)),
% 4.13/1.02    inference(cnf_transformation,[],[f35])).
% 4.13/1.02  
% 4.13/1.02  fof(f12,axiom,(
% 4.13/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f26,plain,(
% 4.13/1.02    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.13/1.02    inference(ennf_transformation,[],[f12])).
% 4.13/1.02  
% 4.13/1.02  fof(f27,plain,(
% 4.13/1.02    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.13/1.02    inference(flattening,[],[f26])).
% 4.13/1.02  
% 4.13/1.02  fof(f47,plain,(
% 4.13/1.02    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.13/1.02    inference(cnf_transformation,[],[f27])).
% 4.13/1.02  
% 4.13/1.02  fof(f53,plain,(
% 4.13/1.02    v8_pre_topc(sK0)),
% 4.13/1.02    inference(cnf_transformation,[],[f35])).
% 4.13/1.02  
% 4.13/1.02  fof(f3,axiom,(
% 4.13/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f17,plain,(
% 4.13/1.02    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.13/1.02    inference(ennf_transformation,[],[f3])).
% 4.13/1.02  
% 4.13/1.02  fof(f38,plain,(
% 4.13/1.02    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.13/1.02    inference(cnf_transformation,[],[f17])).
% 4.13/1.02  
% 4.13/1.02  fof(f51,plain,(
% 4.13/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.13/1.02    inference(cnf_transformation,[],[f35])).
% 4.13/1.02  
% 4.13/1.02  fof(f8,axiom,(
% 4.13/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f22,plain,(
% 4.13/1.02    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.13/1.02    inference(ennf_transformation,[],[f8])).
% 4.13/1.02  
% 4.13/1.02  fof(f43,plain,(
% 4.13/1.02    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.13/1.02    inference(cnf_transformation,[],[f22])).
% 4.13/1.02  
% 4.13/1.02  fof(f6,axiom,(
% 4.13/1.02    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f20,plain,(
% 4.13/1.02    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.13/1.02    inference(ennf_transformation,[],[f6])).
% 4.13/1.02  
% 4.13/1.02  fof(f41,plain,(
% 4.13/1.02    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.13/1.02    inference(cnf_transformation,[],[f20])).
% 4.13/1.02  
% 4.13/1.02  fof(f5,axiom,(
% 4.13/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f19,plain,(
% 4.13/1.02    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.13/1.02    inference(ennf_transformation,[],[f5])).
% 4.13/1.02  
% 4.13/1.02  fof(f40,plain,(
% 4.13/1.02    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.13/1.02    inference(cnf_transformation,[],[f19])).
% 4.13/1.02  
% 4.13/1.02  fof(f4,axiom,(
% 4.13/1.02    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f18,plain,(
% 4.13/1.02    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.13/1.02    inference(ennf_transformation,[],[f4])).
% 4.13/1.02  
% 4.13/1.02  fof(f39,plain,(
% 4.13/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.13/1.02    inference(cnf_transformation,[],[f18])).
% 4.13/1.02  
% 4.13/1.02  fof(f10,axiom,(
% 4.13/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f16,plain,(
% 4.13/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 4.13/1.02    inference(unused_predicate_definition_removal,[],[f10])).
% 4.13/1.02  
% 4.13/1.02  fof(f23,plain,(
% 4.13/1.02    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 4.13/1.02    inference(ennf_transformation,[],[f16])).
% 4.13/1.02  
% 4.13/1.02  fof(f45,plain,(
% 4.13/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.13/1.02    inference(cnf_transformation,[],[f23])).
% 4.13/1.02  
% 4.13/1.02  fof(f13,axiom,(
% 4.13/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f28,plain,(
% 4.13/1.02    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.13/1.02    inference(ennf_transformation,[],[f13])).
% 4.13/1.02  
% 4.13/1.02  fof(f29,plain,(
% 4.13/1.02    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.13/1.02    inference(flattening,[],[f28])).
% 4.13/1.02  
% 4.13/1.02  fof(f48,plain,(
% 4.13/1.02    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.13/1.02    inference(cnf_transformation,[],[f29])).
% 4.13/1.02  
% 4.13/1.02  fof(f54,plain,(
% 4.13/1.02    v2_compts_1(sK1,sK0)),
% 4.13/1.02    inference(cnf_transformation,[],[f35])).
% 4.13/1.02  
% 4.13/1.02  fof(f56,plain,(
% 4.13/1.02    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 4.13/1.02    inference(cnf_transformation,[],[f35])).
% 4.13/1.02  
% 4.13/1.02  fof(f2,axiom,(
% 4.13/1.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f37,plain,(
% 4.13/1.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 4.13/1.02    inference(cnf_transformation,[],[f2])).
% 4.13/1.02  
% 4.13/1.02  fof(f1,axiom,(
% 4.13/1.02    ! [X0] : k2_subset_1(X0) = X0),
% 4.13/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.02  
% 4.13/1.02  fof(f36,plain,(
% 4.13/1.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 4.13/1.02    inference(cnf_transformation,[],[f1])).
% 4.13/1.02  
% 4.13/1.02  cnf(c_16,negated_conjecture,
% 4.13/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.13/1.02      inference(cnf_transformation,[],[f52]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_721,plain,
% 4.13/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_6,plain,
% 4.13/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.13/1.02      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 4.13/1.02      inference(cnf_transformation,[],[f57]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_726,plain,
% 4.13/1.02      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 4.13/1.02      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_1735,plain,
% 4.13/1.02      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_721,c_726]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_9,plain,
% 4.13/1.02      ( ~ v4_pre_topc(X0,X1)
% 4.13/1.02      | ~ v4_pre_topc(X2,X1)
% 4.13/1.02      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ v2_pre_topc(X1)
% 4.13/1.02      | ~ l1_pre_topc(X1) ),
% 4.13/1.02      inference(cnf_transformation,[],[f46]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_18,negated_conjecture,
% 4.13/1.02      ( l1_pre_topc(sK0) ),
% 4.13/1.02      inference(cnf_transformation,[],[f50]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_301,plain,
% 4.13/1.02      ( ~ v4_pre_topc(X0,X1)
% 4.13/1.02      | ~ v4_pre_topc(X2,X1)
% 4.13/1.02      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ v2_pre_topc(X1)
% 4.13/1.02      | sK0 != X1 ),
% 4.13/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_302,plain,
% 4.13/1.02      ( ~ v4_pre_topc(X0,sK0)
% 4.13/1.02      | ~ v4_pre_topc(X1,sK0)
% 4.13/1.02      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.13/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.13/1.02      | ~ v2_pre_topc(sK0) ),
% 4.13/1.02      inference(unflattening,[status(thm)],[c_301]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_19,negated_conjecture,
% 4.13/1.02      ( v2_pre_topc(sK0) ),
% 4.13/1.02      inference(cnf_transformation,[],[f49]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_306,plain,
% 4.13/1.02      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.13/1.02      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 4.13/1.02      | ~ v4_pre_topc(X1,sK0)
% 4.13/1.02      | ~ v4_pre_topc(X0,sK0) ),
% 4.13/1.02      inference(global_propositional_subsumption,
% 4.13/1.02                [status(thm)],
% 4.13/1.02                [c_302,c_19]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_307,plain,
% 4.13/1.02      ( ~ v4_pre_topc(X0,sK0)
% 4.13/1.02      | ~ v4_pre_topc(X1,sK0)
% 4.13/1.02      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.13/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.13/1.02      inference(renaming,[status(thm)],[c_306]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_717,plain,
% 4.13/1.02      ( v4_pre_topc(X0,sK0) != iProver_top
% 4.13/1.02      | v4_pre_topc(X1,sK0) != iProver_top
% 4.13/1.02      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0) = iProver_top
% 4.13/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.13/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_1980,plain,
% 4.13/1.02      ( v4_pre_topc(X0,sK0) != iProver_top
% 4.13/1.02      | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 4.13/1.02      | v4_pre_topc(sK2,sK0) != iProver_top
% 4.13/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.13/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_1735,c_717]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_23,plain,
% 4.13/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_13,negated_conjecture,
% 4.13/1.02      ( v2_compts_1(sK2,sK0) ),
% 4.13/1.02      inference(cnf_transformation,[],[f55]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_26,plain,
% 4.13/1.02      ( v2_compts_1(sK2,sK0) = iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_10,plain,
% 4.13/1.02      ( ~ v2_compts_1(X0,X1)
% 4.13/1.02      | v4_pre_topc(X0,X1)
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ v8_pre_topc(X1)
% 4.13/1.02      | ~ v2_pre_topc(X1)
% 4.13/1.02      | ~ l1_pre_topc(X1) ),
% 4.13/1.02      inference(cnf_transformation,[],[f47]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_15,negated_conjecture,
% 4.13/1.02      ( v8_pre_topc(sK0) ),
% 4.13/1.02      inference(cnf_transformation,[],[f53]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_213,plain,
% 4.13/1.02      ( ~ v2_compts_1(X0,X1)
% 4.13/1.02      | v4_pre_topc(X0,X1)
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ v2_pre_topc(X1)
% 4.13/1.02      | ~ l1_pre_topc(X1)
% 4.13/1.02      | sK0 != X1 ),
% 4.13/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_214,plain,
% 4.13/1.02      ( ~ v2_compts_1(X0,sK0)
% 4.13/1.02      | v4_pre_topc(X0,sK0)
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.13/1.02      | ~ v2_pre_topc(sK0)
% 4.13/1.02      | ~ l1_pre_topc(sK0) ),
% 4.13/1.02      inference(unflattening,[status(thm)],[c_213]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_218,plain,
% 4.13/1.02      ( ~ v2_compts_1(X0,sK0)
% 4.13/1.02      | v4_pre_topc(X0,sK0)
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.13/1.02      inference(global_propositional_subsumption,
% 4.13/1.02                [status(thm)],
% 4.13/1.02                [c_214,c_19,c_18]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_763,plain,
% 4.13/1.02      ( ~ v2_compts_1(sK2,sK0)
% 4.13/1.02      | v4_pre_topc(sK2,sK0)
% 4.13/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.13/1.02      inference(instantiation,[status(thm)],[c_218]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_764,plain,
% 4.13/1.02      ( v2_compts_1(sK2,sK0) != iProver_top
% 4.13/1.02      | v4_pre_topc(sK2,sK0) = iProver_top
% 4.13/1.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_3244,plain,
% 4.13/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.13/1.02      | v4_pre_topc(X0,sK0) != iProver_top
% 4.13/1.02      | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top ),
% 4.13/1.02      inference(global_propositional_subsumption,
% 4.13/1.02                [status(thm)],
% 4.13/1.02                [c_1980,c_23,c_26,c_764]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_3245,plain,
% 4.13/1.02      ( v4_pre_topc(X0,sK0) != iProver_top
% 4.13/1.02      | v4_pre_topc(k1_setfam_1(k2_tarski(X0,sK2)),sK0) = iProver_top
% 4.13/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.13/1.02      inference(renaming,[status(thm)],[c_3244]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_2,plain,
% 4.13/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.13/1.02      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 4.13/1.02      inference(cnf_transformation,[],[f38]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_730,plain,
% 4.13/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.13/1.02      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_17,negated_conjecture,
% 4.13/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.13/1.02      inference(cnf_transformation,[],[f51]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_720,plain,
% 4.13/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_7,plain,
% 4.13/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.13/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.13/1.02      | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
% 4.13/1.02      inference(cnf_transformation,[],[f43]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_725,plain,
% 4.13/1.02      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 4.13/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 4.13/1.02      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_1867,plain,
% 4.13/1.02      ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X0)) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
% 4.13/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_720,c_725]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_5,plain,
% 4.13/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.13/1.02      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 4.13/1.02      inference(cnf_transformation,[],[f41]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_727,plain,
% 4.13/1.02      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 4.13/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_1320,plain,
% 4.13/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_720,c_727]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_1870,plain,
% 4.13/1.02      ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X0)) = k4_xboole_0(sK1,X0)
% 4.13/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.13/1.02      inference(light_normalisation,[status(thm)],[c_1867,c_1320]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_2199,plain,
% 4.13/1.02      ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0))) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X0))
% 4.13/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_730,c_1870]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_8675,plain,
% 4.13/1.02      ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK2)) ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_721,c_2199]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_4,plain,
% 4.13/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.13/1.02      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 4.13/1.02      inference(cnf_transformation,[],[f40]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_728,plain,
% 4.13/1.02      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 4.13/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_1284,plain,
% 4.13/1.02      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_721,c_728]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_8697,plain,
% 4.13/1.02      ( k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 4.13/1.02      inference(light_normalisation,[status(thm)],[c_8675,c_1284]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_8698,plain,
% 4.13/1.02      ( k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 4.13/1.02      inference(demodulation,[status(thm)],[c_8697,c_1735]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_3,plain,
% 4.13/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.13/1.02      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 4.13/1.02      inference(cnf_transformation,[],[f39]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_729,plain,
% 4.13/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.13/1.02      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_1609,plain,
% 4.13/1.02      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 4.13/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_1320,c_729]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_22,plain,
% 4.13/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_2120,plain,
% 4.13/1.02      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.13/1.02      inference(global_propositional_subsumption,
% 4.13/1.02                [status(thm)],
% 4.13/1.02                [c_1609,c_22]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_9292,plain,
% 4.13/1.02      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_8698,c_2120]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_8,plain,
% 4.13/1.02      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.13/1.02      inference(cnf_transformation,[],[f45]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_11,plain,
% 4.13/1.02      ( ~ v2_compts_1(X0,X1)
% 4.13/1.02      | v2_compts_1(X2,X1)
% 4.13/1.02      | ~ v4_pre_topc(X2,X1)
% 4.13/1.02      | ~ r1_tarski(X2,X0)
% 4.13/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ v2_pre_topc(X1)
% 4.13/1.02      | ~ l1_pre_topc(X1) ),
% 4.13/1.02      inference(cnf_transformation,[],[f48]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_238,plain,
% 4.13/1.02      ( ~ v2_compts_1(X0,X1)
% 4.13/1.02      | v2_compts_1(X2,X1)
% 4.13/1.02      | ~ v4_pre_topc(X2,X1)
% 4.13/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 4.13/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ v2_pre_topc(X1)
% 4.13/1.02      | ~ l1_pre_topc(X1)
% 4.13/1.02      | X2 != X3
% 4.13/1.02      | X0 != X4 ),
% 4.13/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_239,plain,
% 4.13/1.02      ( ~ v2_compts_1(X0,X1)
% 4.13/1.02      | v2_compts_1(X2,X1)
% 4.13/1.02      | ~ v4_pre_topc(X2,X1)
% 4.13/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 4.13/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ v2_pre_topc(X1)
% 4.13/1.02      | ~ l1_pre_topc(X1) ),
% 4.13/1.02      inference(unflattening,[status(thm)],[c_238]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_275,plain,
% 4.13/1.02      ( ~ v2_compts_1(X0,X1)
% 4.13/1.02      | v2_compts_1(X2,X1)
% 4.13/1.02      | ~ v4_pre_topc(X2,X1)
% 4.13/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.13/1.02      | ~ v2_pre_topc(X1)
% 4.13/1.02      | sK0 != X1 ),
% 4.13/1.02      inference(resolution_lifted,[status(thm)],[c_239,c_18]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_276,plain,
% 4.13/1.02      ( ~ v2_compts_1(X0,sK0)
% 4.13/1.02      | v2_compts_1(X1,sK0)
% 4.13/1.02      | ~ v4_pre_topc(X1,sK0)
% 4.13/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.13/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.13/1.02      | ~ v2_pre_topc(sK0) ),
% 4.13/1.02      inference(unflattening,[status(thm)],[c_275]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_278,plain,
% 4.13/1.02      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.13/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 4.13/1.02      | ~ v4_pre_topc(X1,sK0)
% 4.13/1.02      | v2_compts_1(X1,sK0)
% 4.13/1.02      | ~ v2_compts_1(X0,sK0) ),
% 4.13/1.02      inference(global_propositional_subsumption,
% 4.13/1.02                [status(thm)],
% 4.13/1.02                [c_276,c_19]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_279,plain,
% 4.13/1.02      ( ~ v2_compts_1(X0,sK0)
% 4.13/1.02      | v2_compts_1(X1,sK0)
% 4.13/1.02      | ~ v4_pre_topc(X1,sK0)
% 4.13/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 4.13/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.13/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.13/1.02      inference(renaming,[status(thm)],[c_278]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_718,plain,
% 4.13/1.02      ( v2_compts_1(X0,sK0) != iProver_top
% 4.13/1.02      | v2_compts_1(X1,sK0) = iProver_top
% 4.13/1.02      | v4_pre_topc(X1,sK0) != iProver_top
% 4.13/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 4.13/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.13/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_1505,plain,
% 4.13/1.02      ( v2_compts_1(X0,sK0) = iProver_top
% 4.13/1.02      | v2_compts_1(sK1,sK0) != iProver_top
% 4.13/1.02      | v4_pre_topc(X0,sK0) != iProver_top
% 4.13/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.13/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_720,c_718]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_14,negated_conjecture,
% 4.13/1.02      ( v2_compts_1(sK1,sK0) ),
% 4.13/1.02      inference(cnf_transformation,[],[f54]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_25,plain,
% 4.13/1.02      ( v2_compts_1(sK1,sK0) = iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_1567,plain,
% 4.13/1.02      ( v2_compts_1(X0,sK0) = iProver_top
% 4.13/1.02      | v4_pre_topc(X0,sK0) != iProver_top
% 4.13/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.13/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 4.13/1.02      inference(global_propositional_subsumption,
% 4.13/1.02                [status(thm)],
% 4.13/1.02                [c_1505,c_25]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_12201,plain,
% 4.13/1.02      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top
% 4.13/1.02      | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top
% 4.13/1.02      | m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK1)) != iProver_top ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_9292,c_1567]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_12,negated_conjecture,
% 4.13/1.02      ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 4.13/1.02      inference(cnf_transformation,[],[f56]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_724,plain,
% 4.13/1.02      ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_1978,plain,
% 4.13/1.02      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
% 4.13/1.02      inference(demodulation,[status(thm)],[c_1735,c_724]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_1,plain,
% 4.13/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 4.13/1.02      inference(cnf_transformation,[],[f37]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_731,plain,
% 4.13/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_0,plain,
% 4.13/1.02      ( k2_subset_1(X0) = X0 ),
% 4.13/1.02      inference(cnf_transformation,[],[f36]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_732,plain,
% 4.13/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.13/1.02      inference(light_normalisation,[status(thm)],[c_731,c_0]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_1321,plain,
% 4.13/1.02      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_732,c_727]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_2258,plain,
% 4.13/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
% 4.13/1.02      | m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_1321,c_729]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_3838,plain,
% 4.13/1.02      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 4.13/1.02      inference(global_propositional_subsumption,
% 4.13/1.02                [status(thm)],
% 4.13/1.02                [c_2258,c_732]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_9298,plain,
% 4.13/1.02      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK1)) = iProver_top ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_8698,c_3838]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_12385,plain,
% 4.13/1.02      ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
% 4.13/1.02      inference(global_propositional_subsumption,
% 4.13/1.02                [status(thm)],
% 4.13/1.02                [c_12201,c_1978,c_9298]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_12389,plain,
% 4.13/1.02      ( v4_pre_topc(sK1,sK0) != iProver_top
% 4.13/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.13/1.02      inference(superposition,[status(thm)],[c_3245,c_12385]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_766,plain,
% 4.13/1.02      ( ~ v2_compts_1(sK1,sK0)
% 4.13/1.02      | v4_pre_topc(sK1,sK0)
% 4.13/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.13/1.02      inference(instantiation,[status(thm)],[c_218]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(c_767,plain,
% 4.13/1.02      ( v2_compts_1(sK1,sK0) != iProver_top
% 4.13/1.02      | v4_pre_topc(sK1,sK0) = iProver_top
% 4.13/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.13/1.02      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 4.13/1.02  
% 4.13/1.02  cnf(contradiction,plain,
% 4.13/1.02      ( $false ),
% 4.13/1.02      inference(minisat,[status(thm)],[c_12389,c_767,c_25,c_22]) ).
% 4.13/1.02  
% 4.13/1.02  
% 4.13/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 4.13/1.02  
% 4.13/1.02  ------                               Statistics
% 4.13/1.02  
% 4.13/1.02  ------ General
% 4.13/1.02  
% 4.13/1.02  abstr_ref_over_cycles:                  0
% 4.13/1.02  abstr_ref_under_cycles:                 0
% 4.13/1.02  gc_basic_clause_elim:                   0
% 4.13/1.02  forced_gc_time:                         0
% 4.13/1.02  parsing_time:                           0.01
% 4.13/1.02  unif_index_cands_time:                  0.
% 4.13/1.02  unif_index_add_time:                    0.
% 4.13/1.02  orderings_time:                         0.
% 4.13/1.02  out_proof_time:                         0.009
% 4.13/1.02  total_time:                             0.503
% 4.13/1.02  num_of_symbols:                         50
% 4.13/1.02  num_of_terms:                           15863
% 4.13/1.02  
% 4.13/1.02  ------ Preprocessing
% 4.13/1.02  
% 4.13/1.02  num_of_splits:                          0
% 4.13/1.02  num_of_split_atoms:                     0
% 4.13/1.02  num_of_reused_defs:                     0
% 4.13/1.02  num_eq_ax_congr_red:                    30
% 4.13/1.02  num_of_sem_filtered_clauses:            1
% 4.13/1.02  num_of_subtypes:                        0
% 4.13/1.02  monotx_restored_types:                  0
% 4.13/1.02  sat_num_of_epr_types:                   0
% 4.13/1.02  sat_num_of_non_cyclic_types:            0
% 4.13/1.02  sat_guarded_non_collapsed_types:        0
% 4.13/1.02  num_pure_diseq_elim:                    0
% 4.13/1.02  simp_replaced_by:                       0
% 4.13/1.02  res_preprocessed:                       89
% 4.13/1.02  prep_upred:                             0
% 4.13/1.02  prep_unflattend:                        5
% 4.13/1.02  smt_new_axioms:                         0
% 4.13/1.02  pred_elim_cands:                        3
% 4.13/1.02  pred_elim:                              4
% 4.13/1.02  pred_elim_cl:                           4
% 4.13/1.02  pred_elim_cycles:                       6
% 4.13/1.02  merged_defs:                            0
% 4.13/1.02  merged_defs_ncl:                        0
% 4.13/1.02  bin_hyper_res:                          0
% 4.13/1.02  prep_cycles:                            4
% 4.13/1.02  pred_elim_time:                         0.003
% 4.13/1.02  splitting_time:                         0.
% 4.13/1.02  sem_filter_time:                        0.
% 4.13/1.02  monotx_time:                            0.
% 4.13/1.02  subtype_inf_time:                       0.
% 4.13/1.02  
% 4.13/1.02  ------ Problem properties
% 4.13/1.02  
% 4.13/1.02  clauses:                                16
% 4.13/1.02  conjectures:                            5
% 4.13/1.02  epr:                                    2
% 4.13/1.02  horn:                                   16
% 4.13/1.02  ground:                                 5
% 4.13/1.02  unary:                                  7
% 4.13/1.02  binary:                                 5
% 4.13/1.02  lits:                                   34
% 4.13/1.02  lits_eq:                                5
% 4.13/1.02  fd_pure:                                0
% 4.13/1.02  fd_pseudo:                              0
% 4.13/1.02  fd_cond:                                0
% 4.13/1.02  fd_pseudo_cond:                         0
% 4.13/1.02  ac_symbols:                             0
% 4.13/1.02  
% 4.13/1.02  ------ Propositional Solver
% 4.13/1.02  
% 4.13/1.02  prop_solver_calls:                      33
% 4.13/1.02  prop_fast_solver_calls:                 1100
% 4.13/1.02  smt_solver_calls:                       0
% 4.13/1.02  smt_fast_solver_calls:                  0
% 4.13/1.02  prop_num_of_clauses:                    6577
% 4.13/1.02  prop_preprocess_simplified:             10139
% 4.13/1.02  prop_fo_subsumed:                       64
% 4.13/1.02  prop_solver_time:                       0.
% 4.13/1.02  smt_solver_time:                        0.
% 4.13/1.02  smt_fast_solver_time:                   0.
% 4.13/1.02  prop_fast_solver_time:                  0.
% 4.13/1.02  prop_unsat_core_time:                   0.
% 4.13/1.02  
% 4.13/1.02  ------ QBF
% 4.13/1.02  
% 4.13/1.02  qbf_q_res:                              0
% 4.13/1.02  qbf_num_tautologies:                    0
% 4.13/1.02  qbf_prep_cycles:                        0
% 4.13/1.02  
% 4.13/1.02  ------ BMC1
% 4.13/1.02  
% 4.13/1.02  bmc1_current_bound:                     -1
% 4.13/1.02  bmc1_last_solved_bound:                 -1
% 4.13/1.02  bmc1_unsat_core_size:                   -1
% 4.13/1.02  bmc1_unsat_core_parents_size:           -1
% 4.13/1.02  bmc1_merge_next_fun:                    0
% 4.13/1.02  bmc1_unsat_core_clauses_time:           0.
% 4.13/1.02  
% 4.13/1.02  ------ Instantiation
% 4.13/1.02  
% 4.13/1.02  inst_num_of_clauses:                    1819
% 4.13/1.02  inst_num_in_passive:                    416
% 4.13/1.02  inst_num_in_active:                     1002
% 4.13/1.02  inst_num_in_unprocessed:                405
% 4.13/1.02  inst_num_of_loops:                      1080
% 4.13/1.02  inst_num_of_learning_restarts:          0
% 4.13/1.02  inst_num_moves_active_passive:          72
% 4.13/1.02  inst_lit_activity:                      0
% 4.13/1.02  inst_lit_activity_moves:                0
% 4.13/1.02  inst_num_tautologies:                   0
% 4.13/1.02  inst_num_prop_implied:                  0
% 4.13/1.02  inst_num_existing_simplified:           0
% 4.13/1.02  inst_num_eq_res_simplified:             0
% 4.13/1.02  inst_num_child_elim:                    0
% 4.13/1.02  inst_num_of_dismatching_blockings:      481
% 4.13/1.02  inst_num_of_non_proper_insts:           1835
% 4.13/1.02  inst_num_of_duplicates:                 0
% 4.13/1.02  inst_inst_num_from_inst_to_res:         0
% 4.13/1.02  inst_dismatching_checking_time:         0.
% 4.13/1.02  
% 4.13/1.02  ------ Resolution
% 4.13/1.02  
% 4.13/1.02  res_num_of_clauses:                     0
% 4.13/1.02  res_num_in_passive:                     0
% 4.13/1.02  res_num_in_active:                      0
% 4.13/1.02  res_num_of_loops:                       93
% 4.13/1.02  res_forward_subset_subsumed:            267
% 4.13/1.02  res_backward_subset_subsumed:           8
% 4.13/1.02  res_forward_subsumed:                   0
% 4.13/1.02  res_backward_subsumed:                  0
% 4.13/1.02  res_forward_subsumption_resolution:     0
% 4.13/1.02  res_backward_subsumption_resolution:    0
% 4.13/1.02  res_clause_to_clause_subsumption:       2406
% 4.13/1.02  res_orphan_elimination:                 0
% 4.13/1.02  res_tautology_del:                      132
% 4.13/1.02  res_num_eq_res_simplified:              0
% 4.13/1.02  res_num_sel_changes:                    0
% 4.13/1.02  res_moves_from_active_to_pass:          0
% 4.13/1.02  
% 4.13/1.02  ------ Superposition
% 4.13/1.02  
% 4.13/1.02  sup_time_total:                         0.
% 4.13/1.02  sup_time_generating:                    0.
% 4.13/1.02  sup_time_sim_full:                      0.
% 4.13/1.02  sup_time_sim_immed:                     0.
% 4.13/1.02  
% 4.13/1.02  sup_num_of_clauses:                     727
% 4.13/1.02  sup_num_in_active:                      199
% 4.13/1.02  sup_num_in_passive:                     528
% 4.13/1.02  sup_num_of_loops:                       214
% 4.13/1.02  sup_fw_superposition:                   523
% 4.13/1.02  sup_bw_superposition:                   495
% 4.13/1.02  sup_immediate_simplified:               441
% 4.13/1.02  sup_given_eliminated:                   0
% 4.13/1.02  comparisons_done:                       0
% 4.13/1.02  comparisons_avoided:                    0
% 4.13/1.02  
% 4.13/1.02  ------ Simplifications
% 4.13/1.02  
% 4.13/1.02  
% 4.13/1.02  sim_fw_subset_subsumed:                 26
% 4.13/1.02  sim_bw_subset_subsumed:                 55
% 4.13/1.02  sim_fw_subsumed:                        38
% 4.13/1.02  sim_bw_subsumed:                        0
% 4.13/1.02  sim_fw_subsumption_res:                 0
% 4.13/1.02  sim_bw_subsumption_res:                 0
% 4.13/1.02  sim_tautology_del:                      14
% 4.13/1.02  sim_eq_tautology_del:                   104
% 4.13/1.02  sim_eq_res_simp:                        0
% 4.13/1.02  sim_fw_demodulated:                     179
% 4.13/1.02  sim_bw_demodulated:                     7
% 4.13/1.02  sim_light_normalised:                   248
% 4.13/1.02  sim_joinable_taut:                      0
% 4.13/1.02  sim_joinable_simp:                      0
% 4.13/1.02  sim_ac_normalised:                      0
% 4.13/1.02  sim_smt_subsumption:                    0
% 4.13/1.02  
%------------------------------------------------------------------------------
