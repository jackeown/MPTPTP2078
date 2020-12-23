%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:57 EST 2020

% Result     : Theorem 51.56s
% Output     : CNFRefutation 51.56s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 743 expanded)
%              Number of clauses        :  120 ( 244 expanded)
%              Number of leaves         :   21 ( 202 expanded)
%              Depth                    :   22
%              Number of atoms          :  574 (3983 expanded)
%              Number of equality atoms :  194 ( 306 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f40,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f39,f38,f37])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f54,f48])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_839,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_850,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1486,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_850])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_144,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_145,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_144])).

cnf(c_187,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_145])).

cnf(c_833,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_4109,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1486,c_833])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_838,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1487,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_838,c_850])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_185,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_145])).

cnf(c_835,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_189,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_145])).

cnf(c_831,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_9737,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,k3_subset_1(X0,X2))) = k7_subset_1(X0,X1,k3_subset_1(X0,X2))
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_831])).

cnf(c_161862,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) = k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_9737])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_186,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_145])).

cnf(c_834,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_186])).

cnf(c_3927,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1487,c_834])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_188,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_145])).

cnf(c_832,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_5307,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_1487,c_832])).

cnf(c_162121,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X0,sK1))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_161862,c_3927,c_5307])).

cnf(c_196576,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_1486,c_162121])).

cnf(c_196735,plain,
    ( k4_xboole_0(sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_4109,c_196576])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_848,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2513,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK2)) = sK2
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_848])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1057,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_pre_topc(sK0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2849,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2513,c_21,c_19,c_1057])).

cnf(c_9,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_849,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2539,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_849])).

cnf(c_24,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1051,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1052,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1051])).

cnf(c_3084,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2539,c_24,c_26,c_1052])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_852,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_851,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_847,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2675,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | r1_tarski(X2,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_851,c_847])).

cnf(c_7615,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(k4_xboole_0(u1_struct_0(X0),X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_2675])).

cnf(c_7874,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(k4_xboole_0(u1_struct_0(X0),X3),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7615,c_847])).

cnf(c_41958,plain,
    ( m1_pre_topc(sK0,X0) != iProver_top
    | m1_subset_1(k4_xboole_0(u1_struct_0(k1_pre_topc(sK0,sK2)),X1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3084,c_7874])).

cnf(c_42221,plain,
    ( m1_pre_topc(sK0,X0) != iProver_top
    | m1_subset_1(k4_xboole_0(sK2,X1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41958,c_2849])).

cnf(c_42822,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(k4_xboole_0(sK2,X1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_pre_topc(sK0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42221,c_24])).

cnf(c_42823,plain,
    ( m1_pre_topc(sK0,X0) != iProver_top
    | m1_subset_1(k4_xboole_0(sK2,X1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_42822])).

cnf(c_42829,plain,
    ( m1_pre_topc(sK0,k1_pre_topc(sK0,sK2)) != iProver_top
    | m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK2)) = iProver_top
    | l1_pre_topc(k1_pre_topc(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_42823])).

cnf(c_4558,plain,
    ( r1_tarski(k4_xboole_0(sK2,X0),sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4559,plain,
    ( r1_tarski(k4_xboole_0(sK2,X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4558])).

cnf(c_1108,plain,
    ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_18573,plain,
    ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK2))
    | ~ r1_tarski(k4_xboole_0(sK2,X0),sK2) ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_18574,plain,
    ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK2)) = iProver_top
    | r1_tarski(k4_xboole_0(sK2,X0),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18573])).

cnf(c_43172,plain,
    ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42829,c_4559,c_18574])).

cnf(c_197616,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK1)),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_196735,c_43172])).

cnf(c_198858,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_197616])).

cnf(c_201668,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_198858,c_850])).

cnf(c_274,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_261,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4005,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_274,c_261])).

cnf(c_4507,plain,
    ( v2_compts_1(k9_subset_1(X0,X1,X2),X3)
    | ~ v2_compts_1(k1_setfam_1(k2_tarski(X1,X2)),X3)
    | ~ r1_tarski(X2,X0) ),
    inference(resolution,[status(thm)],[c_4005,c_188])).

cnf(c_15,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_52785,plain,
    ( ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_4507,c_15])).

cnf(c_5306,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_1486,c_832])).

cnf(c_843,plain,
    ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5544,plain,
    ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5306,c_843])).

cnf(c_5545,plain,
    ( ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5544])).

cnf(c_52816,plain,
    ( ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_52785,c_5545])).

cnf(c_14,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_5239,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_14,c_7])).

cnf(c_23796,plain,
    ( v2_compts_1(X0,sK0)
    | ~ v2_compts_1(sK2,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_5239,c_19])).

cnf(c_2852,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK2),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK2)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_847])).

cnf(c_9577,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3084,c_2852])).

cnf(c_10896,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9577,c_24])).

cnf(c_10897,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10896])).

cnf(c_10904,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10897,c_850])).

cnf(c_11932,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_851,c_10904])).

cnf(c_844,plain,
    ( v2_compts_1(X0,X1) != iProver_top
    | v2_compts_1(X2,X1) = iProver_top
    | v4_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1348,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_844])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,negated_conjecture,
    ( v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,plain,
    ( v2_compts_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1692,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1348,c_23,c_24,c_29])).

cnf(c_1702,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_851,c_1692])).

cnf(c_11967,plain,
    ( v2_compts_1(X0,sK0) = iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11932,c_1702])).

cnf(c_12044,plain,
    ( v2_compts_1(X0,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ r1_tarski(X0,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11967])).

cnf(c_24087,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | v2_compts_1(X0,sK0)
    | ~ r1_tarski(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23796,c_12044])).

cnf(c_24088,plain,
    ( v2_compts_1(X0,sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ r1_tarski(X0,sK2) ),
    inference(renaming,[status(thm)],[c_24087])).

cnf(c_52828,plain,
    ( ~ v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) ),
    inference(resolution,[status(thm)],[c_52816,c_24088])).

cnf(c_52831,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52828])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1281,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,X0)),sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1649,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_1650,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1649])).

cnf(c_13,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1104,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1105,plain,
    ( v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v8_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1104])).

cnf(c_1101,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | v4_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1102,plain,
    ( v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v8_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1101])).

cnf(c_17,negated_conjecture,
    ( v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,plain,
    ( v8_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_25,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_201668,c_52831,c_1650,c_1105,c_1102,c_29,c_28,c_27,c_26,c_25,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 51.56/6.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.56/6.98  
% 51.56/6.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.56/6.98  
% 51.56/6.98  ------  iProver source info
% 51.56/6.98  
% 51.56/6.98  git: date: 2020-06-30 10:37:57 +0100
% 51.56/6.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.56/6.98  git: non_committed_changes: false
% 51.56/6.98  git: last_make_outside_of_git: false
% 51.56/6.98  
% 51.56/6.98  ------ 
% 51.56/6.98  ------ Parsing...
% 51.56/6.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.56/6.98  
% 51.56/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 51.56/6.98  
% 51.56/6.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.56/6.98  
% 51.56/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.56/6.98  ------ Proving...
% 51.56/6.98  ------ Problem Properties 
% 51.56/6.98  
% 51.56/6.98  
% 51.56/6.98  clauses                                 23
% 51.56/6.98  conjectures                             8
% 51.56/6.98  EPR                                     5
% 51.56/6.98  Horn                                    23
% 51.56/6.98  unary                                   10
% 51.56/6.98  binary                                  6
% 51.56/6.98  lits                                    56
% 51.56/6.98  lits eq                                 6
% 51.56/6.98  fd_pure                                 0
% 51.56/6.98  fd_pseudo                               0
% 51.56/6.98  fd_cond                                 0
% 51.56/6.98  fd_pseudo_cond                          0
% 51.56/6.98  AC symbols                              0
% 51.56/6.98  
% 51.56/6.98  ------ Input Options Time Limit: Unbounded
% 51.56/6.98  
% 51.56/6.98  
% 51.56/6.98  ------ 
% 51.56/6.98  Current options:
% 51.56/6.98  ------ 
% 51.56/6.98  
% 51.56/6.98  
% 51.56/6.98  
% 51.56/6.98  
% 51.56/6.98  ------ Proving...
% 51.56/6.98  
% 51.56/6.98  
% 51.56/6.98  % SZS status Theorem for theBenchmark.p
% 51.56/6.98  
% 51.56/6.98  % SZS output start CNFRefutation for theBenchmark.p
% 51.56/6.98  
% 51.56/6.98  fof(f2,axiom,(
% 51.56/6.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f42,plain,(
% 51.56/6.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 51.56/6.98    inference(cnf_transformation,[],[f2])).
% 51.56/6.98  
% 51.56/6.98  fof(f16,conjecture,(
% 51.56/6.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f17,negated_conjecture,(
% 51.56/6.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 51.56/6.98    inference(negated_conjecture,[],[f16])).
% 51.56/6.98  
% 51.56/6.98  fof(f34,plain,(
% 51.56/6.98    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 51.56/6.98    inference(ennf_transformation,[],[f17])).
% 51.56/6.98  
% 51.56/6.98  fof(f35,plain,(
% 51.56/6.98    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 51.56/6.98    inference(flattening,[],[f34])).
% 51.56/6.98  
% 51.56/6.98  fof(f39,plain,(
% 51.56/6.98    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v2_compts_1(sK2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 51.56/6.98    introduced(choice_axiom,[])).
% 51.56/6.98  
% 51.56/6.98  fof(f38,plain,(
% 51.56/6.98    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(sK1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 51.56/6.98    introduced(choice_axiom,[])).
% 51.56/6.98  
% 51.56/6.98  fof(f37,plain,(
% 51.56/6.98    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 51.56/6.98    introduced(choice_axiom,[])).
% 51.56/6.98  
% 51.56/6.98  fof(f40,plain,(
% 51.56/6.98    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 51.56/6.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f39,f38,f37])).
% 51.56/6.98  
% 51.56/6.98  fof(f60,plain,(
% 51.56/6.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 51.56/6.98    inference(cnf_transformation,[],[f40])).
% 51.56/6.98  
% 51.56/6.98  fof(f9,axiom,(
% 51.56/6.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f36,plain,(
% 51.56/6.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 51.56/6.98    inference(nnf_transformation,[],[f9])).
% 51.56/6.98  
% 51.56/6.98  fof(f49,plain,(
% 51.56/6.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 51.56/6.98    inference(cnf_transformation,[],[f36])).
% 51.56/6.98  
% 51.56/6.98  fof(f5,axiom,(
% 51.56/6.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f21,plain,(
% 51.56/6.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.56/6.98    inference(ennf_transformation,[],[f5])).
% 51.56/6.98  
% 51.56/6.98  fof(f45,plain,(
% 51.56/6.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.56/6.98    inference(cnf_transformation,[],[f21])).
% 51.56/6.98  
% 51.56/6.98  fof(f50,plain,(
% 51.56/6.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 51.56/6.98    inference(cnf_transformation,[],[f36])).
% 51.56/6.98  
% 51.56/6.98  fof(f59,plain,(
% 51.56/6.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 51.56/6.98    inference(cnf_transformation,[],[f40])).
% 51.56/6.98  
% 51.56/6.98  fof(f3,axiom,(
% 51.56/6.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f19,plain,(
% 51.56/6.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.56/6.98    inference(ennf_transformation,[],[f3])).
% 51.56/6.98  
% 51.56/6.98  fof(f43,plain,(
% 51.56/6.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.56/6.98    inference(cnf_transformation,[],[f19])).
% 51.56/6.98  
% 51.56/6.98  fof(f7,axiom,(
% 51.56/6.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f23,plain,(
% 51.56/6.98    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.56/6.98    inference(ennf_transformation,[],[f7])).
% 51.56/6.98  
% 51.56/6.98  fof(f47,plain,(
% 51.56/6.98    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.56/6.98    inference(cnf_transformation,[],[f23])).
% 51.56/6.98  
% 51.56/6.98  fof(f4,axiom,(
% 51.56/6.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f20,plain,(
% 51.56/6.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.56/6.98    inference(ennf_transformation,[],[f4])).
% 51.56/6.98  
% 51.56/6.98  fof(f44,plain,(
% 51.56/6.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.56/6.98    inference(cnf_transformation,[],[f20])).
% 51.56/6.98  
% 51.56/6.98  fof(f6,axiom,(
% 51.56/6.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f22,plain,(
% 51.56/6.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 51.56/6.98    inference(ennf_transformation,[],[f6])).
% 51.56/6.98  
% 51.56/6.98  fof(f46,plain,(
% 51.56/6.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 51.56/6.98    inference(cnf_transformation,[],[f22])).
% 51.56/6.98  
% 51.56/6.98  fof(f8,axiom,(
% 51.56/6.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f48,plain,(
% 51.56/6.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 51.56/6.98    inference(cnf_transformation,[],[f8])).
% 51.56/6.98  
% 51.56/6.98  fof(f65,plain,(
% 51.56/6.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 51.56/6.98    inference(definition_unfolding,[],[f46,f48])).
% 51.56/6.98  
% 51.56/6.98  fof(f11,axiom,(
% 51.56/6.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f26,plain,(
% 51.56/6.98    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 51.56/6.98    inference(ennf_transformation,[],[f11])).
% 51.56/6.98  
% 51.56/6.98  fof(f52,plain,(
% 51.56/6.98    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.56/6.98    inference(cnf_transformation,[],[f26])).
% 51.56/6.98  
% 51.56/6.98  fof(f58,plain,(
% 51.56/6.98    l1_pre_topc(sK0)),
% 51.56/6.98    inference(cnf_transformation,[],[f40])).
% 51.56/6.98  
% 51.56/6.98  fof(f10,axiom,(
% 51.56/6.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f18,plain,(
% 51.56/6.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 51.56/6.98    inference(pure_predicate_removal,[],[f10])).
% 51.56/6.98  
% 51.56/6.98  fof(f24,plain,(
% 51.56/6.98    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 51.56/6.98    inference(ennf_transformation,[],[f18])).
% 51.56/6.98  
% 51.56/6.98  fof(f25,plain,(
% 51.56/6.98    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 51.56/6.98    inference(flattening,[],[f24])).
% 51.56/6.98  
% 51.56/6.98  fof(f51,plain,(
% 51.56/6.98    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.56/6.98    inference(cnf_transformation,[],[f25])).
% 51.56/6.98  
% 51.56/6.98  fof(f1,axiom,(
% 51.56/6.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f41,plain,(
% 51.56/6.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 51.56/6.98    inference(cnf_transformation,[],[f1])).
% 51.56/6.98  
% 51.56/6.98  fof(f12,axiom,(
% 51.56/6.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f27,plain,(
% 51.56/6.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 51.56/6.98    inference(ennf_transformation,[],[f12])).
% 51.56/6.98  
% 51.56/6.98  fof(f53,plain,(
% 51.56/6.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 51.56/6.98    inference(cnf_transformation,[],[f27])).
% 51.56/6.98  
% 51.56/6.98  fof(f64,plain,(
% 51.56/6.98    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 51.56/6.98    inference(cnf_transformation,[],[f40])).
% 51.56/6.98  
% 51.56/6.98  fof(f15,axiom,(
% 51.56/6.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f32,plain,(
% 51.56/6.98    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 51.56/6.98    inference(ennf_transformation,[],[f15])).
% 51.56/6.98  
% 51.56/6.98  fof(f33,plain,(
% 51.56/6.98    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.56/6.98    inference(flattening,[],[f32])).
% 51.56/6.98  
% 51.56/6.98  fof(f56,plain,(
% 51.56/6.98    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.56/6.98    inference(cnf_transformation,[],[f33])).
% 51.56/6.98  
% 51.56/6.98  fof(f57,plain,(
% 51.56/6.98    v2_pre_topc(sK0)),
% 51.56/6.98    inference(cnf_transformation,[],[f40])).
% 51.56/6.98  
% 51.56/6.98  fof(f63,plain,(
% 51.56/6.98    v2_compts_1(sK2,sK0)),
% 51.56/6.98    inference(cnf_transformation,[],[f40])).
% 51.56/6.98  
% 51.56/6.98  fof(f13,axiom,(
% 51.56/6.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k3_xboole_0(X1,X2),X0))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f28,plain,(
% 51.56/6.98    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 51.56/6.98    inference(ennf_transformation,[],[f13])).
% 51.56/6.98  
% 51.56/6.98  fof(f29,plain,(
% 51.56/6.98    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.56/6.98    inference(flattening,[],[f28])).
% 51.56/6.98  
% 51.56/6.98  fof(f54,plain,(
% 51.56/6.98    ( ! [X2,X0,X1] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.56/6.98    inference(cnf_transformation,[],[f29])).
% 51.56/6.98  
% 51.56/6.98  fof(f66,plain,(
% 51.56/6.98    ( ! [X2,X0,X1] : (v4_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.56/6.98    inference(definition_unfolding,[],[f54,f48])).
% 51.56/6.98  
% 51.56/6.98  fof(f14,axiom,(
% 51.56/6.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 51.56/6.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.56/6.98  
% 51.56/6.98  fof(f30,plain,(
% 51.56/6.98    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 51.56/6.98    inference(ennf_transformation,[],[f14])).
% 51.56/6.98  
% 51.56/6.98  fof(f31,plain,(
% 51.56/6.98    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.56/6.98    inference(flattening,[],[f30])).
% 51.56/6.98  
% 51.56/6.98  fof(f55,plain,(
% 51.56/6.98    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.56/6.98    inference(cnf_transformation,[],[f31])).
% 51.56/6.98  
% 51.56/6.98  fof(f62,plain,(
% 51.56/6.98    v2_compts_1(sK1,sK0)),
% 51.56/6.98    inference(cnf_transformation,[],[f40])).
% 51.56/6.98  
% 51.56/6.98  fof(f61,plain,(
% 51.56/6.98    v8_pre_topc(sK0)),
% 51.56/6.98    inference(cnf_transformation,[],[f40])).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1,plain,
% 51.56/6.98      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 51.56/6.98      inference(cnf_transformation,[],[f42]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_19,negated_conjecture,
% 51.56/6.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 51.56/6.98      inference(cnf_transformation,[],[f60]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_839,plain,
% 51.56/6.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_8,plain,
% 51.56/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 51.56/6.98      inference(cnf_transformation,[],[f49]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_850,plain,
% 51.56/6.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 51.56/6.98      | r1_tarski(X0,X1) = iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1486,plain,
% 51.56/6.98      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_839,c_850]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_4,plain,
% 51.56/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.56/6.98      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 51.56/6.98      inference(cnf_transformation,[],[f45]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_7,plain,
% 51.56/6.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 51.56/6.98      inference(cnf_transformation,[],[f50]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_144,plain,
% 51.56/6.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 51.56/6.98      inference(prop_impl,[status(thm)],[c_7]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_145,plain,
% 51.56/6.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 51.56/6.98      inference(renaming,[status(thm)],[c_144]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_187,plain,
% 51.56/6.98      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 51.56/6.98      inference(bin_hyper_res,[status(thm)],[c_4,c_145]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_833,plain,
% 51.56/6.98      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 51.56/6.98      | r1_tarski(X1,X0) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_4109,plain,
% 51.56/6.98      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_1486,c_833]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_20,negated_conjecture,
% 51.56/6.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 51.56/6.98      inference(cnf_transformation,[],[f59]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_838,plain,
% 51.56/6.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1487,plain,
% 51.56/6.98      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_838,c_850]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_2,plain,
% 51.56/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.56/6.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 51.56/6.98      inference(cnf_transformation,[],[f43]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_185,plain,
% 51.56/6.98      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 51.56/6.98      | ~ r1_tarski(X1,X0) ),
% 51.56/6.98      inference(bin_hyper_res,[status(thm)],[c_2,c_145]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_835,plain,
% 51.56/6.98      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 51.56/6.98      | r1_tarski(X1,X0) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_185]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_6,plain,
% 51.56/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.56/6.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 51.56/6.98      | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
% 51.56/6.98      inference(cnf_transformation,[],[f47]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_189,plain,
% 51.56/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.56/6.98      | ~ r1_tarski(X2,X1)
% 51.56/6.98      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 51.56/6.98      inference(bin_hyper_res,[status(thm)],[c_6,c_145]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_831,plain,
% 51.56/6.98      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 51.56/6.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 51.56/6.98      | r1_tarski(X1,X0) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_9737,plain,
% 51.56/6.98      ( k9_subset_1(X0,X1,k3_subset_1(X0,k3_subset_1(X0,X2))) = k7_subset_1(X0,X1,k3_subset_1(X0,X2))
% 51.56/6.98      | r1_tarski(X2,X0) != iProver_top
% 51.56/6.98      | r1_tarski(X1,X0) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_835,c_831]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_161862,plain,
% 51.56/6.98      ( k9_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) = k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1))
% 51.56/6.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_1487,c_9737]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_3,plain,
% 51.56/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.56/6.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 51.56/6.98      inference(cnf_transformation,[],[f44]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_186,plain,
% 51.56/6.98      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 51.56/6.98      inference(bin_hyper_res,[status(thm)],[c_3,c_145]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_834,plain,
% 51.56/6.98      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 51.56/6.98      | r1_tarski(X1,X0) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_186]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_3927,plain,
% 51.56/6.98      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_1487,c_834]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_5,plain,
% 51.56/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.56/6.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 51.56/6.98      inference(cnf_transformation,[],[f65]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_188,plain,
% 51.56/6.98      ( ~ r1_tarski(X0,X1)
% 51.56/6.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 51.56/6.98      inference(bin_hyper_res,[status(thm)],[c_5,c_145]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_832,plain,
% 51.56/6.98      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 51.56/6.98      | r1_tarski(X2,X0) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_188]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_5307,plain,
% 51.56/6.98      ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1)) ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_1487,c_832]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_162121,plain,
% 51.56/6.98      ( k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X0,sK1))
% 51.56/6.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 51.56/6.98      inference(light_normalisation,
% 51.56/6.98                [status(thm)],
% 51.56/6.98                [c_161862,c_3927,c_5307]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_196576,plain,
% 51.56/6.98      ( k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK2,sK1)) ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_1486,c_162121]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_196735,plain,
% 51.56/6.98      ( k4_xboole_0(sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK2,sK1)) ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_4109,c_196576]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_10,plain,
% 51.56/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.56/6.98      | ~ l1_pre_topc(X1)
% 51.56/6.98      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 51.56/6.98      inference(cnf_transformation,[],[f52]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_848,plain,
% 51.56/6.98      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 51.56/6.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 51.56/6.98      | l1_pre_topc(X0) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_2513,plain,
% 51.56/6.98      ( u1_struct_0(k1_pre_topc(sK0,sK2)) = sK2
% 51.56/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_839,c_848]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_21,negated_conjecture,
% 51.56/6.98      ( l1_pre_topc(sK0) ),
% 51.56/6.98      inference(cnf_transformation,[],[f58]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1057,plain,
% 51.56/6.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.56/6.98      | ~ l1_pre_topc(sK0)
% 51.56/6.98      | u1_struct_0(k1_pre_topc(sK0,sK2)) = sK2 ),
% 51.56/6.98      inference(instantiation,[status(thm)],[c_10]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_2849,plain,
% 51.56/6.98      ( u1_struct_0(k1_pre_topc(sK0,sK2)) = sK2 ),
% 51.56/6.98      inference(global_propositional_subsumption,
% 51.56/6.98                [status(thm)],
% 51.56/6.98                [c_2513,c_21,c_19,c_1057]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_9,plain,
% 51.56/6.98      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 51.56/6.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 51.56/6.98      | ~ l1_pre_topc(X0) ),
% 51.56/6.98      inference(cnf_transformation,[],[f51]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_849,plain,
% 51.56/6.98      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 51.56/6.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 51.56/6.98      | l1_pre_topc(X0) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_2539,plain,
% 51.56/6.98      ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) = iProver_top
% 51.56/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_839,c_849]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_24,plain,
% 51.56/6.98      ( l1_pre_topc(sK0) = iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_26,plain,
% 51.56/6.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1051,plain,
% 51.56/6.98      ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0)
% 51.56/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.56/6.98      | ~ l1_pre_topc(sK0) ),
% 51.56/6.98      inference(instantiation,[status(thm)],[c_9]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1052,plain,
% 51.56/6.98      ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) = iProver_top
% 51.56/6.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 51.56/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_1051]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_3084,plain,
% 51.56/6.98      ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) = iProver_top ),
% 51.56/6.98      inference(global_propositional_subsumption,
% 51.56/6.98                [status(thm)],
% 51.56/6.98                [c_2539,c_24,c_26,c_1052]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_0,plain,
% 51.56/6.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 51.56/6.98      inference(cnf_transformation,[],[f41]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_852,plain,
% 51.56/6.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_851,plain,
% 51.56/6.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 51.56/6.98      | r1_tarski(X0,X1) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_11,plain,
% 51.56/6.98      ( ~ m1_pre_topc(X0,X1)
% 51.56/6.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 51.56/6.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 51.56/6.98      | ~ l1_pre_topc(X1) ),
% 51.56/6.98      inference(cnf_transformation,[],[f53]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_847,plain,
% 51.56/6.98      ( m1_pre_topc(X0,X1) != iProver_top
% 51.56/6.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 51.56/6.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 51.56/6.98      | l1_pre_topc(X1) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_2675,plain,
% 51.56/6.98      ( m1_pre_topc(X0,X1) != iProver_top
% 51.56/6.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 51.56/6.98      | r1_tarski(X2,u1_struct_0(X0)) != iProver_top
% 51.56/6.98      | l1_pre_topc(X1) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_851,c_847]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_7615,plain,
% 51.56/6.98      ( m1_pre_topc(X0,X1) != iProver_top
% 51.56/6.98      | m1_subset_1(k4_xboole_0(u1_struct_0(X0),X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 51.56/6.98      | l1_pre_topc(X1) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_852,c_2675]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_7874,plain,
% 51.56/6.98      ( m1_pre_topc(X0,X1) != iProver_top
% 51.56/6.98      | m1_pre_topc(X1,X2) != iProver_top
% 51.56/6.98      | m1_subset_1(k4_xboole_0(u1_struct_0(X0),X3),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 51.56/6.98      | l1_pre_topc(X1) != iProver_top
% 51.56/6.98      | l1_pre_topc(X2) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_7615,c_847]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_41958,plain,
% 51.56/6.98      ( m1_pre_topc(sK0,X0) != iProver_top
% 51.56/6.98      | m1_subset_1(k4_xboole_0(u1_struct_0(k1_pre_topc(sK0,sK2)),X1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 51.56/6.98      | l1_pre_topc(X0) != iProver_top
% 51.56/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_3084,c_7874]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_42221,plain,
% 51.56/6.98      ( m1_pre_topc(sK0,X0) != iProver_top
% 51.56/6.98      | m1_subset_1(k4_xboole_0(sK2,X1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 51.56/6.98      | l1_pre_topc(X0) != iProver_top
% 51.56/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.56/6.98      inference(light_normalisation,[status(thm)],[c_41958,c_2849]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_42822,plain,
% 51.56/6.98      ( l1_pre_topc(X0) != iProver_top
% 51.56/6.98      | m1_subset_1(k4_xboole_0(sK2,X1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 51.56/6.98      | m1_pre_topc(sK0,X0) != iProver_top ),
% 51.56/6.98      inference(global_propositional_subsumption,
% 51.56/6.98                [status(thm)],
% 51.56/6.98                [c_42221,c_24]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_42823,plain,
% 51.56/6.98      ( m1_pre_topc(sK0,X0) != iProver_top
% 51.56/6.98      | m1_subset_1(k4_xboole_0(sK2,X1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 51.56/6.98      | l1_pre_topc(X0) != iProver_top ),
% 51.56/6.98      inference(renaming,[status(thm)],[c_42822]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_42829,plain,
% 51.56/6.98      ( m1_pre_topc(sK0,k1_pre_topc(sK0,sK2)) != iProver_top
% 51.56/6.98      | m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK2)) = iProver_top
% 51.56/6.98      | l1_pre_topc(k1_pre_topc(sK0,sK2)) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_2849,c_42823]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_4558,plain,
% 51.56/6.98      ( r1_tarski(k4_xboole_0(sK2,X0),sK2) ),
% 51.56/6.98      inference(instantiation,[status(thm)],[c_0]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_4559,plain,
% 51.56/6.98      ( r1_tarski(k4_xboole_0(sK2,X0),sK2) = iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_4558]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1108,plain,
% 51.56/6.98      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
% 51.56/6.98      | ~ r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 51.56/6.98      inference(instantiation,[status(thm)],[c_7]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_18573,plain,
% 51.56/6.98      ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK2))
% 51.56/6.98      | ~ r1_tarski(k4_xboole_0(sK2,X0),sK2) ),
% 51.56/6.98      inference(instantiation,[status(thm)],[c_1108]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_18574,plain,
% 51.56/6.98      ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK2)) = iProver_top
% 51.56/6.98      | r1_tarski(k4_xboole_0(sK2,X0),sK2) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_18573]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_43172,plain,
% 51.56/6.98      ( m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(sK2)) = iProver_top ),
% 51.56/6.98      inference(global_propositional_subsumption,
% 51.56/6.98                [status(thm)],
% 51.56/6.98                [c_42829,c_4559,c_18574]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_197616,plain,
% 51.56/6.98      ( m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK1)),k1_zfmisc_1(sK2)) = iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_196735,c_43172]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_198858,plain,
% 51.56/6.98      ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2)) = iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_1,c_197616]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_201668,plain,
% 51.56/6.98      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) = iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_198858,c_850]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_274,plain,
% 51.56/6.98      ( ~ v2_compts_1(X0,X1) | v2_compts_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.56/6.98      theory(equality) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_261,plain,( X0 = X0 ),theory(equality) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_4005,plain,
% 51.56/6.98      ( ~ v2_compts_1(X0,X1) | v2_compts_1(X2,X1) | X2 != X0 ),
% 51.56/6.98      inference(resolution,[status(thm)],[c_274,c_261]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_4507,plain,
% 51.56/6.98      ( v2_compts_1(k9_subset_1(X0,X1,X2),X3)
% 51.56/6.98      | ~ v2_compts_1(k1_setfam_1(k2_tarski(X1,X2)),X3)
% 51.56/6.98      | ~ r1_tarski(X2,X0) ),
% 51.56/6.98      inference(resolution,[status(thm)],[c_4005,c_188]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_15,negated_conjecture,
% 51.56/6.98      ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 51.56/6.98      inference(cnf_transformation,[],[f64]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_52785,plain,
% 51.56/6.98      ( ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
% 51.56/6.98      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 51.56/6.98      inference(resolution,[status(thm)],[c_4507,c_15]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_5306,plain,
% 51.56/6.98      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_1486,c_832]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_843,plain,
% 51.56/6.98      ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_5544,plain,
% 51.56/6.98      ( v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top ),
% 51.56/6.98      inference(demodulation,[status(thm)],[c_5306,c_843]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_5545,plain,
% 51.56/6.98      ( ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
% 51.56/6.98      inference(predicate_to_equality_rev,[status(thm)],[c_5544]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_52816,plain,
% 51.56/6.98      ( ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
% 51.56/6.98      inference(global_propositional_subsumption,
% 51.56/6.98                [status(thm)],
% 51.56/6.98                [c_52785,c_5545]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_14,plain,
% 51.56/6.98      ( ~ v2_compts_1(X0,X1)
% 51.56/6.98      | v2_compts_1(X2,X1)
% 51.56/6.98      | ~ v4_pre_topc(X2,X1)
% 51.56/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.56/6.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 51.56/6.98      | ~ r1_tarski(X2,X0)
% 51.56/6.98      | ~ v2_pre_topc(X1)
% 51.56/6.98      | ~ l1_pre_topc(X1) ),
% 51.56/6.98      inference(cnf_transformation,[],[f56]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_5239,plain,
% 51.56/6.98      ( ~ v2_compts_1(X0,X1)
% 51.56/6.98      | v2_compts_1(X2,X1)
% 51.56/6.98      | ~ v4_pre_topc(X2,X1)
% 51.56/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.56/6.98      | ~ r1_tarski(X2,X0)
% 51.56/6.98      | ~ r1_tarski(X2,u1_struct_0(X1))
% 51.56/6.98      | ~ v2_pre_topc(X1)
% 51.56/6.98      | ~ l1_pre_topc(X1) ),
% 51.56/6.98      inference(resolution,[status(thm)],[c_14,c_7]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_23796,plain,
% 51.56/6.98      ( v2_compts_1(X0,sK0)
% 51.56/6.98      | ~ v2_compts_1(sK2,sK0)
% 51.56/6.98      | ~ v4_pre_topc(X0,sK0)
% 51.56/6.98      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 51.56/6.98      | ~ r1_tarski(X0,sK2)
% 51.56/6.98      | ~ v2_pre_topc(sK0)
% 51.56/6.98      | ~ l1_pre_topc(sK0) ),
% 51.56/6.98      inference(resolution,[status(thm)],[c_5239,c_19]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_2852,plain,
% 51.56/6.98      ( m1_pre_topc(k1_pre_topc(sK0,sK2),X0) != iProver_top
% 51.56/6.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 51.56/6.98      | m1_subset_1(X1,k1_zfmisc_1(sK2)) != iProver_top
% 51.56/6.98      | l1_pre_topc(X0) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_2849,c_847]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_9577,plain,
% 51.56/6.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 51.56/6.98      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 51.56/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_3084,c_2852]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_10896,plain,
% 51.56/6.98      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 51.56/6.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 51.56/6.98      inference(global_propositional_subsumption,
% 51.56/6.98                [status(thm)],
% 51.56/6.98                [c_9577,c_24]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_10897,plain,
% 51.56/6.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 51.56/6.98      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top ),
% 51.56/6.98      inference(renaming,[status(thm)],[c_10896]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_10904,plain,
% 51.56/6.98      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 51.56/6.98      | r1_tarski(X0,u1_struct_0(sK0)) = iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_10897,c_850]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_11932,plain,
% 51.56/6.98      ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 51.56/6.98      | r1_tarski(X0,sK2) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_851,c_10904]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_844,plain,
% 51.56/6.98      ( v2_compts_1(X0,X1) != iProver_top
% 51.56/6.98      | v2_compts_1(X2,X1) = iProver_top
% 51.56/6.98      | v4_pre_topc(X2,X1) != iProver_top
% 51.56/6.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 51.56/6.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 51.56/6.98      | r1_tarski(X2,X0) != iProver_top
% 51.56/6.98      | v2_pre_topc(X1) != iProver_top
% 51.56/6.98      | l1_pre_topc(X1) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1348,plain,
% 51.56/6.98      ( v2_compts_1(X0,sK0) = iProver_top
% 51.56/6.98      | v2_compts_1(sK2,sK0) != iProver_top
% 51.56/6.98      | v4_pre_topc(X0,sK0) != iProver_top
% 51.56/6.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 51.56/6.98      | r1_tarski(X0,sK2) != iProver_top
% 51.56/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.56/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_839,c_844]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_22,negated_conjecture,
% 51.56/6.98      ( v2_pre_topc(sK0) ),
% 51.56/6.98      inference(cnf_transformation,[],[f57]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_23,plain,
% 51.56/6.98      ( v2_pre_topc(sK0) = iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_16,negated_conjecture,
% 51.56/6.98      ( v2_compts_1(sK2,sK0) ),
% 51.56/6.98      inference(cnf_transformation,[],[f63]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_29,plain,
% 51.56/6.98      ( v2_compts_1(sK2,sK0) = iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1692,plain,
% 51.56/6.98      ( v2_compts_1(X0,sK0) = iProver_top
% 51.56/6.98      | v4_pre_topc(X0,sK0) != iProver_top
% 51.56/6.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 51.56/6.98      | r1_tarski(X0,sK2) != iProver_top ),
% 51.56/6.98      inference(global_propositional_subsumption,
% 51.56/6.98                [status(thm)],
% 51.56/6.98                [c_1348,c_23,c_24,c_29]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1702,plain,
% 51.56/6.98      ( v2_compts_1(X0,sK0) = iProver_top
% 51.56/6.98      | v4_pre_topc(X0,sK0) != iProver_top
% 51.56/6.98      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 51.56/6.98      | r1_tarski(X0,sK2) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_851,c_1692]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_11967,plain,
% 51.56/6.98      ( v2_compts_1(X0,sK0) = iProver_top
% 51.56/6.98      | v4_pre_topc(X0,sK0) != iProver_top
% 51.56/6.98      | r1_tarski(X0,sK2) != iProver_top ),
% 51.56/6.98      inference(superposition,[status(thm)],[c_11932,c_1702]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_12044,plain,
% 51.56/6.98      ( v2_compts_1(X0,sK0)
% 51.56/6.98      | ~ v4_pre_topc(X0,sK0)
% 51.56/6.98      | ~ r1_tarski(X0,sK2) ),
% 51.56/6.98      inference(predicate_to_equality_rev,[status(thm)],[c_11967]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_24087,plain,
% 51.56/6.98      ( ~ v4_pre_topc(X0,sK0)
% 51.56/6.98      | v2_compts_1(X0,sK0)
% 51.56/6.98      | ~ r1_tarski(X0,sK2) ),
% 51.56/6.98      inference(global_propositional_subsumption,
% 51.56/6.98                [status(thm)],
% 51.56/6.98                [c_23796,c_12044]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_24088,plain,
% 51.56/6.98      ( v2_compts_1(X0,sK0)
% 51.56/6.98      | ~ v4_pre_topc(X0,sK0)
% 51.56/6.98      | ~ r1_tarski(X0,sK2) ),
% 51.56/6.98      inference(renaming,[status(thm)],[c_24087]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_52828,plain,
% 51.56/6.98      ( ~ v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
% 51.56/6.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) ),
% 51.56/6.98      inference(resolution,[status(thm)],[c_52816,c_24088]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_52831,plain,
% 51.56/6.98      ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) != iProver_top
% 51.56/6.98      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_52828]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_12,plain,
% 51.56/6.98      ( ~ v4_pre_topc(X0,X1)
% 51.56/6.98      | ~ v4_pre_topc(X2,X1)
% 51.56/6.98      | v4_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 51.56/6.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 51.56/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.56/6.98      | ~ v2_pre_topc(X1)
% 51.56/6.98      | ~ l1_pre_topc(X1) ),
% 51.56/6.98      inference(cnf_transformation,[],[f66]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1281,plain,
% 51.56/6.98      ( ~ v4_pre_topc(X0,sK0)
% 51.56/6.98      | v4_pre_topc(k1_setfam_1(k2_tarski(sK1,X0)),sK0)
% 51.56/6.98      | ~ v4_pre_topc(sK1,sK0)
% 51.56/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.56/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.56/6.98      | ~ v2_pre_topc(sK0)
% 51.56/6.98      | ~ l1_pre_topc(sK0) ),
% 51.56/6.98      inference(instantiation,[status(thm)],[c_12]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1649,plain,
% 51.56/6.98      ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
% 51.56/6.98      | ~ v4_pre_topc(sK2,sK0)
% 51.56/6.98      | ~ v4_pre_topc(sK1,sK0)
% 51.56/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.56/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.56/6.98      | ~ v2_pre_topc(sK0)
% 51.56/6.98      | ~ l1_pre_topc(sK0) ),
% 51.56/6.98      inference(instantiation,[status(thm)],[c_1281]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1650,plain,
% 51.56/6.98      ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) = iProver_top
% 51.56/6.98      | v4_pre_topc(sK2,sK0) != iProver_top
% 51.56/6.98      | v4_pre_topc(sK1,sK0) != iProver_top
% 51.56/6.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 51.56/6.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 51.56/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.56/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_1649]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_13,plain,
% 51.56/6.98      ( ~ v2_compts_1(X0,X1)
% 51.56/6.98      | v4_pre_topc(X0,X1)
% 51.56/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.56/6.98      | ~ v8_pre_topc(X1)
% 51.56/6.98      | ~ v2_pre_topc(X1)
% 51.56/6.98      | ~ l1_pre_topc(X1) ),
% 51.56/6.98      inference(cnf_transformation,[],[f55]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1104,plain,
% 51.56/6.98      ( ~ v2_compts_1(sK1,sK0)
% 51.56/6.98      | v4_pre_topc(sK1,sK0)
% 51.56/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.56/6.98      | ~ v8_pre_topc(sK0)
% 51.56/6.98      | ~ v2_pre_topc(sK0)
% 51.56/6.98      | ~ l1_pre_topc(sK0) ),
% 51.56/6.98      inference(instantiation,[status(thm)],[c_13]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1105,plain,
% 51.56/6.98      ( v2_compts_1(sK1,sK0) != iProver_top
% 51.56/6.98      | v4_pre_topc(sK1,sK0) = iProver_top
% 51.56/6.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 51.56/6.98      | v8_pre_topc(sK0) != iProver_top
% 51.56/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.56/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_1104]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1101,plain,
% 51.56/6.98      ( ~ v2_compts_1(sK2,sK0)
% 51.56/6.98      | v4_pre_topc(sK2,sK0)
% 51.56/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.56/6.98      | ~ v8_pre_topc(sK0)
% 51.56/6.98      | ~ v2_pre_topc(sK0)
% 51.56/6.98      | ~ l1_pre_topc(sK0) ),
% 51.56/6.98      inference(instantiation,[status(thm)],[c_13]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_1102,plain,
% 51.56/6.98      ( v2_compts_1(sK2,sK0) != iProver_top
% 51.56/6.98      | v4_pre_topc(sK2,sK0) = iProver_top
% 51.56/6.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 51.56/6.98      | v8_pre_topc(sK0) != iProver_top
% 51.56/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.56/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_1101]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_17,negated_conjecture,
% 51.56/6.98      ( v2_compts_1(sK1,sK0) ),
% 51.56/6.98      inference(cnf_transformation,[],[f62]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_28,plain,
% 51.56/6.98      ( v2_compts_1(sK1,sK0) = iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_18,negated_conjecture,
% 51.56/6.98      ( v8_pre_topc(sK0) ),
% 51.56/6.98      inference(cnf_transformation,[],[f61]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_27,plain,
% 51.56/6.98      ( v8_pre_topc(sK0) = iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(c_25,plain,
% 51.56/6.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 51.56/6.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 51.56/6.98  
% 51.56/6.98  cnf(contradiction,plain,
% 51.56/6.98      ( $false ),
% 51.56/6.98      inference(minisat,
% 51.56/6.98                [status(thm)],
% 51.56/6.98                [c_201668,c_52831,c_1650,c_1105,c_1102,c_29,c_28,c_27,
% 51.56/6.98                 c_26,c_25,c_24,c_23]) ).
% 51.56/6.98  
% 51.56/6.98  
% 51.56/6.98  % SZS output end CNFRefutation for theBenchmark.p
% 51.56/6.98  
% 51.56/6.98  ------                               Statistics
% 51.56/6.98  
% 51.56/6.98  ------ Selected
% 51.56/6.98  
% 51.56/6.98  total_time:                             6.141
% 51.56/6.98  
%------------------------------------------------------------------------------
