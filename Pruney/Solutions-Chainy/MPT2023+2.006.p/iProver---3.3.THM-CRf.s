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
% DateTime   : Thu Dec  3 12:28:46 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 875 expanded)
%              Number of clauses        :   89 ( 206 expanded)
%              Number of leaves         :   20 ( 298 expanded)
%              Depth                    :   18
%              Number of atoms          :  707 (5074 expanded)
%              Number of equality atoms :  110 ( 155 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k3_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k3_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK3)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK3))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK3))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f49,f48,f47,f46])).

fof(f79,plain,(
    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k8_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    ~ m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(definition_unfolding,[],[f81,f65])).

fof(f80,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f68,f65])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1169,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_17,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_22,c_17])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_358,c_29])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_28,c_27])).

cnf(c_1167,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_1545,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1167])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1372,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_1516,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_1517,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1516])).

cnf(c_1909,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1545,c_33,c_34,c_1517])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k8_subset_1(X1,X0,X2) = k1_setfam_1(k2_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1174,plain,
    ( k8_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2230,plain,
    ( k8_subset_1(u1_struct_0(sK2),sK4,X0) = k1_setfam_1(k2_tarski(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_1909,c_1174])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k8_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1175,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k8_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2590,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2230,c_1175])).

cnf(c_9007,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2590,c_33,c_34,c_1517])).

cnf(c_19,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_485,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_486,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_490,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_28,c_27])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_506,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_490,c_15])).

cnf(c_1163,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1173,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2142,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1163,c_1173])).

cnf(c_23,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1171,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6600,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2142,c_1171])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1170,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_18,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_170,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_17])).

cnf(c_171,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_170])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_22,c_171])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_335,c_29])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_28,c_27])).

cnf(c_1166,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_1467,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1166])).

cnf(c_1468,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1166])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2776,plain,
    ( ~ r2_hidden(sK3,X0)
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(X0,sK5)))
    | ~ r2_hidden(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3619,plain,
    ( r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5)))
    | ~ r2_hidden(sK3,sK5)
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2776])).

cnf(c_3620,plain,
    ( r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) = iProver_top
    | r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3619])).

cnf(c_6922,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6600,c_33,c_1467,c_1468,c_3620])).

cnf(c_6923,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6922])).

cnf(c_9020,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9007,c_6923])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_537,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_538,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
    | ~ v3_pre_topc(X1,sK2)
    | ~ v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_28])).

cnf(c_543,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_542])).

cnf(c_3197,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X0,sK5)),sK2)
    | ~ v3_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_7155,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2)
    | ~ v3_pre_topc(sK5,sK2)
    | ~ v3_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3197])).

cnf(c_7156,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) = iProver_top
    | v3_pre_topc(sK5,sK2) != iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7155])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1177,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2874,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1177])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1176,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2284,plain,
    ( r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1176])).

cnf(c_20,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_461,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_462,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_466,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_28,c_27])).

cnf(c_1164,plain,
    ( v3_pre_topc(X0,sK2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_2482,plain,
    ( v3_pre_topc(sK4,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2284,c_1164])).

cnf(c_2283,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1176])).

cnf(c_2427,plain,
    ( v3_pre_topc(sK5,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2283,c_1164])).

cnf(c_1480,plain,
    ( r2_hidden(sK3,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1467,c_33])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1185,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1707,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_1185])).

cnf(c_1513,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_1514,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1513])).

cnf(c_35,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9020,c_7156,c_2874,c_2482,c_2427,c_1707,c_1517,c_1514,c_35,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:12:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.24/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.01  
% 3.24/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/1.01  
% 3.24/1.01  ------  iProver source info
% 3.24/1.01  
% 3.24/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.24/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/1.01  git: non_committed_changes: false
% 3.24/1.01  git: last_make_outside_of_git: false
% 3.24/1.01  
% 3.24/1.01  ------ 
% 3.24/1.01  
% 3.24/1.01  ------ Input Options
% 3.24/1.01  
% 3.24/1.01  --out_options                           all
% 3.24/1.01  --tptp_safe_out                         true
% 3.24/1.01  --problem_path                          ""
% 3.24/1.01  --include_path                          ""
% 3.24/1.01  --clausifier                            res/vclausify_rel
% 3.24/1.01  --clausifier_options                    --mode clausify
% 3.24/1.01  --stdin                                 false
% 3.24/1.01  --stats_out                             all
% 3.24/1.01  
% 3.24/1.01  ------ General Options
% 3.24/1.01  
% 3.24/1.01  --fof                                   false
% 3.24/1.01  --time_out_real                         305.
% 3.24/1.01  --time_out_virtual                      -1.
% 3.24/1.01  --symbol_type_check                     false
% 3.24/1.01  --clausify_out                          false
% 3.24/1.01  --sig_cnt_out                           false
% 3.24/1.01  --trig_cnt_out                          false
% 3.24/1.01  --trig_cnt_out_tolerance                1.
% 3.24/1.01  --trig_cnt_out_sk_spl                   false
% 3.24/1.01  --abstr_cl_out                          false
% 3.24/1.01  
% 3.24/1.01  ------ Global Options
% 3.24/1.01  
% 3.24/1.01  --schedule                              default
% 3.24/1.01  --add_important_lit                     false
% 3.24/1.01  --prop_solver_per_cl                    1000
% 3.24/1.01  --min_unsat_core                        false
% 3.24/1.01  --soft_assumptions                      false
% 3.24/1.01  --soft_lemma_size                       3
% 3.24/1.01  --prop_impl_unit_size                   0
% 3.24/1.01  --prop_impl_unit                        []
% 3.24/1.01  --share_sel_clauses                     true
% 3.24/1.01  --reset_solvers                         false
% 3.24/1.01  --bc_imp_inh                            [conj_cone]
% 3.24/1.01  --conj_cone_tolerance                   3.
% 3.24/1.01  --extra_neg_conj                        none
% 3.24/1.01  --large_theory_mode                     true
% 3.24/1.01  --prolific_symb_bound                   200
% 3.24/1.01  --lt_threshold                          2000
% 3.24/1.01  --clause_weak_htbl                      true
% 3.24/1.01  --gc_record_bc_elim                     false
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing Options
% 3.24/1.01  
% 3.24/1.01  --preprocessing_flag                    true
% 3.24/1.01  --time_out_prep_mult                    0.1
% 3.24/1.01  --splitting_mode                        input
% 3.24/1.01  --splitting_grd                         true
% 3.24/1.01  --splitting_cvd                         false
% 3.24/1.01  --splitting_cvd_svl                     false
% 3.24/1.01  --splitting_nvd                         32
% 3.24/1.01  --sub_typing                            true
% 3.24/1.01  --prep_gs_sim                           true
% 3.24/1.01  --prep_unflatten                        true
% 3.24/1.01  --prep_res_sim                          true
% 3.24/1.01  --prep_upred                            true
% 3.24/1.01  --prep_sem_filter                       exhaustive
% 3.24/1.01  --prep_sem_filter_out                   false
% 3.24/1.01  --pred_elim                             true
% 3.24/1.01  --res_sim_input                         true
% 3.24/1.01  --eq_ax_congr_red                       true
% 3.24/1.01  --pure_diseq_elim                       true
% 3.24/1.01  --brand_transform                       false
% 3.24/1.01  --non_eq_to_eq                          false
% 3.24/1.01  --prep_def_merge                        true
% 3.24/1.01  --prep_def_merge_prop_impl              false
% 3.24/1.01  --prep_def_merge_mbd                    true
% 3.24/1.01  --prep_def_merge_tr_red                 false
% 3.24/1.01  --prep_def_merge_tr_cl                  false
% 3.24/1.01  --smt_preprocessing                     true
% 3.24/1.01  --smt_ac_axioms                         fast
% 3.24/1.01  --preprocessed_out                      false
% 3.24/1.01  --preprocessed_stats                    false
% 3.24/1.01  
% 3.24/1.01  ------ Abstraction refinement Options
% 3.24/1.01  
% 3.24/1.01  --abstr_ref                             []
% 3.24/1.01  --abstr_ref_prep                        false
% 3.24/1.01  --abstr_ref_until_sat                   false
% 3.24/1.01  --abstr_ref_sig_restrict                funpre
% 3.24/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.01  --abstr_ref_under                       []
% 3.24/1.01  
% 3.24/1.01  ------ SAT Options
% 3.24/1.01  
% 3.24/1.01  --sat_mode                              false
% 3.24/1.01  --sat_fm_restart_options                ""
% 3.24/1.01  --sat_gr_def                            false
% 3.24/1.01  --sat_epr_types                         true
% 3.24/1.01  --sat_non_cyclic_types                  false
% 3.24/1.01  --sat_finite_models                     false
% 3.24/1.01  --sat_fm_lemmas                         false
% 3.24/1.01  --sat_fm_prep                           false
% 3.24/1.01  --sat_fm_uc_incr                        true
% 3.24/1.01  --sat_out_model                         small
% 3.24/1.01  --sat_out_clauses                       false
% 3.24/1.01  
% 3.24/1.01  ------ QBF Options
% 3.24/1.01  
% 3.24/1.01  --qbf_mode                              false
% 3.24/1.01  --qbf_elim_univ                         false
% 3.24/1.01  --qbf_dom_inst                          none
% 3.24/1.01  --qbf_dom_pre_inst                      false
% 3.24/1.01  --qbf_sk_in                             false
% 3.24/1.01  --qbf_pred_elim                         true
% 3.24/1.01  --qbf_split                             512
% 3.24/1.01  
% 3.24/1.01  ------ BMC1 Options
% 3.24/1.01  
% 3.24/1.01  --bmc1_incremental                      false
% 3.24/1.01  --bmc1_axioms                           reachable_all
% 3.24/1.01  --bmc1_min_bound                        0
% 3.24/1.01  --bmc1_max_bound                        -1
% 3.24/1.01  --bmc1_max_bound_default                -1
% 3.24/1.01  --bmc1_symbol_reachability              true
% 3.24/1.01  --bmc1_property_lemmas                  false
% 3.24/1.01  --bmc1_k_induction                      false
% 3.24/1.01  --bmc1_non_equiv_states                 false
% 3.24/1.01  --bmc1_deadlock                         false
% 3.24/1.01  --bmc1_ucm                              false
% 3.24/1.01  --bmc1_add_unsat_core                   none
% 3.24/1.01  --bmc1_unsat_core_children              false
% 3.24/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.01  --bmc1_out_stat                         full
% 3.24/1.01  --bmc1_ground_init                      false
% 3.24/1.01  --bmc1_pre_inst_next_state              false
% 3.24/1.01  --bmc1_pre_inst_state                   false
% 3.24/1.01  --bmc1_pre_inst_reach_state             false
% 3.24/1.01  --bmc1_out_unsat_core                   false
% 3.24/1.01  --bmc1_aig_witness_out                  false
% 3.24/1.01  --bmc1_verbose                          false
% 3.24/1.01  --bmc1_dump_clauses_tptp                false
% 3.24/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.01  --bmc1_dump_file                        -
% 3.24/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.01  --bmc1_ucm_extend_mode                  1
% 3.24/1.01  --bmc1_ucm_init_mode                    2
% 3.24/1.01  --bmc1_ucm_cone_mode                    none
% 3.24/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.01  --bmc1_ucm_relax_model                  4
% 3.24/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.01  --bmc1_ucm_layered_model                none
% 3.24/1.01  --bmc1_ucm_max_lemma_size               10
% 3.24/1.01  
% 3.24/1.01  ------ AIG Options
% 3.24/1.01  
% 3.24/1.01  --aig_mode                              false
% 3.24/1.01  
% 3.24/1.01  ------ Instantiation Options
% 3.24/1.01  
% 3.24/1.01  --instantiation_flag                    true
% 3.24/1.01  --inst_sos_flag                         false
% 3.24/1.01  --inst_sos_phase                        true
% 3.24/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.01  --inst_lit_sel_side                     num_symb
% 3.24/1.01  --inst_solver_per_active                1400
% 3.24/1.01  --inst_solver_calls_frac                1.
% 3.24/1.01  --inst_passive_queue_type               priority_queues
% 3.24/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.01  --inst_passive_queues_freq              [25;2]
% 3.24/1.01  --inst_dismatching                      true
% 3.24/1.01  --inst_eager_unprocessed_to_passive     true
% 3.24/1.01  --inst_prop_sim_given                   true
% 3.24/1.01  --inst_prop_sim_new                     false
% 3.24/1.01  --inst_subs_new                         false
% 3.24/1.01  --inst_eq_res_simp                      false
% 3.24/1.01  --inst_subs_given                       false
% 3.24/1.01  --inst_orphan_elimination               true
% 3.24/1.01  --inst_learning_loop_flag               true
% 3.24/1.01  --inst_learning_start                   3000
% 3.24/1.01  --inst_learning_factor                  2
% 3.24/1.01  --inst_start_prop_sim_after_learn       3
% 3.24/1.01  --inst_sel_renew                        solver
% 3.24/1.01  --inst_lit_activity_flag                true
% 3.24/1.01  --inst_restr_to_given                   false
% 3.24/1.01  --inst_activity_threshold               500
% 3.24/1.01  --inst_out_proof                        true
% 3.24/1.01  
% 3.24/1.01  ------ Resolution Options
% 3.24/1.01  
% 3.24/1.01  --resolution_flag                       true
% 3.24/1.01  --res_lit_sel                           adaptive
% 3.24/1.01  --res_lit_sel_side                      none
% 3.24/1.01  --res_ordering                          kbo
% 3.24/1.01  --res_to_prop_solver                    active
% 3.24/1.01  --res_prop_simpl_new                    false
% 3.24/1.01  --res_prop_simpl_given                  true
% 3.24/1.01  --res_passive_queue_type                priority_queues
% 3.24/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.01  --res_passive_queues_freq               [15;5]
% 3.24/1.01  --res_forward_subs                      full
% 3.24/1.01  --res_backward_subs                     full
% 3.24/1.01  --res_forward_subs_resolution           true
% 3.24/1.01  --res_backward_subs_resolution          true
% 3.24/1.01  --res_orphan_elimination                true
% 3.24/1.01  --res_time_limit                        2.
% 3.24/1.01  --res_out_proof                         true
% 3.24/1.01  
% 3.24/1.01  ------ Superposition Options
% 3.24/1.01  
% 3.24/1.01  --superposition_flag                    true
% 3.24/1.01  --sup_passive_queue_type                priority_queues
% 3.24/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.24/1.01  --demod_completeness_check              fast
% 3.24/1.01  --demod_use_ground                      true
% 3.24/1.01  --sup_to_prop_solver                    passive
% 3.24/1.01  --sup_prop_simpl_new                    true
% 3.24/1.01  --sup_prop_simpl_given                  true
% 3.24/1.01  --sup_fun_splitting                     false
% 3.24/1.01  --sup_smt_interval                      50000
% 3.24/1.01  
% 3.24/1.01  ------ Superposition Simplification Setup
% 3.24/1.01  
% 3.24/1.01  --sup_indices_passive                   []
% 3.24/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.01  --sup_full_bw                           [BwDemod]
% 3.24/1.01  --sup_immed_triv                        [TrivRules]
% 3.24/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.01  --sup_immed_bw_main                     []
% 3.24/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.01  
% 3.24/1.01  ------ Combination Options
% 3.24/1.01  
% 3.24/1.01  --comb_res_mult                         3
% 3.24/1.01  --comb_sup_mult                         2
% 3.24/1.01  --comb_inst_mult                        10
% 3.24/1.01  
% 3.24/1.01  ------ Debug Options
% 3.24/1.01  
% 3.24/1.01  --dbg_backtrace                         false
% 3.24/1.01  --dbg_dump_prop_clauses                 false
% 3.24/1.01  --dbg_dump_prop_clauses_file            -
% 3.24/1.01  --dbg_out_stat                          false
% 3.24/1.01  ------ Parsing...
% 3.24/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/1.01  ------ Proving...
% 3.24/1.01  ------ Problem Properties 
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  clauses                                 25
% 3.24/1.01  conjectures                             4
% 3.24/1.01  EPR                                     5
% 3.24/1.01  Horn                                    21
% 3.24/1.01  unary                                   4
% 3.24/1.01  binary                                  7
% 3.24/1.01  lits                                    66
% 3.24/1.01  lits eq                                 4
% 3.24/1.01  fd_pure                                 0
% 3.24/1.01  fd_pseudo                               0
% 3.24/1.01  fd_cond                                 0
% 3.24/1.01  fd_pseudo_cond                          3
% 3.24/1.01  AC symbols                              0
% 3.24/1.01  
% 3.24/1.01  ------ Schedule dynamic 5 is on 
% 3.24/1.01  
% 3.24/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  ------ 
% 3.24/1.01  Current options:
% 3.24/1.01  ------ 
% 3.24/1.01  
% 3.24/1.01  ------ Input Options
% 3.24/1.01  
% 3.24/1.01  --out_options                           all
% 3.24/1.01  --tptp_safe_out                         true
% 3.24/1.01  --problem_path                          ""
% 3.24/1.01  --include_path                          ""
% 3.24/1.01  --clausifier                            res/vclausify_rel
% 3.24/1.01  --clausifier_options                    --mode clausify
% 3.24/1.01  --stdin                                 false
% 3.24/1.01  --stats_out                             all
% 3.24/1.01  
% 3.24/1.01  ------ General Options
% 3.24/1.01  
% 3.24/1.01  --fof                                   false
% 3.24/1.01  --time_out_real                         305.
% 3.24/1.01  --time_out_virtual                      -1.
% 3.24/1.01  --symbol_type_check                     false
% 3.24/1.01  --clausify_out                          false
% 3.24/1.01  --sig_cnt_out                           false
% 3.24/1.01  --trig_cnt_out                          false
% 3.24/1.01  --trig_cnt_out_tolerance                1.
% 3.24/1.01  --trig_cnt_out_sk_spl                   false
% 3.24/1.01  --abstr_cl_out                          false
% 3.24/1.01  
% 3.24/1.01  ------ Global Options
% 3.24/1.01  
% 3.24/1.01  --schedule                              default
% 3.24/1.01  --add_important_lit                     false
% 3.24/1.01  --prop_solver_per_cl                    1000
% 3.24/1.01  --min_unsat_core                        false
% 3.24/1.01  --soft_assumptions                      false
% 3.24/1.01  --soft_lemma_size                       3
% 3.24/1.01  --prop_impl_unit_size                   0
% 3.24/1.01  --prop_impl_unit                        []
% 3.24/1.01  --share_sel_clauses                     true
% 3.24/1.01  --reset_solvers                         false
% 3.24/1.01  --bc_imp_inh                            [conj_cone]
% 3.24/1.01  --conj_cone_tolerance                   3.
% 3.24/1.01  --extra_neg_conj                        none
% 3.24/1.01  --large_theory_mode                     true
% 3.24/1.01  --prolific_symb_bound                   200
% 3.24/1.01  --lt_threshold                          2000
% 3.24/1.01  --clause_weak_htbl                      true
% 3.24/1.01  --gc_record_bc_elim                     false
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing Options
% 3.24/1.01  
% 3.24/1.01  --preprocessing_flag                    true
% 3.24/1.01  --time_out_prep_mult                    0.1
% 3.24/1.01  --splitting_mode                        input
% 3.24/1.01  --splitting_grd                         true
% 3.24/1.01  --splitting_cvd                         false
% 3.24/1.01  --splitting_cvd_svl                     false
% 3.24/1.01  --splitting_nvd                         32
% 3.24/1.01  --sub_typing                            true
% 3.24/1.01  --prep_gs_sim                           true
% 3.24/1.01  --prep_unflatten                        true
% 3.24/1.01  --prep_res_sim                          true
% 3.24/1.01  --prep_upred                            true
% 3.24/1.01  --prep_sem_filter                       exhaustive
% 3.24/1.01  --prep_sem_filter_out                   false
% 3.24/1.01  --pred_elim                             true
% 3.24/1.01  --res_sim_input                         true
% 3.24/1.01  --eq_ax_congr_red                       true
% 3.24/1.01  --pure_diseq_elim                       true
% 3.24/1.01  --brand_transform                       false
% 3.24/1.01  --non_eq_to_eq                          false
% 3.24/1.01  --prep_def_merge                        true
% 3.24/1.01  --prep_def_merge_prop_impl              false
% 3.24/1.01  --prep_def_merge_mbd                    true
% 3.24/1.01  --prep_def_merge_tr_red                 false
% 3.24/1.01  --prep_def_merge_tr_cl                  false
% 3.24/1.01  --smt_preprocessing                     true
% 3.24/1.01  --smt_ac_axioms                         fast
% 3.24/1.01  --preprocessed_out                      false
% 3.24/1.01  --preprocessed_stats                    false
% 3.24/1.01  
% 3.24/1.01  ------ Abstraction refinement Options
% 3.24/1.01  
% 3.24/1.01  --abstr_ref                             []
% 3.24/1.01  --abstr_ref_prep                        false
% 3.24/1.01  --abstr_ref_until_sat                   false
% 3.24/1.01  --abstr_ref_sig_restrict                funpre
% 3.24/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.01  --abstr_ref_under                       []
% 3.24/1.01  
% 3.24/1.01  ------ SAT Options
% 3.24/1.01  
% 3.24/1.01  --sat_mode                              false
% 3.24/1.01  --sat_fm_restart_options                ""
% 3.24/1.01  --sat_gr_def                            false
% 3.24/1.01  --sat_epr_types                         true
% 3.24/1.01  --sat_non_cyclic_types                  false
% 3.24/1.01  --sat_finite_models                     false
% 3.24/1.01  --sat_fm_lemmas                         false
% 3.24/1.01  --sat_fm_prep                           false
% 3.24/1.01  --sat_fm_uc_incr                        true
% 3.24/1.01  --sat_out_model                         small
% 3.24/1.01  --sat_out_clauses                       false
% 3.24/1.01  
% 3.24/1.01  ------ QBF Options
% 3.24/1.01  
% 3.24/1.01  --qbf_mode                              false
% 3.24/1.01  --qbf_elim_univ                         false
% 3.24/1.01  --qbf_dom_inst                          none
% 3.24/1.01  --qbf_dom_pre_inst                      false
% 3.24/1.01  --qbf_sk_in                             false
% 3.24/1.01  --qbf_pred_elim                         true
% 3.24/1.01  --qbf_split                             512
% 3.24/1.01  
% 3.24/1.01  ------ BMC1 Options
% 3.24/1.01  
% 3.24/1.01  --bmc1_incremental                      false
% 3.24/1.01  --bmc1_axioms                           reachable_all
% 3.24/1.01  --bmc1_min_bound                        0
% 3.24/1.01  --bmc1_max_bound                        -1
% 3.24/1.01  --bmc1_max_bound_default                -1
% 3.24/1.01  --bmc1_symbol_reachability              true
% 3.24/1.01  --bmc1_property_lemmas                  false
% 3.24/1.01  --bmc1_k_induction                      false
% 3.24/1.01  --bmc1_non_equiv_states                 false
% 3.24/1.01  --bmc1_deadlock                         false
% 3.24/1.01  --bmc1_ucm                              false
% 3.24/1.01  --bmc1_add_unsat_core                   none
% 3.24/1.01  --bmc1_unsat_core_children              false
% 3.24/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.01  --bmc1_out_stat                         full
% 3.24/1.01  --bmc1_ground_init                      false
% 3.24/1.01  --bmc1_pre_inst_next_state              false
% 3.24/1.01  --bmc1_pre_inst_state                   false
% 3.24/1.01  --bmc1_pre_inst_reach_state             false
% 3.24/1.01  --bmc1_out_unsat_core                   false
% 3.24/1.01  --bmc1_aig_witness_out                  false
% 3.24/1.01  --bmc1_verbose                          false
% 3.24/1.01  --bmc1_dump_clauses_tptp                false
% 3.24/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.01  --bmc1_dump_file                        -
% 3.24/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.01  --bmc1_ucm_extend_mode                  1
% 3.24/1.01  --bmc1_ucm_init_mode                    2
% 3.24/1.01  --bmc1_ucm_cone_mode                    none
% 3.24/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.01  --bmc1_ucm_relax_model                  4
% 3.24/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.01  --bmc1_ucm_layered_model                none
% 3.24/1.01  --bmc1_ucm_max_lemma_size               10
% 3.24/1.01  
% 3.24/1.01  ------ AIG Options
% 3.24/1.01  
% 3.24/1.01  --aig_mode                              false
% 3.24/1.01  
% 3.24/1.01  ------ Instantiation Options
% 3.24/1.01  
% 3.24/1.01  --instantiation_flag                    true
% 3.24/1.01  --inst_sos_flag                         false
% 3.24/1.01  --inst_sos_phase                        true
% 3.24/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.01  --inst_lit_sel_side                     none
% 3.24/1.01  --inst_solver_per_active                1400
% 3.24/1.01  --inst_solver_calls_frac                1.
% 3.24/1.01  --inst_passive_queue_type               priority_queues
% 3.24/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.01  --inst_passive_queues_freq              [25;2]
% 3.24/1.01  --inst_dismatching                      true
% 3.24/1.01  --inst_eager_unprocessed_to_passive     true
% 3.24/1.01  --inst_prop_sim_given                   true
% 3.24/1.01  --inst_prop_sim_new                     false
% 3.24/1.01  --inst_subs_new                         false
% 3.24/1.01  --inst_eq_res_simp                      false
% 3.24/1.01  --inst_subs_given                       false
% 3.24/1.01  --inst_orphan_elimination               true
% 3.24/1.01  --inst_learning_loop_flag               true
% 3.24/1.01  --inst_learning_start                   3000
% 3.24/1.01  --inst_learning_factor                  2
% 3.24/1.01  --inst_start_prop_sim_after_learn       3
% 3.24/1.01  --inst_sel_renew                        solver
% 3.24/1.01  --inst_lit_activity_flag                true
% 3.24/1.01  --inst_restr_to_given                   false
% 3.24/1.01  --inst_activity_threshold               500
% 3.24/1.01  --inst_out_proof                        true
% 3.24/1.01  
% 3.24/1.01  ------ Resolution Options
% 3.24/1.01  
% 3.24/1.01  --resolution_flag                       false
% 3.24/1.01  --res_lit_sel                           adaptive
% 3.24/1.01  --res_lit_sel_side                      none
% 3.24/1.01  --res_ordering                          kbo
% 3.24/1.01  --res_to_prop_solver                    active
% 3.24/1.01  --res_prop_simpl_new                    false
% 3.24/1.01  --res_prop_simpl_given                  true
% 3.24/1.01  --res_passive_queue_type                priority_queues
% 3.24/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.01  --res_passive_queues_freq               [15;5]
% 3.24/1.01  --res_forward_subs                      full
% 3.24/1.01  --res_backward_subs                     full
% 3.24/1.01  --res_forward_subs_resolution           true
% 3.24/1.01  --res_backward_subs_resolution          true
% 3.24/1.01  --res_orphan_elimination                true
% 3.24/1.01  --res_time_limit                        2.
% 3.24/1.01  --res_out_proof                         true
% 3.24/1.01  
% 3.24/1.01  ------ Superposition Options
% 3.24/1.01  
% 3.24/1.01  --superposition_flag                    true
% 3.24/1.01  --sup_passive_queue_type                priority_queues
% 3.24/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.24/1.01  --demod_completeness_check              fast
% 3.24/1.01  --demod_use_ground                      true
% 3.24/1.01  --sup_to_prop_solver                    passive
% 3.24/1.01  --sup_prop_simpl_new                    true
% 3.24/1.01  --sup_prop_simpl_given                  true
% 3.24/1.01  --sup_fun_splitting                     false
% 3.24/1.01  --sup_smt_interval                      50000
% 3.24/1.01  
% 3.24/1.01  ------ Superposition Simplification Setup
% 3.24/1.01  
% 3.24/1.01  --sup_indices_passive                   []
% 3.24/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.01  --sup_full_bw                           [BwDemod]
% 3.24/1.01  --sup_immed_triv                        [TrivRules]
% 3.24/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.01  --sup_immed_bw_main                     []
% 3.24/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.01  
% 3.24/1.01  ------ Combination Options
% 3.24/1.01  
% 3.24/1.01  --comb_res_mult                         3
% 3.24/1.01  --comb_sup_mult                         2
% 3.24/1.01  --comb_inst_mult                        10
% 3.24/1.01  
% 3.24/1.01  ------ Debug Options
% 3.24/1.01  
% 3.24/1.01  --dbg_backtrace                         false
% 3.24/1.01  --dbg_dump_prop_clauses                 false
% 3.24/1.01  --dbg_dump_prop_clauses_file            -
% 3.24/1.01  --dbg_out_stat                          false
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  ------ Proving...
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  % SZS status Theorem for theBenchmark.p
% 3.24/1.01  
% 3.24/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/1.01  
% 3.24/1.01  fof(f14,conjecture,(
% 3.24/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f15,negated_conjecture,(
% 3.24/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.24/1.01    inference(negated_conjecture,[],[f14])).
% 3.24/1.01  
% 3.24/1.01  fof(f32,plain,(
% 3.24/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.24/1.01    inference(ennf_transformation,[],[f15])).
% 3.24/1.01  
% 3.24/1.01  fof(f33,plain,(
% 3.24/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.24/1.01    inference(flattening,[],[f32])).
% 3.24/1.01  
% 3.24/1.01  fof(f49,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k3_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.24/1.01    introduced(choice_axiom,[])).
% 3.24/1.01  
% 3.24/1.01  fof(f48,plain,(
% 3.24/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.24/1.01    introduced(choice_axiom,[])).
% 3.24/1.01  
% 3.24/1.01  fof(f47,plain,(
% 3.24/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.24/1.01    introduced(choice_axiom,[])).
% 3.24/1.01  
% 3.24/1.01  fof(f46,plain,(
% 3.24/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.24/1.01    introduced(choice_axiom,[])).
% 3.24/1.01  
% 3.24/1.01  fof(f50,plain,(
% 3.24/1.01    (((~m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.24/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f49,f48,f47,f46])).
% 3.24/1.01  
% 3.24/1.01  fof(f79,plain,(
% 3.24/1.01    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.24/1.01    inference(cnf_transformation,[],[f50])).
% 3.24/1.01  
% 3.24/1.01  fof(f13,axiom,(
% 3.24/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f30,plain,(
% 3.24/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.24/1.01    inference(ennf_transformation,[],[f13])).
% 3.24/1.01  
% 3.24/1.01  fof(f31,plain,(
% 3.24/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.24/1.01    inference(flattening,[],[f30])).
% 3.24/1.01  
% 3.24/1.01  fof(f74,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f31])).
% 3.24/1.01  
% 3.24/1.01  fof(f10,axiom,(
% 3.24/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f24,plain,(
% 3.24/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.24/1.01    inference(ennf_transformation,[],[f10])).
% 3.24/1.01  
% 3.24/1.01  fof(f25,plain,(
% 3.24/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.24/1.01    inference(flattening,[],[f24])).
% 3.24/1.01  
% 3.24/1.01  fof(f69,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f25])).
% 3.24/1.01  
% 3.24/1.01  fof(f75,plain,(
% 3.24/1.01    ~v2_struct_0(sK2)),
% 3.24/1.01    inference(cnf_transformation,[],[f50])).
% 3.24/1.01  
% 3.24/1.01  fof(f76,plain,(
% 3.24/1.01    v2_pre_topc(sK2)),
% 3.24/1.01    inference(cnf_transformation,[],[f50])).
% 3.24/1.01  
% 3.24/1.01  fof(f77,plain,(
% 3.24/1.01    l1_pre_topc(sK2)),
% 3.24/1.01    inference(cnf_transformation,[],[f50])).
% 3.24/1.01  
% 3.24/1.01  fof(f78,plain,(
% 3.24/1.01    m1_subset_1(sK3,u1_struct_0(sK2))),
% 3.24/1.01    inference(cnf_transformation,[],[f50])).
% 3.24/1.01  
% 3.24/1.01  fof(f5,axiom,(
% 3.24/1.01    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f18,plain,(
% 3.24/1.01    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.24/1.01    inference(ennf_transformation,[],[f5])).
% 3.24/1.01  
% 3.24/1.01  fof(f64,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.24/1.01    inference(cnf_transformation,[],[f18])).
% 3.24/1.01  
% 3.24/1.01  fof(f6,axiom,(
% 3.24/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f65,plain,(
% 3.24/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.24/1.01    inference(cnf_transformation,[],[f6])).
% 3.24/1.01  
% 3.24/1.01  fof(f88,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (k8_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.24/1.01    inference(definition_unfolding,[],[f64,f65])).
% 3.24/1.01  
% 3.24/1.01  fof(f4,axiom,(
% 3.24/1.01    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f17,plain,(
% 3.24/1.01    ! [X0,X1,X2] : (m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.24/1.01    inference(ennf_transformation,[],[f4])).
% 3.24/1.01  
% 3.24/1.01  fof(f63,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.24/1.01    inference(cnf_transformation,[],[f17])).
% 3.24/1.01  
% 3.24/1.01  fof(f12,axiom,(
% 3.24/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f28,plain,(
% 3.24/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.24/1.01    inference(ennf_transformation,[],[f12])).
% 3.24/1.01  
% 3.24/1.01  fof(f29,plain,(
% 3.24/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.24/1.01    inference(flattening,[],[f28])).
% 3.24/1.01  
% 3.24/1.01  fof(f44,plain,(
% 3.24/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.24/1.01    inference(nnf_transformation,[],[f29])).
% 3.24/1.01  
% 3.24/1.01  fof(f45,plain,(
% 3.24/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.24/1.01    inference(flattening,[],[f44])).
% 3.24/1.01  
% 3.24/1.01  fof(f73,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f45])).
% 3.24/1.01  
% 3.24/1.01  fof(f8,axiom,(
% 3.24/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f20,plain,(
% 3.24/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.24/1.01    inference(ennf_transformation,[],[f8])).
% 3.24/1.01  
% 3.24/1.01  fof(f21,plain,(
% 3.24/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.24/1.01    inference(flattening,[],[f20])).
% 3.24/1.01  
% 3.24/1.01  fof(f67,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f21])).
% 3.24/1.01  
% 3.24/1.01  fof(f7,axiom,(
% 3.24/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f19,plain,(
% 3.24/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.24/1.01    inference(ennf_transformation,[],[f7])).
% 3.24/1.01  
% 3.24/1.01  fof(f66,plain,(
% 3.24/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f19])).
% 3.24/1.01  
% 3.24/1.01  fof(f81,plain,(
% 3.24/1.01    ~m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.24/1.01    inference(cnf_transformation,[],[f50])).
% 3.24/1.01  
% 3.24/1.01  fof(f90,plain,(
% 3.24/1.01    ~m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.24/1.01    inference(definition_unfolding,[],[f81,f65])).
% 3.24/1.01  
% 3.24/1.01  fof(f80,plain,(
% 3.24/1.01    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.24/1.01    inference(cnf_transformation,[],[f50])).
% 3.24/1.01  
% 3.24/1.01  fof(f11,axiom,(
% 3.24/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f26,plain,(
% 3.24/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.24/1.01    inference(ennf_transformation,[],[f11])).
% 3.24/1.01  
% 3.24/1.01  fof(f27,plain,(
% 3.24/1.01    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.24/1.01    inference(flattening,[],[f26])).
% 3.24/1.01  
% 3.24/1.01  fof(f70,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f27])).
% 3.24/1.01  
% 3.24/1.01  fof(f2,axiom,(
% 3.24/1.01    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f38,plain,(
% 3.24/1.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.24/1.01    inference(nnf_transformation,[],[f2])).
% 3.24/1.01  
% 3.24/1.01  fof(f39,plain,(
% 3.24/1.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.24/1.01    inference(flattening,[],[f38])).
% 3.24/1.01  
% 3.24/1.01  fof(f40,plain,(
% 3.24/1.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.24/1.01    inference(rectify,[],[f39])).
% 3.24/1.01  
% 3.24/1.01  fof(f41,plain,(
% 3.24/1.01    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.24/1.01    introduced(choice_axiom,[])).
% 3.24/1.01  
% 3.24/1.01  fof(f42,plain,(
% 3.24/1.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.24/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 3.24/1.01  
% 3.24/1.01  fof(f55,plain,(
% 3.24/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.24/1.01    inference(cnf_transformation,[],[f42])).
% 3.24/1.01  
% 3.24/1.01  fof(f85,plain,(
% 3.24/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 3.24/1.01    inference(definition_unfolding,[],[f55,f65])).
% 3.24/1.01  
% 3.24/1.01  fof(f91,plain,(
% 3.24/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.24/1.01    inference(equality_resolution,[],[f85])).
% 3.24/1.01  
% 3.24/1.01  fof(f9,axiom,(
% 3.24/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f22,plain,(
% 3.24/1.01    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.24/1.01    inference(ennf_transformation,[],[f9])).
% 3.24/1.01  
% 3.24/1.01  fof(f23,plain,(
% 3.24/1.01    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.24/1.01    inference(flattening,[],[f22])).
% 3.24/1.01  
% 3.24/1.01  fof(f68,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f23])).
% 3.24/1.01  
% 3.24/1.01  fof(f89,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.24/1.01    inference(definition_unfolding,[],[f68,f65])).
% 3.24/1.01  
% 3.24/1.01  fof(f3,axiom,(
% 3.24/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f16,plain,(
% 3.24/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.24/1.01    inference(ennf_transformation,[],[f3])).
% 3.24/1.01  
% 3.24/1.01  fof(f43,plain,(
% 3.24/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.24/1.01    inference(nnf_transformation,[],[f16])).
% 3.24/1.01  
% 3.24/1.01  fof(f61,plain,(
% 3.24/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f43])).
% 3.24/1.01  
% 3.24/1.01  fof(f59,plain,(
% 3.24/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f43])).
% 3.24/1.01  
% 3.24/1.01  fof(f72,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f45])).
% 3.24/1.01  
% 3.24/1.01  fof(f1,axiom,(
% 3.24/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f34,plain,(
% 3.24/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.24/1.01    inference(nnf_transformation,[],[f1])).
% 3.24/1.01  
% 3.24/1.01  fof(f35,plain,(
% 3.24/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.24/1.01    inference(rectify,[],[f34])).
% 3.24/1.01  
% 3.24/1.01  fof(f36,plain,(
% 3.24/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.24/1.01    introduced(choice_axiom,[])).
% 3.24/1.01  
% 3.24/1.01  fof(f37,plain,(
% 3.24/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.24/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 3.24/1.01  
% 3.24/1.01  fof(f51,plain,(
% 3.24/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f37])).
% 3.24/1.01  
% 3.24/1.01  cnf(c_25,negated_conjecture,
% 3.24/1.01      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.24/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1169,plain,
% 3.24/1.01      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_22,plain,
% 3.24/1.01      ( m1_connsp_2(X0,X1,X2)
% 3.24/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/1.01      | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.24/1.01      | v2_struct_0(X1)
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_17,plain,
% 3.24/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 3.24/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | v2_struct_0(X1)
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_358,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.24/1.01      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.24/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | v2_struct_0(X1)
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(resolution,[status(thm)],[c_22,c_17]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_29,negated_conjecture,
% 3.24/1.01      ( ~ v2_struct_0(sK2) ),
% 3.24/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_395,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.24/1.01      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.24/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1)
% 3.24/1.01      | sK2 != X1 ),
% 3.24/1.01      inference(resolution_lifted,[status(thm)],[c_358,c_29]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_396,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.24/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ v2_pre_topc(sK2)
% 3.24/1.01      | ~ l1_pre_topc(sK2) ),
% 3.24/1.01      inference(unflattening,[status(thm)],[c_395]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_28,negated_conjecture,
% 3.24/1.01      ( v2_pre_topc(sK2) ),
% 3.24/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_27,negated_conjecture,
% 3.24/1.01      ( l1_pre_topc(sK2) ),
% 3.24/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_400,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.24/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_396,c_28,c_27]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1167,plain,
% 3.24/1.01      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
% 3.24/1.01      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1545,plain,
% 3.24/1.01      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.24/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1169,c_1167]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_26,negated_conjecture,
% 3.24/1.01      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.24/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_33,plain,
% 3.24/1.01      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_34,plain,
% 3.24/1.01      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1372,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_400]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1516,plain,
% 3.24/1.01      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.24/1.01      | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.24/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_1372]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1517,plain,
% 3.24/1.01      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.24/1.01      | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.24/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_1516]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1909,plain,
% 3.24/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_1545,c_33,c_34,c_1517]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_13,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.24/1.01      | k8_subset_1(X1,X0,X2) = k1_setfam_1(k2_tarski(X0,X2)) ),
% 3.24/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1174,plain,
% 3.24/1.01      ( k8_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 3.24/1.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2230,plain,
% 3.24/1.01      ( k8_subset_1(u1_struct_0(sK2),sK4,X0) = k1_setfam_1(k2_tarski(sK4,X0)) ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1909,c_1174]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_12,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.24/1.01      | m1_subset_1(k8_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 3.24/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1175,plain,
% 3.24/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.24/1.01      | m1_subset_1(k8_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2590,plain,
% 3.24/1.01      ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.24/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_2230,c_1175]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_9007,plain,
% 3.24/1.01      ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_2590,c_33,c_34,c_1517]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_19,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,X1)
% 3.24/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | ~ r2_hidden(X2,X0)
% 3.24/1.01      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.24/1.01      | v2_struct_0(X1)
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_485,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,X1)
% 3.24/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | ~ r2_hidden(X2,X0)
% 3.24/1.01      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1)
% 3.24/1.01      | sK2 != X1 ),
% 3.24/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_486,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,sK2)
% 3.24/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ r2_hidden(X1,X0)
% 3.24/1.01      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.24/1.01      | ~ v2_pre_topc(sK2)
% 3.24/1.01      | ~ l1_pre_topc(sK2) ),
% 3.24/1.01      inference(unflattening,[status(thm)],[c_485]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_490,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,sK2)
% 3.24/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ r2_hidden(X1,X0)
% 3.24/1.01      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_486,c_28,c_27]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_15,plain,
% 3.24/1.01      ( m1_subset_1(X0,X1)
% 3.24/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.24/1.01      | ~ r2_hidden(X0,X2) ),
% 3.24/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_506,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,sK2)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ r2_hidden(X1,X0)
% 3.24/1.01      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.24/1.01      inference(forward_subsumption_resolution,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_490,c_15]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1163,plain,
% 3.24/1.01      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.24/1.01      | r2_hidden(X1,X0) != iProver_top
% 3.24/1.01      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_14,plain,
% 3.24/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1173,plain,
% 3.24/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 3.24/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2142,plain,
% 3.24/1.01      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.24/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1163,c_1173]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_23,negated_conjecture,
% 3.24/1.01      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.24/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1171,plain,
% 3.24/1.01      ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6600,plain,
% 3.24/1.01      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.24/1.01      | m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.24/1.01      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_2142,c_1171]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_24,negated_conjecture,
% 3.24/1.01      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.24/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1170,plain,
% 3.24/1.01      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_18,plain,
% 3.24/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 3.24/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | r2_hidden(X2,X0)
% 3.24/1.01      | v2_struct_0(X1)
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_170,plain,
% 3.24/1.01      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/1.01      | ~ m1_connsp_2(X0,X1,X2)
% 3.24/1.01      | r2_hidden(X2,X0)
% 3.24/1.01      | v2_struct_0(X1)
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_18,c_17]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_171,plain,
% 3.24/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 3.24/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/1.01      | r2_hidden(X2,X0)
% 3.24/1.01      | v2_struct_0(X1)
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(renaming,[status(thm)],[c_170]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_335,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.24/1.01      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.24/1.01      | r2_hidden(X0,X2)
% 3.24/1.01      | v2_struct_0(X1)
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(resolution,[status(thm)],[c_22,c_171]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_416,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.24/1.01      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.24/1.01      | r2_hidden(X0,X2)
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1)
% 3.24/1.01      | sK2 != X1 ),
% 3.24/1.01      inference(resolution_lifted,[status(thm)],[c_335,c_29]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_417,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.24/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.24/1.01      | r2_hidden(X1,X0)
% 3.24/1.01      | ~ v2_pre_topc(sK2)
% 3.24/1.01      | ~ l1_pre_topc(sK2) ),
% 3.24/1.01      inference(unflattening,[status(thm)],[c_416]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_421,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.24/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.24/1.01      | r2_hidden(X1,X0) ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_417,c_28,c_27]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1166,plain,
% 3.24/1.01      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
% 3.24/1.01      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.24/1.01      | r2_hidden(X1,X0) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1467,plain,
% 3.24/1.01      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.24/1.01      | r2_hidden(sK3,sK5) = iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1170,c_1166]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1468,plain,
% 3.24/1.01      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.24/1.01      | r2_hidden(sK3,sK4) = iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1169,c_1166]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5,plain,
% 3.24/1.01      ( ~ r2_hidden(X0,X1)
% 3.24/1.01      | ~ r2_hidden(X0,X2)
% 3.24/1.01      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 3.24/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2776,plain,
% 3.24/1.01      ( ~ r2_hidden(sK3,X0)
% 3.24/1.01      | r2_hidden(sK3,k1_setfam_1(k2_tarski(X0,sK5)))
% 3.24/1.01      | ~ r2_hidden(sK3,sK5) ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3619,plain,
% 3.24/1.01      ( r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5)))
% 3.24/1.01      | ~ r2_hidden(sK3,sK5)
% 3.24/1.01      | ~ r2_hidden(sK3,sK4) ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_2776]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3620,plain,
% 3.24/1.01      ( r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) = iProver_top
% 3.24/1.01      | r2_hidden(sK3,sK5) != iProver_top
% 3.24/1.01      | r2_hidden(sK3,sK4) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_3619]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6922,plain,
% 3.24/1.01      ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.24/1.01      | v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_6600,c_33,c_1467,c_1468,c_3620]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6923,plain,
% 3.24/1.01      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.24/1.01      | m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.24/1.01      inference(renaming,[status(thm)],[c_6922]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_9020,plain,
% 3.24/1.01      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_9007,c_6923]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_16,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,X1)
% 3.24/1.01      | ~ v3_pre_topc(X2,X1)
% 3.24/1.01      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_537,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,X1)
% 3.24/1.01      | ~ v3_pre_topc(X2,X1)
% 3.24/1.01      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | sK2 != X1 ),
% 3.24/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_538,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,sK2)
% 3.24/1.01      | ~ v3_pre_topc(X1,sK2)
% 3.24/1.01      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ v2_pre_topc(sK2) ),
% 3.24/1.01      inference(unflattening,[status(thm)],[c_537]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_542,plain,
% 3.24/1.01      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
% 3.24/1.01      | ~ v3_pre_topc(X1,sK2)
% 3.24/1.01      | ~ v3_pre_topc(X0,sK2) ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_538,c_28]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_543,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,sK2)
% 3.24/1.01      | ~ v3_pre_topc(X1,sK2)
% 3.24/1.01      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.24/1.01      inference(renaming,[status(thm)],[c_542]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3197,plain,
% 3.24/1.01      ( ~ v3_pre_topc(X0,sK2)
% 3.24/1.01      | v3_pre_topc(k1_setfam_1(k2_tarski(X0,sK5)),sK2)
% 3.24/1.01      | ~ v3_pre_topc(sK5,sK2)
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_543]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_7155,plain,
% 3.24/1.01      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2)
% 3.24/1.01      | ~ v3_pre_topc(sK5,sK2)
% 3.24/1.01      | ~ v3_pre_topc(sK4,sK2)
% 3.24/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_3197]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_7156,plain,
% 3.24/1.01      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) = iProver_top
% 3.24/1.01      | v3_pre_topc(sK5,sK2) != iProver_top
% 3.24/1.01      | v3_pre_topc(sK4,sK2) != iProver_top
% 3.24/1.01      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.24/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_7155]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_9,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.24/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1177,plain,
% 3.24/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 3.24/1.01      | v1_xboole_0(X1) != iProver_top
% 3.24/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2874,plain,
% 3.24/1.01      ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.24/1.01      | v1_xboole_0(sK5) = iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1170,c_1177]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_11,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1176,plain,
% 3.24/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 3.24/1.01      | r2_hidden(X0,X1) = iProver_top
% 3.24/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2284,plain,
% 3.24/1.01      ( r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top
% 3.24/1.01      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1169,c_1176]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_20,plain,
% 3.24/1.01      ( v3_pre_topc(X0,X1)
% 3.24/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.24/1.01      | v2_struct_0(X1)
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_461,plain,
% 3.24/1.01      ( v3_pre_topc(X0,X1)
% 3.24/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.24/1.01      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.24/1.01      | ~ v2_pre_topc(X1)
% 3.24/1.01      | ~ l1_pre_topc(X1)
% 3.24/1.01      | sK2 != X1 ),
% 3.24/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_462,plain,
% 3.24/1.01      ( v3_pre_topc(X0,sK2)
% 3.24/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.24/1.01      | ~ v2_pre_topc(sK2)
% 3.24/1.01      | ~ l1_pre_topc(sK2) ),
% 3.24/1.01      inference(unflattening,[status(thm)],[c_461]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_466,plain,
% 3.24/1.01      ( v3_pre_topc(X0,sK2)
% 3.24/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.24/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.24/1.01      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_462,c_28,c_27]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1164,plain,
% 3.24/1.01      ( v3_pre_topc(X0,sK2) = iProver_top
% 3.24/1.01      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.24/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.24/1.01      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2482,plain,
% 3.24/1.01      ( v3_pre_topc(sK4,sK2) = iProver_top
% 3.24/1.01      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.24/1.01      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.24/1.01      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_2284,c_1164]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2283,plain,
% 3.24/1.01      ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top
% 3.24/1.01      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1170,c_1176]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2427,plain,
% 3.24/1.01      ( v3_pre_topc(sK5,sK2) = iProver_top
% 3.24/1.01      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.24/1.01      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.24/1.01      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_2283,c_1164]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1480,plain,
% 3.24/1.01      ( r2_hidden(sK3,sK5) = iProver_top ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_1467,c_33]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1,plain,
% 3.24/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.24/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1185,plain,
% 3.24/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.24/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1707,plain,
% 3.24/1.01      ( v1_xboole_0(sK5) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1480,c_1185]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1513,plain,
% 3.24/1.01      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.24/1.01      | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.24/1.01      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_1372]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1514,plain,
% 3.24/1.01      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.24/1.01      | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.24/1.01      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_1513]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_35,plain,
% 3.24/1.01      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(contradiction,plain,
% 3.24/1.01      ( $false ),
% 3.24/1.01      inference(minisat,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_9020,c_7156,c_2874,c_2482,c_2427,c_1707,c_1517,c_1514,
% 3.24/1.01                 c_35,c_34,c_33]) ).
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/1.01  
% 3.24/1.01  ------                               Statistics
% 3.24/1.01  
% 3.24/1.01  ------ General
% 3.24/1.01  
% 3.24/1.01  abstr_ref_over_cycles:                  0
% 3.24/1.01  abstr_ref_under_cycles:                 0
% 3.24/1.01  gc_basic_clause_elim:                   0
% 3.24/1.01  forced_gc_time:                         0
% 3.24/1.01  parsing_time:                           0.01
% 3.24/1.01  unif_index_cands_time:                  0.
% 3.24/1.01  unif_index_add_time:                    0.
% 3.24/1.01  orderings_time:                         0.
% 3.24/1.01  out_proof_time:                         0.009
% 3.24/1.01  total_time:                             0.264
% 3.24/1.01  num_of_symbols:                         51
% 3.24/1.01  num_of_terms:                           8976
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing
% 3.24/1.01  
% 3.24/1.01  num_of_splits:                          0
% 3.24/1.01  num_of_split_atoms:                     0
% 3.24/1.01  num_of_reused_defs:                     0
% 3.24/1.01  num_eq_ax_congr_red:                    28
% 3.24/1.01  num_of_sem_filtered_clauses:            1
% 3.24/1.01  num_of_subtypes:                        0
% 3.24/1.01  monotx_restored_types:                  0
% 3.24/1.01  sat_num_of_epr_types:                   0
% 3.24/1.01  sat_num_of_non_cyclic_types:            0
% 3.24/1.01  sat_guarded_non_collapsed_types:        0
% 3.24/1.01  num_pure_diseq_elim:                    0
% 3.24/1.01  simp_replaced_by:                       0
% 3.24/1.01  res_preprocessed:                       125
% 3.24/1.01  prep_upred:                             0
% 3.24/1.01  prep_unflattend:                        6
% 3.24/1.01  smt_new_axioms:                         0
% 3.24/1.01  pred_elim_cands:                        4
% 3.24/1.01  pred_elim:                              4
% 3.24/1.01  pred_elim_cl:                           4
% 3.24/1.01  pred_elim_cycles:                       6
% 3.24/1.01  merged_defs:                            0
% 3.24/1.01  merged_defs_ncl:                        0
% 3.24/1.01  bin_hyper_res:                          0
% 3.24/1.01  prep_cycles:                            4
% 3.24/1.01  pred_elim_time:                         0.006
% 3.24/1.01  splitting_time:                         0.
% 3.24/1.01  sem_filter_time:                        0.
% 3.24/1.01  monotx_time:                            0.001
% 3.24/1.01  subtype_inf_time:                       0.
% 3.24/1.01  
% 3.24/1.01  ------ Problem properties
% 3.24/1.01  
% 3.24/1.01  clauses:                                25
% 3.24/1.01  conjectures:                            4
% 3.24/1.01  epr:                                    5
% 3.24/1.01  horn:                                   21
% 3.24/1.01  ground:                                 4
% 3.24/1.01  unary:                                  4
% 3.24/1.01  binary:                                 7
% 3.24/1.01  lits:                                   66
% 3.24/1.01  lits_eq:                                4
% 3.24/1.01  fd_pure:                                0
% 3.24/1.01  fd_pseudo:                              0
% 3.24/1.01  fd_cond:                                0
% 3.24/1.01  fd_pseudo_cond:                         3
% 3.24/1.01  ac_symbols:                             0
% 3.24/1.01  
% 3.24/1.01  ------ Propositional Solver
% 3.24/1.01  
% 3.24/1.01  prop_solver_calls:                      29
% 3.24/1.01  prop_fast_solver_calls:                 1062
% 3.24/1.01  smt_solver_calls:                       0
% 3.24/1.01  smt_fast_solver_calls:                  0
% 3.24/1.01  prop_num_of_clauses:                    3811
% 3.24/1.01  prop_preprocess_simplified:             8756
% 3.24/1.01  prop_fo_subsumed:                       35
% 3.24/1.01  prop_solver_time:                       0.
% 3.24/1.01  smt_solver_time:                        0.
% 3.24/1.01  smt_fast_solver_time:                   0.
% 3.24/1.01  prop_fast_solver_time:                  0.
% 3.24/1.01  prop_unsat_core_time:                   0.
% 3.24/1.01  
% 3.24/1.01  ------ QBF
% 3.24/1.01  
% 3.24/1.01  qbf_q_res:                              0
% 3.24/1.01  qbf_num_tautologies:                    0
% 3.24/1.01  qbf_prep_cycles:                        0
% 3.24/1.01  
% 3.24/1.01  ------ BMC1
% 3.24/1.01  
% 3.24/1.01  bmc1_current_bound:                     -1
% 3.24/1.01  bmc1_last_solved_bound:                 -1
% 3.24/1.01  bmc1_unsat_core_size:                   -1
% 3.24/1.01  bmc1_unsat_core_parents_size:           -1
% 3.24/1.01  bmc1_merge_next_fun:                    0
% 3.24/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.24/1.01  
% 3.24/1.01  ------ Instantiation
% 3.24/1.01  
% 3.24/1.01  inst_num_of_clauses:                    1021
% 3.24/1.01  inst_num_in_passive:                    272
% 3.24/1.01  inst_num_in_active:                     346
% 3.24/1.01  inst_num_in_unprocessed:                403
% 3.24/1.01  inst_num_of_loops:                      450
% 3.24/1.01  inst_num_of_learning_restarts:          0
% 3.24/1.01  inst_num_moves_active_passive:          101
% 3.24/1.01  inst_lit_activity:                      0
% 3.24/1.01  inst_lit_activity_moves:                0
% 3.24/1.01  inst_num_tautologies:                   0
% 3.24/1.01  inst_num_prop_implied:                  0
% 3.24/1.01  inst_num_existing_simplified:           0
% 3.24/1.01  inst_num_eq_res_simplified:             0
% 3.24/1.01  inst_num_child_elim:                    0
% 3.24/1.01  inst_num_of_dismatching_blockings:      309
% 3.24/1.01  inst_num_of_non_proper_insts:           790
% 3.24/1.01  inst_num_of_duplicates:                 0
% 3.24/1.01  inst_inst_num_from_inst_to_res:         0
% 3.24/1.01  inst_dismatching_checking_time:         0.
% 3.24/1.01  
% 3.24/1.01  ------ Resolution
% 3.24/1.01  
% 3.24/1.01  res_num_of_clauses:                     0
% 3.24/1.01  res_num_in_passive:                     0
% 3.24/1.01  res_num_in_active:                      0
% 3.24/1.01  res_num_of_loops:                       129
% 3.24/1.01  res_forward_subset_subsumed:            71
% 3.24/1.01  res_backward_subset_subsumed:           0
% 3.24/1.01  res_forward_subsumed:                   0
% 3.24/1.01  res_backward_subsumed:                  0
% 3.24/1.01  res_forward_subsumption_resolution:     1
% 3.24/1.01  res_backward_subsumption_resolution:    0
% 3.24/1.01  res_clause_to_clause_subsumption:       747
% 3.24/1.01  res_orphan_elimination:                 0
% 3.24/1.01  res_tautology_del:                      35
% 3.24/1.01  res_num_eq_res_simplified:              0
% 3.24/1.01  res_num_sel_changes:                    0
% 3.24/1.01  res_moves_from_active_to_pass:          0
% 3.24/1.01  
% 3.24/1.01  ------ Superposition
% 3.24/1.01  
% 3.24/1.01  sup_time_total:                         0.
% 3.24/1.01  sup_time_generating:                    0.
% 3.24/1.01  sup_time_sim_full:                      0.
% 3.24/1.01  sup_time_sim_immed:                     0.
% 3.24/1.01  
% 3.24/1.01  sup_num_of_clauses:                     176
% 3.24/1.01  sup_num_in_active:                      88
% 3.24/1.01  sup_num_in_passive:                     88
% 3.24/1.01  sup_num_of_loops:                       89
% 3.24/1.01  sup_fw_superposition:                   83
% 3.24/1.01  sup_bw_superposition:                   140
% 3.24/1.01  sup_immediate_simplified:               44
% 3.24/1.01  sup_given_eliminated:                   0
% 3.24/1.01  comparisons_done:                       0
% 3.24/1.01  comparisons_avoided:                    0
% 3.24/1.01  
% 3.24/1.01  ------ Simplifications
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  sim_fw_subset_subsumed:                 32
% 3.24/1.01  sim_bw_subset_subsumed:                 5
% 3.24/1.01  sim_fw_subsumed:                        8
% 3.24/1.01  sim_bw_subsumed:                        0
% 3.24/1.01  sim_fw_subsumption_res:                 1
% 3.24/1.01  sim_bw_subsumption_res:                 0
% 3.24/1.01  sim_tautology_del:                      19
% 3.24/1.01  sim_eq_tautology_del:                   0
% 3.24/1.01  sim_eq_res_simp:                        2
% 3.24/1.01  sim_fw_demodulated:                     0
% 3.24/1.01  sim_bw_demodulated:                     0
% 3.24/1.01  sim_light_normalised:                   3
% 3.24/1.01  sim_joinable_taut:                      0
% 3.24/1.01  sim_joinable_simp:                      0
% 3.24/1.01  sim_ac_normalised:                      0
% 3.24/1.01  sim_smt_subsumption:                    0
% 3.24/1.01  
%------------------------------------------------------------------------------
