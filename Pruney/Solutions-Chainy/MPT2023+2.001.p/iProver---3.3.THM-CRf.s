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
% DateTime   : Thu Dec  3 12:28:45 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  234 (4065 expanded)
%              Number of clauses        :  142 ( 901 expanded)
%              Number of leaves         :   23 (1386 expanded)
%              Depth                    :   27
%              Number of atoms          :  859 (23180 expanded)
%              Number of equality atoms :  166 ( 446 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k3_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f58,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f38,f57,f56,f55,f54])).

fof(f97,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f58])).

fof(f18,axiom,(
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

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f93,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f95,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f112,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f98,plain,(
    ~ m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f108,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(definition_unfolding,[],[f98,f80])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f96,plain,(
    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f58])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f106,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f72,f80])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f86,f80])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f80])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f99,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f59,f80,f80])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1660,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1639,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_27,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_31,c_27])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_470,c_38])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_37,c_36])).

cnf(c_1635,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_2006,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_1635])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1924,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[status(thm)],[c_505,c_33])).

cnf(c_1925,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(c_2019,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2006,c_42,c_1925])).

cnf(c_24,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1641,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3033,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2019,c_1641])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1647,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4463,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3033,c_1647])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_281,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_282,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_281])).

cnf(c_347,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_25,c_282])).

cnf(c_2792,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_3272,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ r1_tarski(sK5,sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_3274,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3272])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_3273,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3278,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3273])).

cnf(c_5674,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_16,c_33])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4270,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_18,c_33])).

cnf(c_21,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2597,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK2,X0))) ),
    inference(resolution,[status(thm)],[c_21,c_505])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_521,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_38])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,X1)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,X1)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK2,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_37,c_36])).

cnf(c_2741,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,X1)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK2,X0))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2597,c_526])).

cnf(c_4930,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,sK5)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_4270,c_2741])).

cnf(c_5001,plain,
    ( r2_hidden(sK3,sK5)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4930,c_35])).

cnf(c_6176,plain,
    ( r2_hidden(sK3,sK5)
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_5674,c_5001])).

cnf(c_6183,plain,
    ( r2_hidden(sK3,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6176])).

cnf(c_32,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2604,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_32,c_21])).

cnf(c_28,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_569,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_38])).

cnf(c_570,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_574,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_570,c_37,c_36])).

cnf(c_590,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_574,c_24])).

cnf(c_3539,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) ),
    inference(resolution,[status(thm)],[c_2604,c_590])).

cnf(c_8606,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2)
    | ~ r2_hidden(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) ),
    inference(resolution,[status(thm)],[c_3539,c_21])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1638,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2007,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_1635])).

cnf(c_1926,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[status(thm)],[c_505,c_34])).

cnf(c_1927,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1926])).

cnf(c_2057,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2007,c_42,c_1927])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3021,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2057,c_1642])).

cnf(c_3027,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3021])).

cnf(c_13,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1650,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1649,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5538,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1650,c_1649])).

cnf(c_1643,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1632,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_1644,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2731,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_1644])).

cnf(c_1640,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2928,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2731,c_1640])).

cnf(c_3151,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_2928])).

cnf(c_10555,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5538,c_3151])).

cnf(c_10576,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2)
    | ~ r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5)))
    | ~ r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10555])).

cnf(c_15284,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2)
    | ~ r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8606,c_3027,c_10576])).

cnf(c_26,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_617,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_36])).

cnf(c_618,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
    | ~ v3_pre_topc(X1,sK2)
    | ~ v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_37])).

cnf(c_623,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_622])).

cnf(c_15443,plain,
    ( ~ v3_pre_topc(sK5,sK2)
    | ~ v3_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) ),
    inference(resolution,[status(thm)],[c_15284,c_623])).

cnf(c_15446,plain,
    ( ~ v3_pre_topc(sK5,sK2)
    | ~ v3_pre_topc(sK4,sK2)
    | ~ r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15443,c_35,c_1924,c_1926])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_15466,plain,
    ( ~ v3_pre_topc(sK5,sK2)
    | ~ v3_pre_topc(sK4,sK2)
    | ~ r2_hidden(sK3,sK5)
    | ~ r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_15446,c_7])).

cnf(c_4272,plain,
    ( r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_18,c_34])).

cnf(c_29,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_545,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_38])).

cnf(c_546,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_550,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_37,c_36])).

cnf(c_2742,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2597,c_550])).

cnf(c_4943,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_4272,c_2742])).

cnf(c_5287,plain,
    ( v3_pre_topc(sK4,sK2)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4943,c_35])).

cnf(c_6179,plain,
    ( v3_pre_topc(sK4,sK2)
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_5674,c_5287])).

cnf(c_4941,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,sK4)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_4272,c_2741])).

cnf(c_5270,plain,
    ( r2_hidden(sK3,sK4)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4941,c_35])).

cnf(c_6178,plain,
    ( r2_hidden(sK3,sK4)
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_5674,c_5270])).

cnf(c_4932,plain,
    ( v3_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_4270,c_2742])).

cnf(c_5142,plain,
    ( v3_pre_topc(sK5,sK2)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4932,c_35])).

cnf(c_6177,plain,
    ( v3_pre_topc(sK5,sK2)
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_5674,c_5142])).

cnf(c_8396,plain,
    ( ~ r2_hidden(sK3,sK5)
    | ~ r1_tarski(sK5,sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3272])).

cnf(c_15560,plain,
    ( ~ r2_hidden(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15466,c_3273,c_6179,c_6178,c_6177,c_8396])).

cnf(c_15562,plain,
    ( r2_hidden(sK3,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15560])).

cnf(c_15743,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4463,c_3274,c_3278,c_6183,c_15562])).

cnf(c_15750,plain,
    ( r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1660,c_15743])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2408,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1650])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1652,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4889,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X1
    | r1_tarski(X1,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2408,c_1652])).

cnf(c_15540,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X1
    | r1_tarski(X1,k1_setfam_1(k2_tarski(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_4889])).

cnf(c_16944,plain,
    ( k1_setfam_1(k2_tarski(X0,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_15750,c_15540])).

cnf(c_1655,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1631,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(X1,sK2) != iProver_top
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1648,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4550,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_2928])).

cnf(c_6366,plain,
    ( v3_pre_topc(sK5,sK2) != iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1631,c_4550])).

cnf(c_4548,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_1640])).

cnf(c_4933,plain,
    ( v3_pre_topc(sK5,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4932])).

cnf(c_4944,plain,
    ( v3_pre_topc(sK4,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4943])).

cnf(c_6369,plain,
    ( r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6366,c_42,c_1925,c_1927,c_4548,c_4933,c_4944])).

cnf(c_6376,plain,
    ( r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_6369])).

cnf(c_1646,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4176,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_1646])).

cnf(c_1634,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_5225,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,sK5) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4176,c_1634])).

cnf(c_5003,plain,
    ( r2_hidden(sK3,sK5) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5001])).

cnf(c_8562,plain,
    ( r2_hidden(sK3,sK5) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5225,c_5003])).

cnf(c_8568,plain,
    ( r2_hidden(sK3,sK5) = iProver_top
    | v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8562,c_4548])).

cnf(c_16344,plain,
    ( v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6376,c_8568,c_15562])).

cnf(c_17765,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16944,c_16344])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17765,c_15562,c_6183])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:36:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.82/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/0.99  
% 3.82/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.82/0.99  
% 3.82/0.99  ------  iProver source info
% 3.82/0.99  
% 3.82/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.82/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.82/0.99  git: non_committed_changes: false
% 3.82/0.99  git: last_make_outside_of_git: false
% 3.82/0.99  
% 3.82/0.99  ------ 
% 3.82/0.99  ------ Parsing...
% 3.82/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.82/0.99  
% 3.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.82/0.99  
% 3.82/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.82/0.99  
% 3.82/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.99  ------ Proving...
% 3.82/0.99  ------ Problem Properties 
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  clauses                                 33
% 3.82/0.99  conjectures                             4
% 3.82/0.99  EPR                                     9
% 3.82/0.99  Horn                                    29
% 3.82/0.99  unary                                   9
% 3.82/0.99  binary                                  7
% 3.82/0.99  lits                                    80
% 3.82/0.99  lits eq                                 6
% 3.82/0.99  fd_pure                                 0
% 3.82/0.99  fd_pseudo                               0
% 3.82/0.99  fd_cond                                 0
% 3.82/0.99  fd_pseudo_cond                          4
% 3.82/0.99  AC symbols                              0
% 3.82/0.99  
% 3.82/0.99  ------ Input Options Time Limit: Unbounded
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  ------ 
% 3.82/0.99  Current options:
% 3.82/0.99  ------ 
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  ------ Proving...
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  % SZS status Theorem for theBenchmark.p
% 3.82/0.99  
% 3.82/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.82/0.99  
% 3.82/0.99  fof(f2,axiom,(
% 3.82/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f21,plain,(
% 3.82/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.82/0.99    inference(ennf_transformation,[],[f2])).
% 3.82/0.99  
% 3.82/0.99  fof(f39,plain,(
% 3.82/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.82/0.99    inference(nnf_transformation,[],[f21])).
% 3.82/0.99  
% 3.82/0.99  fof(f40,plain,(
% 3.82/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.82/0.99    inference(rectify,[],[f39])).
% 3.82/0.99  
% 3.82/0.99  fof(f41,plain,(
% 3.82/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.82/0.99    introduced(choice_axiom,[])).
% 3.82/0.99  
% 3.82/0.99  fof(f42,plain,(
% 3.82/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.82/0.99  
% 3.82/0.99  fof(f61,plain,(
% 3.82/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f42])).
% 3.82/0.99  
% 3.82/0.99  fof(f19,conjecture,(
% 3.82/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f20,negated_conjecture,(
% 3.82/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.82/0.99    inference(negated_conjecture,[],[f19])).
% 3.82/0.99  
% 3.82/0.99  fof(f37,plain,(
% 3.82/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.82/0.99    inference(ennf_transformation,[],[f20])).
% 3.82/0.99  
% 3.82/0.99  fof(f38,plain,(
% 3.82/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.82/0.99    inference(flattening,[],[f37])).
% 3.82/0.99  
% 3.82/0.99  fof(f57,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k3_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.82/0.99    introduced(choice_axiom,[])).
% 3.82/0.99  
% 3.82/0.99  fof(f56,plain,(
% 3.82/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.82/0.99    introduced(choice_axiom,[])).
% 3.82/0.99  
% 3.82/0.99  fof(f55,plain,(
% 3.82/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.82/0.99    introduced(choice_axiom,[])).
% 3.82/0.99  
% 3.82/0.99  fof(f54,plain,(
% 3.82/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.82/0.99    introduced(choice_axiom,[])).
% 3.82/0.99  
% 3.82/0.99  fof(f58,plain,(
% 3.82/0.99    (((~m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f38,f57,f56,f55,f54])).
% 3.82/0.99  
% 3.82/0.99  fof(f97,plain,(
% 3.82/0.99    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.82/0.99    inference(cnf_transformation,[],[f58])).
% 3.82/0.99  
% 3.82/0.99  fof(f18,axiom,(
% 3.82/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f35,plain,(
% 3.82/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.82/0.99    inference(ennf_transformation,[],[f18])).
% 3.82/0.99  
% 3.82/0.99  fof(f36,plain,(
% 3.82/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/0.99    inference(flattening,[],[f35])).
% 3.82/0.99  
% 3.82/0.99  fof(f91,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f36])).
% 3.82/0.99  
% 3.82/0.99  fof(f16,axiom,(
% 3.82/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f31,plain,(
% 3.82/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.82/0.99    inference(ennf_transformation,[],[f16])).
% 3.82/0.99  
% 3.82/0.99  fof(f32,plain,(
% 3.82/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/0.99    inference(flattening,[],[f31])).
% 3.82/0.99  
% 3.82/0.99  fof(f87,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f32])).
% 3.82/0.99  
% 3.82/0.99  fof(f92,plain,(
% 3.82/0.99    ~v2_struct_0(sK2)),
% 3.82/0.99    inference(cnf_transformation,[],[f58])).
% 3.82/0.99  
% 3.82/0.99  fof(f93,plain,(
% 3.82/0.99    v2_pre_topc(sK2)),
% 3.82/0.99    inference(cnf_transformation,[],[f58])).
% 3.82/0.99  
% 3.82/0.99  fof(f94,plain,(
% 3.82/0.99    l1_pre_topc(sK2)),
% 3.82/0.99    inference(cnf_transformation,[],[f58])).
% 3.82/0.99  
% 3.82/0.99  fof(f95,plain,(
% 3.82/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 3.82/0.99    inference(cnf_transformation,[],[f58])).
% 3.82/0.99  
% 3.82/0.99  fof(f13,axiom,(
% 3.82/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f26,plain,(
% 3.82/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.82/0.99    inference(ennf_transformation,[],[f13])).
% 3.82/0.99  
% 3.82/0.99  fof(f27,plain,(
% 3.82/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.82/0.99    inference(flattening,[],[f26])).
% 3.82/0.99  
% 3.82/0.99  fof(f84,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f27])).
% 3.82/0.99  
% 3.82/0.99  fof(f7,axiom,(
% 3.82/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f24,plain,(
% 3.82/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.82/0.99    inference(ennf_transformation,[],[f7])).
% 3.82/0.99  
% 3.82/0.99  fof(f50,plain,(
% 3.82/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.82/0.99    inference(nnf_transformation,[],[f24])).
% 3.82/0.99  
% 3.82/0.99  fof(f76,plain,(
% 3.82/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f50])).
% 3.82/0.99  
% 3.82/0.99  fof(f14,axiom,(
% 3.82/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f28,plain,(
% 3.82/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.82/0.99    inference(ennf_transformation,[],[f14])).
% 3.82/0.99  
% 3.82/0.99  fof(f85,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f28])).
% 3.82/0.99  
% 3.82/0.99  fof(f12,axiom,(
% 3.82/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f51,plain,(
% 3.82/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.82/0.99    inference(nnf_transformation,[],[f12])).
% 3.82/0.99  
% 3.82/0.99  fof(f83,plain,(
% 3.82/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f51])).
% 3.82/0.99  
% 3.82/0.99  fof(f4,axiom,(
% 3.82/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f48,plain,(
% 3.82/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.82/0.99    inference(nnf_transformation,[],[f4])).
% 3.82/0.99  
% 3.82/0.99  fof(f49,plain,(
% 3.82/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.82/0.99    inference(flattening,[],[f48])).
% 3.82/0.99  
% 3.82/0.99  fof(f70,plain,(
% 3.82/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.82/0.99    inference(cnf_transformation,[],[f49])).
% 3.82/0.99  
% 3.82/0.99  fof(f112,plain,(
% 3.82/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.82/0.99    inference(equality_resolution,[],[f70])).
% 3.82/0.99  
% 3.82/0.99  fof(f74,plain,(
% 3.82/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f50])).
% 3.82/0.99  
% 3.82/0.99  fof(f11,axiom,(
% 3.82/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f25,plain,(
% 3.82/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.82/0.99    inference(ennf_transformation,[],[f11])).
% 3.82/0.99  
% 3.82/0.99  fof(f81,plain,(
% 3.82/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f25])).
% 3.82/0.99  
% 3.82/0.99  fof(f17,axiom,(
% 3.82/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f33,plain,(
% 3.82/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.82/0.99    inference(ennf_transformation,[],[f17])).
% 3.82/0.99  
% 3.82/0.99  fof(f34,plain,(
% 3.82/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/0.99    inference(flattening,[],[f33])).
% 3.82/0.99  
% 3.82/0.99  fof(f52,plain,(
% 3.82/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/0.99    inference(nnf_transformation,[],[f34])).
% 3.82/0.99  
% 3.82/0.99  fof(f53,plain,(
% 3.82/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/0.99    inference(flattening,[],[f52])).
% 3.82/0.99  
% 3.82/0.99  fof(f88,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f53])).
% 3.82/0.99  
% 3.82/0.99  fof(f98,plain,(
% 3.82/0.99    ~m1_subset_1(k3_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.82/0.99    inference(cnf_transformation,[],[f58])).
% 3.82/0.99  
% 3.82/0.99  fof(f10,axiom,(
% 3.82/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f80,plain,(
% 3.82/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.82/0.99    inference(cnf_transformation,[],[f10])).
% 3.82/0.99  
% 3.82/0.99  fof(f108,plain,(
% 3.82/0.99    ~m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.82/0.99    inference(definition_unfolding,[],[f98,f80])).
% 3.82/0.99  
% 3.82/0.99  fof(f90,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f53])).
% 3.82/0.99  
% 3.82/0.99  fof(f96,plain,(
% 3.82/0.99    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.82/0.99    inference(cnf_transformation,[],[f58])).
% 3.82/0.99  
% 3.82/0.99  fof(f82,plain,(
% 3.82/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.82/0.99    inference(cnf_transformation,[],[f51])).
% 3.82/0.99  
% 3.82/0.99  fof(f5,axiom,(
% 3.82/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f72,plain,(
% 3.82/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f5])).
% 3.82/0.99  
% 3.82/0.99  fof(f106,plain,(
% 3.82/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 3.82/0.99    inference(definition_unfolding,[],[f72,f80])).
% 3.82/0.99  
% 3.82/0.99  fof(f6,axiom,(
% 3.82/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f22,plain,(
% 3.82/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.82/0.99    inference(ennf_transformation,[],[f6])).
% 3.82/0.99  
% 3.82/0.99  fof(f23,plain,(
% 3.82/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.82/0.99    inference(flattening,[],[f22])).
% 3.82/0.99  
% 3.82/0.99  fof(f73,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f23])).
% 3.82/0.99  
% 3.82/0.99  fof(f15,axiom,(
% 3.82/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f29,plain,(
% 3.82/0.99    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.82/0.99    inference(ennf_transformation,[],[f15])).
% 3.82/0.99  
% 3.82/0.99  fof(f30,plain,(
% 3.82/0.99    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.82/0.99    inference(flattening,[],[f29])).
% 3.82/0.99  
% 3.82/0.99  fof(f86,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f30])).
% 3.82/0.99  
% 3.82/0.99  fof(f107,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.82/0.99    inference(definition_unfolding,[],[f86,f80])).
% 3.82/0.99  
% 3.82/0.99  fof(f3,axiom,(
% 3.82/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f43,plain,(
% 3.82/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.82/0.99    inference(nnf_transformation,[],[f3])).
% 3.82/0.99  
% 3.82/0.99  fof(f44,plain,(
% 3.82/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.82/0.99    inference(flattening,[],[f43])).
% 3.82/0.99  
% 3.82/0.99  fof(f45,plain,(
% 3.82/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.82/0.99    inference(rectify,[],[f44])).
% 3.82/0.99  
% 3.82/0.99  fof(f46,plain,(
% 3.82/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.82/0.99    introduced(choice_axiom,[])).
% 3.82/0.99  
% 3.82/0.99  fof(f47,plain,(
% 3.82/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 3.82/0.99  
% 3.82/0.99  fof(f65,plain,(
% 3.82/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.82/0.99    inference(cnf_transformation,[],[f47])).
% 3.82/0.99  
% 3.82/0.99  fof(f103,plain,(
% 3.82/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 3.82/0.99    inference(definition_unfolding,[],[f65,f80])).
% 3.82/0.99  
% 3.82/0.99  fof(f109,plain,(
% 3.82/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.82/0.99    inference(equality_resolution,[],[f103])).
% 3.82/0.99  
% 3.82/0.99  fof(f89,plain,(
% 3.82/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f53])).
% 3.82/0.99  
% 3.82/0.99  fof(f1,axiom,(
% 3.82/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/0.99  
% 3.82/0.99  fof(f59,plain,(
% 3.82/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f1])).
% 3.82/0.99  
% 3.82/0.99  fof(f99,plain,(
% 3.82/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 3.82/0.99    inference(definition_unfolding,[],[f59,f80,f80])).
% 3.82/0.99  
% 3.82/0.99  fof(f71,plain,(
% 3.82/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f49])).
% 3.82/0.99  
% 3.82/0.99  fof(f77,plain,(
% 3.82/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 3.82/0.99    inference(cnf_transformation,[],[f50])).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2,plain,
% 3.82/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1660,plain,
% 3.82/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.82/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_33,negated_conjecture,
% 3.82/0.99      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1639,plain,
% 3.82/0.99      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_31,plain,
% 3.82/0.99      ( m1_connsp_2(X0,X1,X2)
% 3.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.82/0.99      | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.82/0.99      | v2_struct_0(X1)
% 3.82/0.99      | ~ v2_pre_topc(X1)
% 3.82/0.99      | ~ l1_pre_topc(X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_27,plain,
% 3.82/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 3.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.82/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | v2_struct_0(X1)
% 3.82/0.99      | ~ v2_pre_topc(X1)
% 3.82/0.99      | ~ l1_pre_topc(X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_470,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.82/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | v2_struct_0(X1)
% 3.82/0.99      | ~ v2_pre_topc(X1)
% 3.82/0.99      | ~ l1_pre_topc(X1) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_31,c_27]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_38,negated_conjecture,
% 3.82/0.99      ( ~ v2_struct_0(sK2) ),
% 3.82/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_500,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.82/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | ~ v2_pre_topc(X1)
% 3.82/0.99      | ~ l1_pre_topc(X1)
% 3.82/0.99      | sK2 != X1 ),
% 3.82/0.99      inference(resolution_lifted,[status(thm)],[c_470,c_38]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_501,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.82/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ v2_pre_topc(sK2)
% 3.82/0.99      | ~ l1_pre_topc(sK2) ),
% 3.82/0.99      inference(unflattening,[status(thm)],[c_500]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_37,negated_conjecture,
% 3.82/0.99      ( v2_pre_topc(sK2) ),
% 3.82/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_36,negated_conjecture,
% 3.82/0.99      ( l1_pre_topc(sK2) ),
% 3.82/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_505,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.82/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_501,c_37,c_36]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1635,plain,
% 3.82/0.99      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
% 3.82/0.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.82/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2006,plain,
% 3.82/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.82/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_1639,c_1635]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_35,negated_conjecture,
% 3.82/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.82/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_42,plain,
% 3.82/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1924,plain,
% 3.82/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.82/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_505,c_33]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1925,plain,
% 3.82/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.82/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_1924]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2019,plain,
% 3.82/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_2006,c_42,c_1925]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_24,plain,
% 3.82/0.99      ( m1_subset_1(X0,X1)
% 3.82/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.82/0.99      | ~ r2_hidden(X0,X2) ),
% 3.82/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1641,plain,
% 3.82/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.82/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.82/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_3033,plain,
% 3.82/0.99      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 3.82/0.99      | r2_hidden(X0,sK5) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_2019,c_1641]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_16,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.82/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1647,plain,
% 3.82/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.82/0.99      | v1_xboole_0(X1) != iProver_top
% 3.82/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4463,plain,
% 3.82/0.99      ( r2_hidden(X0,sK5) != iProver_top
% 3.82/0.99      | v1_xboole_0(X0) = iProver_top
% 3.82/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_3033,c_1647]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_25,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.82/0.99      | ~ r2_hidden(X2,X0)
% 3.82/0.99      | ~ v1_xboole_0(X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_22,plain,
% 3.82/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_281,plain,
% 3.82/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.82/0.99      inference(prop_impl,[status(thm)],[c_22]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_282,plain,
% 3.82/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.82/0.99      inference(renaming,[status(thm)],[c_281]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_347,plain,
% 3.82/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.82/0.99      inference(bin_hyper_res,[status(thm)],[c_25,c_282]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2792,plain,
% 3.82/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,sK5) | ~ v1_xboole_0(sK5) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_347]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_3272,plain,
% 3.82/0.99      ( ~ r2_hidden(X0,sK5) | ~ r1_tarski(sK5,sK5) | ~ v1_xboole_0(sK5) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_2792]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_3274,plain,
% 3.82/0.99      ( r2_hidden(X0,sK5) != iProver_top
% 3.82/0.99      | r1_tarski(sK5,sK5) != iProver_top
% 3.82/0.99      | v1_xboole_0(sK5) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_3272]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_11,plain,
% 3.82/0.99      ( r1_tarski(X0,X0) ),
% 3.82/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_3273,plain,
% 3.82/0.99      ( r1_tarski(sK5,sK5) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_3278,plain,
% 3.82/0.99      ( r1_tarski(sK5,sK5) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_3273]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_5674,plain,
% 3.82/0.99      ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.82/0.99      | v1_xboole_0(sK5) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_16,c_33]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_18,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4270,plain,
% 3.82/0.99      ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_18,c_33]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_21,plain,
% 3.82/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2597,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.82/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK2,X0))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_21,c_505]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_30,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.82/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | r2_hidden(X0,X2)
% 3.82/0.99      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.82/0.99      | v2_struct_0(X1)
% 3.82/0.99      | ~ v2_pre_topc(X1)
% 3.82/0.99      | ~ l1_pre_topc(X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_521,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.82/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | r2_hidden(X0,X2)
% 3.82/0.99      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.82/0.99      | ~ v2_pre_topc(X1)
% 3.82/0.99      | ~ l1_pre_topc(X1)
% 3.82/0.99      | sK2 != X1 ),
% 3.82/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_38]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_522,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.82/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | r2_hidden(X0,X1)
% 3.82/0.99      | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK2,X0)))
% 3.82/0.99      | ~ v2_pre_topc(sK2)
% 3.82/0.99      | ~ l1_pre_topc(sK2) ),
% 3.82/0.99      inference(unflattening,[status(thm)],[c_521]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_526,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.82/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | r2_hidden(X0,X1)
% 3.82/0.99      | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK2,X0))) ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_522,c_37,c_36]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2741,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.82/0.99      | r2_hidden(X0,X1)
% 3.82/0.99      | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK2,X0))) ),
% 3.82/0.99      inference(backward_subsumption_resolution,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_2597,c_526]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4930,plain,
% 3.82/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.82/0.99      | r2_hidden(sK3,sK5)
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_4270,c_2741]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_5001,plain,
% 3.82/0.99      ( r2_hidden(sK3,sK5)
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_4930,c_35]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_6176,plain,
% 3.82/0.99      ( r2_hidden(sK3,sK5) | v1_xboole_0(sK5) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_5674,c_5001]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_6183,plain,
% 3.82/0.99      ( r2_hidden(sK3,sK5) = iProver_top
% 3.82/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_6176]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_32,negated_conjecture,
% 3.82/0.99      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2604,plain,
% 3.82/0.99      ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_32,c_21]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_28,plain,
% 3.82/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | ~ r2_hidden(X2,X0)
% 3.82/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.82/0.99      | v2_struct_0(X1)
% 3.82/0.99      | ~ v2_pre_topc(X1)
% 3.82/0.99      | ~ l1_pre_topc(X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_569,plain,
% 3.82/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | ~ r2_hidden(X2,X0)
% 3.82/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.82/0.99      | ~ v2_pre_topc(X1)
% 3.82/0.99      | ~ l1_pre_topc(X1)
% 3.82/0.99      | sK2 != X1 ),
% 3.82/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_38]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_570,plain,
% 3.82/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ r2_hidden(X1,X0)
% 3.82/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.82/0.99      | ~ v2_pre_topc(sK2)
% 3.82/0.99      | ~ l1_pre_topc(sK2) ),
% 3.82/0.99      inference(unflattening,[status(thm)],[c_569]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_574,plain,
% 3.82/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ r2_hidden(X1,X0)
% 3.82/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_570,c_37,c_36]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_590,plain,
% 3.82/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ r2_hidden(X1,X0)
% 3.82/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.82/0.99      inference(forward_subsumption_resolution,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_574,c_24]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_3539,plain,
% 3.82/0.99      ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2)
% 3.82/0.99      | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_2604,c_590]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_8606,plain,
% 3.82/0.99      ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2)
% 3.82/0.99      | ~ r2_hidden(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_3539,c_21]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_34,negated_conjecture,
% 3.82/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1638,plain,
% 3.82/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2007,plain,
% 3.82/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.82/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_1638,c_1635]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1926,plain,
% 3.82/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.82/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_505,c_34]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1927,plain,
% 3.82/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.82/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_1926]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2057,plain,
% 3.82/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_2007,c_42,c_1927]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_23,plain,
% 3.82/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1642,plain,
% 3.82/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.82/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_3021,plain,
% 3.82/0.99      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_2057,c_1642]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_3027,plain,
% 3.82/0.99      ( r1_tarski(sK4,u1_struct_0(sK2)) ),
% 3.82/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3021]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_13,plain,
% 3.82/0.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 3.82/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1650,plain,
% 3.82/0.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_14,plain,
% 3.82/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.82/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1649,plain,
% 3.82/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.82/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.82/0.99      | r1_tarski(X0,X2) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_5538,plain,
% 3.82/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.82/0.99      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_1650,c_1649]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1643,plain,
% 3.82/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.82/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1632,plain,
% 3.82/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.82/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.82/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.82/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1644,plain,
% 3.82/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.82/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2731,plain,
% 3.82/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.82/0.99      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top
% 3.82/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.82/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_1632,c_1644]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1640,plain,
% 3.82/0.99      ( m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2928,plain,
% 3.82/0.99      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.82/0.99      | m1_subset_1(k1_setfam_1(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.82/0.99      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_2731,c_1640]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_3151,plain,
% 3.82/0.99      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.82/0.99      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top
% 3.82/0.99      | r1_tarski(k1_setfam_1(k2_tarski(sK4,sK5)),u1_struct_0(sK2)) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_1643,c_2928]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_10555,plain,
% 3.82/0.99      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.82/0.99      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top
% 3.82/0.99      | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_5538,c_3151]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_10576,plain,
% 3.82/0.99      ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2)
% 3.82/0.99      | ~ r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5)))
% 3.82/0.99      | ~ r1_tarski(sK4,u1_struct_0(sK2)) ),
% 3.82/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_10555]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_15284,plain,
% 3.82/0.99      ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2)
% 3.82/0.99      | ~ r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_8606,c_3027,c_10576]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_26,plain,
% 3.82/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.82/0.99      | ~ v3_pre_topc(X2,X1)
% 3.82/0.99      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | ~ v2_pre_topc(X1)
% 3.82/0.99      | ~ l1_pre_topc(X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_617,plain,
% 3.82/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.82/0.99      | ~ v3_pre_topc(X2,X1)
% 3.82/0.99      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | ~ v2_pre_topc(X1)
% 3.82/0.99      | sK2 != X1 ),
% 3.82/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_36]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_618,plain,
% 3.82/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.82/0.99      | ~ v3_pre_topc(X1,sK2)
% 3.82/0.99      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ v2_pre_topc(sK2) ),
% 3.82/0.99      inference(unflattening,[status(thm)],[c_617]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_622,plain,
% 3.82/0.99      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
% 3.82/0.99      | ~ v3_pre_topc(X1,sK2)
% 3.82/0.99      | ~ v3_pre_topc(X0,sK2) ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_618,c_37]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_623,plain,
% 3.82/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.82/0.99      | ~ v3_pre_topc(X1,sK2)
% 3.82/0.99      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2)
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.82/0.99      inference(renaming,[status(thm)],[c_622]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_15443,plain,
% 3.82/0.99      ( ~ v3_pre_topc(sK5,sK2)
% 3.82/0.99      | ~ v3_pre_topc(sK4,sK2)
% 3.82/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_15284,c_623]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_15446,plain,
% 3.82/0.99      ( ~ v3_pre_topc(sK5,sK2)
% 3.82/0.99      | ~ v3_pre_topc(sK4,sK2)
% 3.82/0.99      | ~ r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_15443,c_35,c_1924,c_1926]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_7,plain,
% 3.82/0.99      ( ~ r2_hidden(X0,X1)
% 3.82/0.99      | ~ r2_hidden(X0,X2)
% 3.82/0.99      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 3.82/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_15466,plain,
% 3.82/0.99      ( ~ v3_pre_topc(sK5,sK2)
% 3.82/0.99      | ~ v3_pre_topc(sK4,sK2)
% 3.82/0.99      | ~ r2_hidden(sK3,sK5)
% 3.82/0.99      | ~ r2_hidden(sK3,sK4) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_15446,c_7]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4272,plain,
% 3.82/0.99      ( r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_18,c_34]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_29,plain,
% 3.82/0.99      ( v3_pre_topc(X0,X1)
% 3.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.82/0.99      | v2_struct_0(X1)
% 3.82/0.99      | ~ v2_pre_topc(X1)
% 3.82/0.99      | ~ l1_pre_topc(X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_545,plain,
% 3.82/0.99      ( v3_pre_topc(X0,X1)
% 3.82/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.82/0.99      | ~ v2_pre_topc(X1)
% 3.82/0.99      | ~ l1_pre_topc(X1)
% 3.82/0.99      | sK2 != X1 ),
% 3.82/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_38]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_546,plain,
% 3.82/0.99      ( v3_pre_topc(X0,sK2)
% 3.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.82/0.99      | ~ v2_pre_topc(sK2)
% 3.82/0.99      | ~ l1_pre_topc(sK2) ),
% 3.82/0.99      inference(unflattening,[status(thm)],[c_545]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_550,plain,
% 3.82/0.99      ( v3_pre_topc(X0,sK2)
% 3.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.82/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.82/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_546,c_37,c_36]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2742,plain,
% 3.82/0.99      ( v3_pre_topc(X0,sK2)
% 3.82/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.82/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.82/0.99      inference(backward_subsumption_resolution,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_2597,c_550]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4943,plain,
% 3.82/0.99      ( v3_pre_topc(sK4,sK2)
% 3.82/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_4272,c_2742]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_5287,plain,
% 3.82/0.99      ( v3_pre_topc(sK4,sK2)
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_4943,c_35]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_6179,plain,
% 3.82/0.99      ( v3_pre_topc(sK4,sK2) | v1_xboole_0(sK5) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_5674,c_5287]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4941,plain,
% 3.82/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.82/0.99      | r2_hidden(sK3,sK4)
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_4272,c_2741]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_5270,plain,
% 3.82/0.99      ( r2_hidden(sK3,sK4)
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_4941,c_35]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_6178,plain,
% 3.82/0.99      ( r2_hidden(sK3,sK4) | v1_xboole_0(sK5) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_5674,c_5270]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4932,plain,
% 3.82/0.99      ( v3_pre_topc(sK5,sK2)
% 3.82/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_4270,c_2742]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_5142,plain,
% 3.82/0.99      ( v3_pre_topc(sK5,sK2)
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_4932,c_35]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_6177,plain,
% 3.82/0.99      ( v3_pre_topc(sK5,sK2) | v1_xboole_0(sK5) ),
% 3.82/0.99      inference(resolution,[status(thm)],[c_5674,c_5142]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_8396,plain,
% 3.82/0.99      ( ~ r2_hidden(sK3,sK5)
% 3.82/0.99      | ~ r1_tarski(sK5,sK5)
% 3.82/0.99      | ~ v1_xboole_0(sK5) ),
% 3.82/0.99      inference(instantiation,[status(thm)],[c_3272]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_15560,plain,
% 3.82/0.99      ( ~ r2_hidden(sK3,sK5) ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_15466,c_3273,c_6179,c_6178,c_6177,c_8396]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_15562,plain,
% 3.82/0.99      ( r2_hidden(sK3,sK5) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_15560]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_15743,plain,
% 3.82/0.99      ( r2_hidden(X0,sK5) != iProver_top ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_4463,c_3274,c_3278,c_6183,c_15562]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_15750,plain,
% 3.82/0.99      ( r1_tarski(sK5,X0) = iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_1660,c_15743]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_0,plain,
% 3.82/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 3.82/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_2408,plain,
% 3.82/0.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_0,c_1650]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_10,plain,
% 3.82/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.82/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1652,plain,
% 3.82/0.99      ( X0 = X1
% 3.82/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.82/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4889,plain,
% 3.82/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X1
% 3.82/0.99      | r1_tarski(X1,k1_setfam_1(k2_tarski(X0,X1))) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_2408,c_1652]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_15540,plain,
% 3.82/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X1
% 3.82/0.99      | r1_tarski(X1,k1_setfam_1(k2_tarski(X1,X0))) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_0,c_4889]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_16944,plain,
% 3.82/0.99      ( k1_setfam_1(k2_tarski(X0,sK5)) = sK5 ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_15750,c_15540]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1655,plain,
% 3.82/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.82/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.82/0.99      | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1631,plain,
% 3.82/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.82/0.99      | v3_pre_topc(X1,sK2) != iProver_top
% 3.82/0.99      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK2) = iProver_top
% 3.82/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.82/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_15,plain,
% 3.82/0.99      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) ),
% 3.82/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1648,plain,
% 3.82/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.82/0.99      | v1_xboole_0(X1) != iProver_top
% 3.82/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4550,plain,
% 3.82/0.99      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.82/0.99      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top
% 3.82/0.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.82/0.99      | v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_1648,c_2928]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_6366,plain,
% 3.82/0.99      ( v3_pre_topc(sK5,sK2) != iProver_top
% 3.82/0.99      | v3_pre_topc(sK4,sK2) != iProver_top
% 3.82/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.82/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.82/0.99      | r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top
% 3.82/0.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.82/0.99      | v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_1631,c_4550]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4548,plain,
% 3.82/0.99      ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.82/0.99      | v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_1648,c_1640]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4933,plain,
% 3.82/0.99      ( v3_pre_topc(sK5,sK2) = iProver_top
% 3.82/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4932]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4944,plain,
% 3.82/0.99      ( v3_pre_topc(sK4,sK2) = iProver_top
% 3.82/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_4943]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_6369,plain,
% 3.82/0.99      ( r2_hidden(sK3,k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top
% 3.82/0.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.82/0.99      | v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_6366,c_42,c_1925,c_1927,c_4548,c_4933,c_4944]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_6376,plain,
% 3.82/0.99      ( r2_hidden(sK3,sK5) != iProver_top
% 3.82/0.99      | r2_hidden(sK3,sK4) != iProver_top
% 3.82/0.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.82/0.99      | v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_1655,c_6369]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1646,plain,
% 3.82/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.82/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.82/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_4176,plain,
% 3.82/0.99      ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_1639,c_1646]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_1634,plain,
% 3.82/0.99      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.82/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.82/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.82/0.99      | r2_hidden(X1,u1_struct_0(k9_yellow_6(sK2,X0))) != iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_5225,plain,
% 3.82/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.82/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.82/0.99      | r2_hidden(sK3,sK5) = iProver_top
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_4176,c_1634]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_5003,plain,
% 3.82/0.99      ( r2_hidden(sK3,sK5) = iProver_top
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.82/0.99      inference(predicate_to_equality,[status(thm)],[c_5001]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_8562,plain,
% 3.82/0.99      ( r2_hidden(sK3,sK5) = iProver_top
% 3.82/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_5225,c_5003]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_8568,plain,
% 3.82/0.99      ( r2_hidden(sK3,sK5) = iProver_top
% 3.82/0.99      | v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.82/0.99      inference(superposition,[status(thm)],[c_8562,c_4548]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_16344,plain,
% 3.82/0.99      ( v1_xboole_0(k1_setfam_1(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.82/0.99      inference(global_propositional_subsumption,
% 3.82/0.99                [status(thm)],
% 3.82/0.99                [c_6376,c_8568,c_15562]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(c_17765,plain,
% 3.82/0.99      ( v1_xboole_0(sK5) != iProver_top ),
% 3.82/0.99      inference(demodulation,[status(thm)],[c_16944,c_16344]) ).
% 3.82/0.99  
% 3.82/0.99  cnf(contradiction,plain,
% 3.82/0.99      ( $false ),
% 3.82/0.99      inference(minisat,[status(thm)],[c_17765,c_15562,c_6183]) ).
% 3.82/0.99  
% 3.82/0.99  
% 3.82/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.82/0.99  
% 3.82/0.99  ------                               Statistics
% 3.82/0.99  
% 3.82/0.99  ------ Selected
% 3.82/0.99  
% 3.82/0.99  total_time:                             0.472
% 3.82/0.99  
%------------------------------------------------------------------------------
