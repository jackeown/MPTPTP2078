%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:46 EST 2020

% Result     : Theorem 22.86s
% Output     : CNFRefutation 22.86s
% Verified   : 
% Statistics : Number of formulae       :  215 (1632 expanded)
%              Number of clauses        :  118 ( 349 expanded)
%              Number of leaves         :   24 ( 550 expanded)
%              Depth                    :   19
%              Number of atoms          :  826 (8657 expanded)
%              Number of equality atoms :  117 ( 410 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f107,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f95])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f89,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(definition_unfolding,[],[f74,f80])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f89])).

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

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f79,f89])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k3_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k3_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
                ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4))) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
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
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f31,f52,f51,f50,f49])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X2)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f73,f89])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,(
    ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f104,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(definition_unfolding,[],[f88,f69])).

fof(f85,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f63,f69])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f77,f89])).

fof(f14,axiom,(
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

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f76,f89])).

fof(f86,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f78,f89])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f75,f69,f89,f89])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) ) ),
    inference(definition_unfolding,[],[f71,f89])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1612,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1605,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2221,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top
    | r2_hidden(sK1(k1_setfam_1(k2_tarski(X0,X1)),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_1605])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1611,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4958,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X3) = iProver_top
    | r2_hidden(sK1(k1_setfam_1(k2_tarski(X0,X2)),X3),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_1611])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1613,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_21756,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4958,c_1613])).

cnf(c_16,plain,
    ( m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1600,plain,
    ( m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_21,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_583,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_584,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_588,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_30,c_29])).

cnf(c_18,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_604,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_588,c_18])).

cnf(c_1590,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_2104,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_1590])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1601,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4110,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2104,c_1601])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1597,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_45898,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4110,c_1597])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_967,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1848,plain,
    ( u1_struct_0(k9_yellow_6(sK3,sK4)) = u1_struct_0(k9_yellow_6(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_972,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1744,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
    | u1_struct_0(k9_yellow_6(sK3,sK4)) != X1
    | k1_setfam_1(k2_tarski(sK5,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_1847,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
    | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
    | k1_setfam_1(k2_tarski(sK5,sK6)) != X0 ),
    inference(instantiation,[status(thm)],[c_1744])).

cnf(c_1962,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
    | k1_setfam_1(k2_tarski(sK5,sK6)) != sK6 ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1984,plain,
    ( r2_hidden(sK2(sK5,sK6,sK6),sK6)
    | k1_setfam_1(k2_tarski(sK5,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1985,plain,
    ( k1_setfam_1(k2_tarski(sK5,sK6)) = sK6
    | r2_hidden(sK2(sK5,sK6,sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1984])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2373,plain,
    ( ~ r2_hidden(sK2(sK5,sK6,sK6),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2377,plain,
    ( r2_hidden(sK2(sK5,sK6,sK6),sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2373])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2838,plain,
    ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(resolution,[status(thm)],[c_14,c_26])).

cnf(c_1596,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1602,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2408,plain,
    ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1596,c_1602])).

cnf(c_2414,plain,
    ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2408])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1603,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2547,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1596,c_1603])).

cnf(c_2553,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4)))
    | v1_xboole_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2547])).

cnf(c_2955,plain,
    ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2838,c_26,c_25,c_1848,c_1962,c_1984,c_2373,c_2414,c_2553])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_30,c_29])).

cnf(c_24,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_20,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_24,c_20])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_412,c_31])).

cnf(c_515,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_30,c_29])).

cnf(c_2045,plain,
    ( m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(resolution,[status(thm)],[c_15,c_519])).

cnf(c_2123,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_540,c_2045])).

cnf(c_2124,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,X1)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0))) ),
    inference(renaming,[status(thm)],[c_2123])).

cnf(c_3033,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,sK6) ),
    inference(resolution,[status(thm)],[c_2955,c_2124])).

cnf(c_3034,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3033])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2840,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(resolution,[status(thm)],[c_14,c_27])).

cnf(c_1595,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2409,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1595,c_1602])).

cnf(c_2415,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2409])).

cnf(c_3036,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2840,c_26,c_25,c_1848,c_1962,c_1984,c_2373,c_2415,c_2553])).

cnf(c_3051,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_3036,c_2124])).

cnf(c_3052,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3051])).

cnf(c_1593,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_2750,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1596,c_1593])).

cnf(c_1712,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | m1_subset_1(sK6,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
    inference(resolution,[status(thm)],[c_519,c_26])).

cnf(c_1713,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1712])).

cnf(c_4209,plain,
    ( m1_subset_1(sK6,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2750,c_35,c_1713])).

cnf(c_4213,plain,
    ( v1_xboole_0(u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4209,c_1603])).

cnf(c_2595,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ r2_hidden(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
    inference(resolution,[status(thm)],[c_604,c_15])).

cnf(c_2058,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(resolution,[status(thm)],[c_25,c_15])).

cnf(c_5163,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
    | ~ r2_hidden(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) ),
    inference(resolution,[status(thm)],[c_2595,c_2058])).

cnf(c_1714,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | m1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
    inference(resolution,[status(thm)],[c_519,c_27])).

cnf(c_22,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_559,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_560,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_564,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_560,c_30,c_29])).

cnf(c_2238,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_564,c_2045])).

cnf(c_3030,plain,
    ( v3_pre_topc(sK6,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_2955,c_2238])).

cnf(c_3048,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_3036,c_2238])).

cnf(c_19,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_631,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_632,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_636,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
    | ~ v3_pre_topc(X1,sK3)
    | ~ v3_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_30])).

cnf(c_637,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
    inference(renaming,[status(thm)],[c_636])).

cnf(c_6582,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | v3_pre_topc(k1_setfam_1(k2_tarski(sK5,X0)),sK3)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_7913,plain,
    ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
    | ~ v3_pre_topc(sK6,sK3)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
    inference(instantiation,[status(thm)],[c_6582])).

cnf(c_9512,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
    | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5163,c_28,c_1712,c_1714,c_3030,c_3048,c_7913])).

cnf(c_3930,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,u1_struct_0(k3_yellow_1(X1)))
    | v1_xboole_0(u1_struct_0(k3_yellow_1(X1))) ),
    inference(resolution,[status(thm)],[c_16,c_14])).

cnf(c_9528,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(sK3))
    | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6)))
    | v1_xboole_0(u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
    inference(resolution,[status(thm)],[c_9512,c_3930])).

cnf(c_9529,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top
    | v1_xboole_0(u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9528])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_6564,plain,
    ( ~ r2_hidden(sK4,X0)
    | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,X0)))
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9561,plain,
    ( r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6)))
    | ~ r2_hidden(sK4,sK6)
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_6564])).

cnf(c_9562,plain,
    ( r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) = iProver_top
    | r2_hidden(sK4,sK6) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9561])).

cnf(c_64288,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_45898,c_35,c_26,c_25,c_1848,c_1962,c_1985,c_2377,c_3034,c_3052,c_4213,c_9529,c_9562])).

cnf(c_64295,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21756,c_64288])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1732,plain,
    ( m1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1714,c_28])).

cnf(c_2946,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_17,c_1732])).

cnf(c_2947,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2946])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_64295,c_2947])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:12:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 22.86/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.86/3.49  
% 22.86/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 22.86/3.49  
% 22.86/3.49  ------  iProver source info
% 22.86/3.49  
% 22.86/3.49  git: date: 2020-06-30 10:37:57 +0100
% 22.86/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 22.86/3.49  git: non_committed_changes: false
% 22.86/3.49  git: last_make_outside_of_git: false
% 22.86/3.49  
% 22.86/3.49  ------ 
% 22.86/3.49  ------ Parsing...
% 22.86/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 22.86/3.49  
% 22.86/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 22.86/3.49  
% 22.86/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 22.86/3.49  
% 22.86/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 22.86/3.49  ------ Proving...
% 22.86/3.49  ------ Problem Properties 
% 22.86/3.49  
% 22.86/3.49  
% 22.86/3.49  clauses                                 27
% 22.86/3.49  conjectures                             4
% 22.86/3.49  EPR                                     6
% 22.86/3.49  Horn                                    22
% 22.86/3.49  unary                                   4
% 22.86/3.49  binary                                  9
% 22.86/3.49  lits                                    70
% 22.86/3.49  lits eq                                 3
% 22.86/3.49  fd_pure                                 0
% 22.86/3.49  fd_pseudo                               0
% 22.86/3.49  fd_cond                                 0
% 22.86/3.49  fd_pseudo_cond                          3
% 22.86/3.49  AC symbols                              0
% 22.86/3.49  
% 22.86/3.49  ------ Input Options Time Limit: Unbounded
% 22.86/3.49  
% 22.86/3.49  
% 22.86/3.49  ------ 
% 22.86/3.49  Current options:
% 22.86/3.49  ------ 
% 22.86/3.49  
% 22.86/3.49  
% 22.86/3.49  
% 22.86/3.49  
% 22.86/3.49  ------ Proving...
% 22.86/3.49  
% 22.86/3.49  
% 22.86/3.49  % SZS status Theorem for theBenchmark.p
% 22.86/3.49  
% 22.86/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 22.86/3.49  
% 22.86/3.49  fof(f2,axiom,(
% 22.86/3.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f17,plain,(
% 22.86/3.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 22.86/3.49    inference(ennf_transformation,[],[f2])).
% 22.86/3.49  
% 22.86/3.49  fof(f36,plain,(
% 22.86/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 22.86/3.49    inference(nnf_transformation,[],[f17])).
% 22.86/3.49  
% 22.86/3.49  fof(f37,plain,(
% 22.86/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 22.86/3.49    inference(rectify,[],[f36])).
% 22.86/3.49  
% 22.86/3.49  fof(f38,plain,(
% 22.86/3.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 22.86/3.49    introduced(choice_axiom,[])).
% 22.86/3.49  
% 22.86/3.49  fof(f39,plain,(
% 22.86/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 22.86/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 22.86/3.49  
% 22.86/3.49  fof(f57,plain,(
% 22.86/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f39])).
% 22.86/3.49  
% 22.86/3.49  fof(f3,axiom,(
% 22.86/3.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f40,plain,(
% 22.86/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 22.86/3.49    inference(nnf_transformation,[],[f3])).
% 22.86/3.49  
% 22.86/3.49  fof(f41,plain,(
% 22.86/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 22.86/3.49    inference(flattening,[],[f40])).
% 22.86/3.49  
% 22.86/3.49  fof(f42,plain,(
% 22.86/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 22.86/3.49    inference(rectify,[],[f41])).
% 22.86/3.49  
% 22.86/3.49  fof(f43,plain,(
% 22.86/3.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 22.86/3.49    introduced(choice_axiom,[])).
% 22.86/3.49  
% 22.86/3.49  fof(f44,plain,(
% 22.86/3.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 22.86/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 22.86/3.49  
% 22.86/3.49  fof(f59,plain,(
% 22.86/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 22.86/3.49    inference(cnf_transformation,[],[f44])).
% 22.86/3.49  
% 22.86/3.49  fof(f5,axiom,(
% 22.86/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f69,plain,(
% 22.86/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 22.86/3.49    inference(cnf_transformation,[],[f5])).
% 22.86/3.49  
% 22.86/3.49  fof(f95,plain,(
% 22.86/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 22.86/3.49    inference(definition_unfolding,[],[f59,f69])).
% 22.86/3.49  
% 22.86/3.49  fof(f107,plain,(
% 22.86/3.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 22.86/3.49    inference(equality_resolution,[],[f95])).
% 22.86/3.49  
% 22.86/3.49  fof(f56,plain,(
% 22.86/3.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f39])).
% 22.86/3.49  
% 22.86/3.49  fof(f58,plain,(
% 22.86/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f39])).
% 22.86/3.49  
% 22.86/3.49  fof(f7,axiom,(
% 22.86/3.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f46,plain,(
% 22.86/3.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 22.86/3.49    inference(nnf_transformation,[],[f7])).
% 22.86/3.49  
% 22.86/3.49  fof(f72,plain,(
% 22.86/3.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f46])).
% 22.86/3.49  
% 22.86/3.49  fof(f9,axiom,(
% 22.86/3.49    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f74,plain,(
% 22.86/3.49    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f9])).
% 22.86/3.49  
% 22.86/3.49  fof(f13,axiom,(
% 22.86/3.49    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f80,plain,(
% 22.86/3.49    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 22.86/3.49    inference(cnf_transformation,[],[f13])).
% 22.86/3.49  
% 22.86/3.49  fof(f89,plain,(
% 22.86/3.49    ( ! [X0] : (k1_zfmisc_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 22.86/3.49    inference(definition_unfolding,[],[f74,f80])).
% 22.86/3.49  
% 22.86/3.49  fof(f96,plain,(
% 22.86/3.49    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) | ~r1_tarski(X0,X1)) )),
% 22.86/3.49    inference(definition_unfolding,[],[f72,f89])).
% 22.86/3.49  
% 22.86/3.49  fof(f12,axiom,(
% 22.86/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f26,plain,(
% 22.86/3.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 22.86/3.49    inference(ennf_transformation,[],[f12])).
% 22.86/3.49  
% 22.86/3.49  fof(f27,plain,(
% 22.86/3.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 22.86/3.49    inference(flattening,[],[f26])).
% 22.86/3.49  
% 22.86/3.49  fof(f47,plain,(
% 22.86/3.49    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 22.86/3.49    inference(nnf_transformation,[],[f27])).
% 22.86/3.49  
% 22.86/3.49  fof(f48,plain,(
% 22.86/3.49    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 22.86/3.49    inference(flattening,[],[f47])).
% 22.86/3.49  
% 22.86/3.49  fof(f79,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f48])).
% 22.86/3.49  
% 22.86/3.49  fof(f101,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 22.86/3.49    inference(definition_unfolding,[],[f79,f89])).
% 22.86/3.49  
% 22.86/3.49  fof(f15,conjecture,(
% 22.86/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f16,negated_conjecture,(
% 22.86/3.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 22.86/3.49    inference(negated_conjecture,[],[f15])).
% 22.86/3.49  
% 22.86/3.49  fof(f30,plain,(
% 22.86/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 22.86/3.49    inference(ennf_transformation,[],[f16])).
% 22.86/3.49  
% 22.86/3.49  fof(f31,plain,(
% 22.86/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 22.86/3.49    inference(flattening,[],[f30])).
% 22.86/3.49  
% 22.86/3.49  fof(f52,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k3_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 22.86/3.49    introduced(choice_axiom,[])).
% 22.86/3.49  
% 22.86/3.49  fof(f51,plain,(
% 22.86/3.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 22.86/3.49    introduced(choice_axiom,[])).
% 22.86/3.49  
% 22.86/3.49  fof(f50,plain,(
% 22.86/3.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 22.86/3.49    introduced(choice_axiom,[])).
% 22.86/3.49  
% 22.86/3.49  fof(f49,plain,(
% 22.86/3.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 22.86/3.49    introduced(choice_axiom,[])).
% 22.86/3.49  
% 22.86/3.49  fof(f53,plain,(
% 22.86/3.49    (((~m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 22.86/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f31,f52,f51,f50,f49])).
% 22.86/3.49  
% 22.86/3.49  fof(f82,plain,(
% 22.86/3.49    ~v2_struct_0(sK3)),
% 22.86/3.49    inference(cnf_transformation,[],[f53])).
% 22.86/3.49  
% 22.86/3.49  fof(f83,plain,(
% 22.86/3.49    v2_pre_topc(sK3)),
% 22.86/3.49    inference(cnf_transformation,[],[f53])).
% 22.86/3.49  
% 22.86/3.49  fof(f84,plain,(
% 22.86/3.49    l1_pre_topc(sK3)),
% 22.86/3.49    inference(cnf_transformation,[],[f53])).
% 22.86/3.49  
% 22.86/3.49  fof(f8,axiom,(
% 22.86/3.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f20,plain,(
% 22.86/3.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 22.86/3.49    inference(ennf_transformation,[],[f8])).
% 22.86/3.49  
% 22.86/3.49  fof(f21,plain,(
% 22.86/3.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 22.86/3.49    inference(flattening,[],[f20])).
% 22.86/3.49  
% 22.86/3.49  fof(f73,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f21])).
% 22.86/3.49  
% 22.86/3.49  fof(f98,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X2))) | ~r2_hidden(X0,X1)) )),
% 22.86/3.49    inference(definition_unfolding,[],[f73,f89])).
% 22.86/3.49  
% 22.86/3.49  fof(f6,axiom,(
% 22.86/3.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f19,plain,(
% 22.86/3.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 22.86/3.49    inference(ennf_transformation,[],[f6])).
% 22.86/3.49  
% 22.86/3.49  fof(f70,plain,(
% 22.86/3.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f19])).
% 22.86/3.49  
% 22.86/3.49  fof(f88,plain,(
% 22.86/3.49    ~m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 22.86/3.49    inference(cnf_transformation,[],[f53])).
% 22.86/3.49  
% 22.86/3.49  fof(f104,plain,(
% 22.86/3.49    ~m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 22.86/3.49    inference(definition_unfolding,[],[f88,f69])).
% 22.86/3.49  
% 22.86/3.49  fof(f85,plain,(
% 22.86/3.49    m1_subset_1(sK4,u1_struct_0(sK3))),
% 22.86/3.49    inference(cnf_transformation,[],[f53])).
% 22.86/3.49  
% 22.86/3.49  fof(f87,plain,(
% 22.86/3.49    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 22.86/3.49    inference(cnf_transformation,[],[f53])).
% 22.86/3.49  
% 22.86/3.49  fof(f63,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f44])).
% 22.86/3.49  
% 22.86/3.49  fof(f91,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 22.86/3.49    inference(definition_unfolding,[],[f63,f69])).
% 22.86/3.49  
% 22.86/3.49  fof(f1,axiom,(
% 22.86/3.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f32,plain,(
% 22.86/3.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 22.86/3.49    inference(nnf_transformation,[],[f1])).
% 22.86/3.49  
% 22.86/3.49  fof(f33,plain,(
% 22.86/3.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 22.86/3.49    inference(rectify,[],[f32])).
% 22.86/3.49  
% 22.86/3.49  fof(f34,plain,(
% 22.86/3.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 22.86/3.49    introduced(choice_axiom,[])).
% 22.86/3.49  
% 22.86/3.49  fof(f35,plain,(
% 22.86/3.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 22.86/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 22.86/3.49  
% 22.86/3.49  fof(f54,plain,(
% 22.86/3.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f35])).
% 22.86/3.49  
% 22.86/3.49  fof(f4,axiom,(
% 22.86/3.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f18,plain,(
% 22.86/3.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 22.86/3.49    inference(ennf_transformation,[],[f4])).
% 22.86/3.49  
% 22.86/3.49  fof(f45,plain,(
% 22.86/3.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 22.86/3.49    inference(nnf_transformation,[],[f18])).
% 22.86/3.49  
% 22.86/3.49  fof(f65,plain,(
% 22.86/3.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f45])).
% 22.86/3.49  
% 22.86/3.49  fof(f67,plain,(
% 22.86/3.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f45])).
% 22.86/3.49  
% 22.86/3.49  fof(f77,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f48])).
% 22.86/3.49  
% 22.86/3.49  fof(f103,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 22.86/3.49    inference(definition_unfolding,[],[f77,f89])).
% 22.86/3.49  
% 22.86/3.49  fof(f14,axiom,(
% 22.86/3.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f28,plain,(
% 22.86/3.49    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 22.86/3.49    inference(ennf_transformation,[],[f14])).
% 22.86/3.49  
% 22.86/3.49  fof(f29,plain,(
% 22.86/3.49    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 22.86/3.49    inference(flattening,[],[f28])).
% 22.86/3.49  
% 22.86/3.49  fof(f81,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f29])).
% 22.86/3.49  
% 22.86/3.49  fof(f11,axiom,(
% 22.86/3.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f24,plain,(
% 22.86/3.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 22.86/3.49    inference(ennf_transformation,[],[f11])).
% 22.86/3.49  
% 22.86/3.49  fof(f25,plain,(
% 22.86/3.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 22.86/3.49    inference(flattening,[],[f24])).
% 22.86/3.49  
% 22.86/3.49  fof(f76,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f25])).
% 22.86/3.49  
% 22.86/3.49  fof(f100,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 22.86/3.49    inference(definition_unfolding,[],[f76,f89])).
% 22.86/3.49  
% 22.86/3.49  fof(f86,plain,(
% 22.86/3.49    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 22.86/3.49    inference(cnf_transformation,[],[f53])).
% 22.86/3.49  
% 22.86/3.49  fof(f78,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f48])).
% 22.86/3.49  
% 22.86/3.49  fof(f102,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 22.86/3.49    inference(definition_unfolding,[],[f78,f89])).
% 22.86/3.49  
% 22.86/3.49  fof(f10,axiom,(
% 22.86/3.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 22.86/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 22.86/3.49  
% 22.86/3.49  fof(f22,plain,(
% 22.86/3.49    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 22.86/3.49    inference(ennf_transformation,[],[f10])).
% 22.86/3.49  
% 22.86/3.49  fof(f23,plain,(
% 22.86/3.49    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 22.86/3.49    inference(flattening,[],[f22])).
% 22.86/3.49  
% 22.86/3.49  fof(f75,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 22.86/3.49    inference(cnf_transformation,[],[f23])).
% 22.86/3.49  
% 22.86/3.49  fof(f99,plain,(
% 22.86/3.49    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 22.86/3.49    inference(definition_unfolding,[],[f75,f69,f89,f89])).
% 22.86/3.49  
% 22.86/3.49  fof(f61,plain,(
% 22.86/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 22.86/3.49    inference(cnf_transformation,[],[f44])).
% 22.86/3.49  
% 22.86/3.49  fof(f93,plain,(
% 22.86/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 22.86/3.49    inference(definition_unfolding,[],[f61,f69])).
% 22.86/3.49  
% 22.86/3.49  fof(f105,plain,(
% 22.86/3.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 22.86/3.49    inference(equality_resolution,[],[f93])).
% 22.86/3.49  
% 22.86/3.49  fof(f71,plain,(
% 22.86/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 22.86/3.49    inference(cnf_transformation,[],[f46])).
% 22.86/3.49  
% 22.86/3.49  fof(f97,plain,(
% 22.86/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))) )),
% 22.86/3.49    inference(definition_unfolding,[],[f71,f89])).
% 22.86/3.49  
% 22.86/3.49  cnf(c_3,plain,
% 22.86/3.49      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 22.86/3.49      inference(cnf_transformation,[],[f57]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1612,plain,
% 22.86/3.49      ( r1_tarski(X0,X1) = iProver_top
% 22.86/3.49      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_10,plain,
% 22.86/3.49      ( r2_hidden(X0,X1)
% 22.86/3.49      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 22.86/3.49      inference(cnf_transformation,[],[f107]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1605,plain,
% 22.86/3.49      ( r2_hidden(X0,X1) = iProver_top
% 22.86/3.49      | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2221,plain,
% 22.86/3.49      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top
% 22.86/3.49      | r2_hidden(sK1(k1_setfam_1(k2_tarski(X0,X1)),X2),X0) = iProver_top ),
% 22.86/3.49      inference(superposition,[status(thm)],[c_1612,c_1605]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_4,plain,
% 22.86/3.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f56]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1611,plain,
% 22.86/3.49      ( r1_tarski(X0,X1) != iProver_top
% 22.86/3.49      | r2_hidden(X2,X0) != iProver_top
% 22.86/3.49      | r2_hidden(X2,X1) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_4958,plain,
% 22.86/3.49      ( r1_tarski(X0,X1) != iProver_top
% 22.86/3.49      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X3) = iProver_top
% 22.86/3.49      | r2_hidden(sK1(k1_setfam_1(k2_tarski(X0,X2)),X3),X1) = iProver_top ),
% 22.86/3.49      inference(superposition,[status(thm)],[c_2221,c_1611]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2,plain,
% 22.86/3.49      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f58]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1613,plain,
% 22.86/3.49      ( r1_tarski(X0,X1) = iProver_top
% 22.86/3.49      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_21756,plain,
% 22.86/3.49      ( r1_tarski(X0,X1) != iProver_top
% 22.86/3.49      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) = iProver_top ),
% 22.86/3.49      inference(superposition,[status(thm)],[c_4958,c_1613]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_16,plain,
% 22.86/3.49      ( m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
% 22.86/3.49      | ~ r1_tarski(X0,X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f96]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1600,plain,
% 22.86/3.49      ( m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) = iProver_top
% 22.86/3.49      | r1_tarski(X0,X1) != iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_21,plain,
% 22.86/3.49      ( ~ v3_pre_topc(X0,X1)
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | ~ r2_hidden(X2,X0)
% 22.86/3.49      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 22.86/3.49      | v2_struct_0(X1)
% 22.86/3.49      | ~ v2_pre_topc(X1)
% 22.86/3.49      | ~ l1_pre_topc(X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f101]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_31,negated_conjecture,
% 22.86/3.49      ( ~ v2_struct_0(sK3) ),
% 22.86/3.49      inference(cnf_transformation,[],[f82]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_583,plain,
% 22.86/3.49      ( ~ v3_pre_topc(X0,X1)
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | ~ r2_hidden(X2,X0)
% 22.86/3.49      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 22.86/3.49      | ~ v2_pre_topc(X1)
% 22.86/3.49      | ~ l1_pre_topc(X1)
% 22.86/3.49      | sK3 != X1 ),
% 22.86/3.49      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_584,plain,
% 22.86/3.49      ( ~ v3_pre_topc(X0,sK3)
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 22.86/3.49      | ~ r2_hidden(X1,X0)
% 22.86/3.49      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 22.86/3.49      | ~ v2_pre_topc(sK3)
% 22.86/3.49      | ~ l1_pre_topc(sK3) ),
% 22.86/3.49      inference(unflattening,[status(thm)],[c_583]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_30,negated_conjecture,
% 22.86/3.49      ( v2_pre_topc(sK3) ),
% 22.86/3.49      inference(cnf_transformation,[],[f83]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_29,negated_conjecture,
% 22.86/3.49      ( l1_pre_topc(sK3) ),
% 22.86/3.49      inference(cnf_transformation,[],[f84]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_588,plain,
% 22.86/3.49      ( ~ v3_pre_topc(X0,sK3)
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 22.86/3.49      | ~ r2_hidden(X1,X0)
% 22.86/3.49      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_584,c_30,c_29]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_18,plain,
% 22.86/3.49      ( m1_subset_1(X0,X1)
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
% 22.86/3.49      | ~ r2_hidden(X0,X2) ),
% 22.86/3.49      inference(cnf_transformation,[],[f98]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_604,plain,
% 22.86/3.49      ( ~ v3_pre_topc(X0,sK3)
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ r2_hidden(X1,X0)
% 22.86/3.49      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 22.86/3.49      inference(forward_subsumption_resolution,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_588,c_18]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1590,plain,
% 22.86/3.49      ( v3_pre_topc(X0,sK3) != iProver_top
% 22.86/3.49      | m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) != iProver_top
% 22.86/3.49      | r2_hidden(X1,X0) != iProver_top
% 22.86/3.49      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2104,plain,
% 22.86/3.49      ( v3_pre_topc(X0,sK3) != iProver_top
% 22.86/3.49      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 22.86/3.49      | r2_hidden(X1,X0) != iProver_top
% 22.86/3.49      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
% 22.86/3.49      inference(superposition,[status(thm)],[c_1600,c_1590]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_15,plain,
% 22.86/3.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f70]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1601,plain,
% 22.86/3.49      ( m1_subset_1(X0,X1) = iProver_top
% 22.86/3.49      | r2_hidden(X0,X1) != iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_4110,plain,
% 22.86/3.49      ( v3_pre_topc(X0,sK3) != iProver_top
% 22.86/3.49      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
% 22.86/3.49      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 22.86/3.49      | r2_hidden(X1,X0) != iProver_top ),
% 22.86/3.49      inference(superposition,[status(thm)],[c_2104,c_1601]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_25,negated_conjecture,
% 22.86/3.49      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 22.86/3.49      inference(cnf_transformation,[],[f104]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1597,plain,
% 22.86/3.49      ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_45898,plain,
% 22.86/3.49      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) != iProver_top
% 22.86/3.49      | r1_tarski(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(sK3)) != iProver_top
% 22.86/3.49      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top ),
% 22.86/3.49      inference(superposition,[status(thm)],[c_4110,c_1597]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_28,negated_conjecture,
% 22.86/3.49      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 22.86/3.49      inference(cnf_transformation,[],[f85]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_35,plain,
% 22.86/3.49      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_26,negated_conjecture,
% 22.86/3.49      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 22.86/3.49      inference(cnf_transformation,[],[f87]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_967,plain,( X0 = X0 ),theory(equality) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1848,plain,
% 22.86/3.49      ( u1_struct_0(k9_yellow_6(sK3,sK4)) = u1_struct_0(k9_yellow_6(sK3,sK4)) ),
% 22.86/3.49      inference(instantiation,[status(thm)],[c_967]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_972,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 22.86/3.49      theory(equality) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1744,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,X1)
% 22.86/3.49      | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
% 22.86/3.49      | u1_struct_0(k9_yellow_6(sK3,sK4)) != X1
% 22.86/3.49      | k1_setfam_1(k2_tarski(sK5,sK6)) != X0 ),
% 22.86/3.49      inference(instantiation,[status(thm)],[c_972]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1847,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 22.86/3.49      | m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
% 22.86/3.49      | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
% 22.86/3.49      | k1_setfam_1(k2_tarski(sK5,sK6)) != X0 ),
% 22.86/3.49      inference(instantiation,[status(thm)],[c_1744]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1962,plain,
% 22.86/3.49      ( m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))
% 22.86/3.49      | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 22.86/3.49      | u1_struct_0(k9_yellow_6(sK3,sK4)) != u1_struct_0(k9_yellow_6(sK3,sK4))
% 22.86/3.49      | k1_setfam_1(k2_tarski(sK5,sK6)) != sK6 ),
% 22.86/3.49      inference(instantiation,[status(thm)],[c_1847]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_6,plain,
% 22.86/3.49      ( r2_hidden(sK2(X0,X1,X2),X1)
% 22.86/3.49      | r2_hidden(sK2(X0,X1,X2),X2)
% 22.86/3.49      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
% 22.86/3.49      inference(cnf_transformation,[],[f91]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1984,plain,
% 22.86/3.49      ( r2_hidden(sK2(sK5,sK6,sK6),sK6)
% 22.86/3.49      | k1_setfam_1(k2_tarski(sK5,sK6)) = sK6 ),
% 22.86/3.49      inference(instantiation,[status(thm)],[c_6]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1985,plain,
% 22.86/3.49      ( k1_setfam_1(k2_tarski(sK5,sK6)) = sK6
% 22.86/3.49      | r2_hidden(sK2(sK5,sK6,sK6),sK6) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_1984]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1,plain,
% 22.86/3.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f54]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2373,plain,
% 22.86/3.49      ( ~ r2_hidden(sK2(sK5,sK6,sK6),sK6) | ~ v1_xboole_0(sK6) ),
% 22.86/3.49      inference(instantiation,[status(thm)],[c_1]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2377,plain,
% 22.86/3.49      ( r2_hidden(sK2(sK5,sK6,sK6),sK6) != iProver_top
% 22.86/3.49      | v1_xboole_0(sK6) != iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_2373]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_14,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f65]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2838,plain,
% 22.86/3.49      ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 22.86/3.49      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_14,c_26]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1596,plain,
% 22.86/3.49      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1602,plain,
% 22.86/3.49      ( m1_subset_1(X0,X1) != iProver_top
% 22.86/3.49      | r2_hidden(X0,X1) = iProver_top
% 22.86/3.49      | v1_xboole_0(X1) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2408,plain,
% 22.86/3.49      ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
% 22.86/3.49      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 22.86/3.49      inference(superposition,[status(thm)],[c_1596,c_1602]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2414,plain,
% 22.86/3.49      ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 22.86/3.49      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 22.86/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_2408]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_12,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 22.86/3.49      inference(cnf_transformation,[],[f67]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1603,plain,
% 22.86/3.49      ( m1_subset_1(X0,X1) != iProver_top
% 22.86/3.49      | v1_xboole_0(X1) != iProver_top
% 22.86/3.49      | v1_xboole_0(X0) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2547,plain,
% 22.86/3.49      ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 22.86/3.49      | v1_xboole_0(sK6) = iProver_top ),
% 22.86/3.49      inference(superposition,[status(thm)],[c_1596,c_1603]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2553,plain,
% 22.86/3.49      ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4)))
% 22.86/3.49      | v1_xboole_0(sK6) ),
% 22.86/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_2547]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2955,plain,
% 22.86/3.49      ( r2_hidden(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_2838,c_26,c_25,c_1848,c_1962,c_1984,c_2373,c_2414,
% 22.86/3.49                 c_2553]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_23,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | r2_hidden(X0,X2)
% 22.86/3.49      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 22.86/3.49      | v2_struct_0(X1)
% 22.86/3.49      | ~ v2_pre_topc(X1)
% 22.86/3.49      | ~ l1_pre_topc(X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f103]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_535,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | r2_hidden(X0,X2)
% 22.86/3.49      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 22.86/3.49      | ~ v2_pre_topc(X1)
% 22.86/3.49      | ~ l1_pre_topc(X1)
% 22.86/3.49      | sK3 != X1 ),
% 22.86/3.49      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_536,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 22.86/3.49      | r2_hidden(X1,X0)
% 22.86/3.49      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 22.86/3.49      | ~ v2_pre_topc(sK3)
% 22.86/3.49      | ~ l1_pre_topc(sK3) ),
% 22.86/3.49      inference(unflattening,[status(thm)],[c_535]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_540,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 22.86/3.49      | r2_hidden(X1,X0)
% 22.86/3.49      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_536,c_30,c_29]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_24,plain,
% 22.86/3.49      ( m1_connsp_2(X0,X1,X2)
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 22.86/3.49      | v2_struct_0(X1)
% 22.86/3.49      | ~ v2_pre_topc(X1)
% 22.86/3.49      | ~ l1_pre_topc(X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f81]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_20,plain,
% 22.86/3.49      ( ~ m1_connsp_2(X0,X1,X2)
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 22.86/3.49      | m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | v2_struct_0(X1)
% 22.86/3.49      | ~ v2_pre_topc(X1)
% 22.86/3.49      | ~ l1_pre_topc(X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f100]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_412,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 22.86/3.49      | m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | v2_struct_0(X1)
% 22.86/3.49      | ~ v2_pre_topc(X1)
% 22.86/3.49      | ~ l1_pre_topc(X1) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_24,c_20]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_514,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 22.86/3.49      | m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | ~ v2_pre_topc(X1)
% 22.86/3.49      | ~ l1_pre_topc(X1)
% 22.86/3.49      | sK3 != X1 ),
% 22.86/3.49      inference(resolution_lifted,[status(thm)],[c_412,c_31]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_515,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 22.86/3.49      | m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 22.86/3.49      | ~ v2_pre_topc(sK3)
% 22.86/3.49      | ~ l1_pre_topc(sK3) ),
% 22.86/3.49      inference(unflattening,[status(thm)],[c_514]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_519,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 22.86/3.49      | m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_515,c_30,c_29]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2045,plain,
% 22.86/3.49      ( m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 22.86/3.49      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_15,c_519]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2123,plain,
% 22.86/3.49      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
% 22.86/3.49      | r2_hidden(X1,X0)
% 22.86/3.49      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_540,c_2045]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2124,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 22.86/3.49      | r2_hidden(X0,X1)
% 22.86/3.49      | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(sK3,X0))) ),
% 22.86/3.49      inference(renaming,[status(thm)],[c_2123]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_3033,plain,
% 22.86/3.49      ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) | r2_hidden(sK4,sK6) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_2955,c_2124]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_3034,plain,
% 22.86/3.49      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 22.86/3.49      | r2_hidden(sK4,sK6) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_3033]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_27,negated_conjecture,
% 22.86/3.49      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 22.86/3.49      inference(cnf_transformation,[],[f86]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2840,plain,
% 22.86/3.49      ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 22.86/3.49      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_14,c_27]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1595,plain,
% 22.86/3.49      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2409,plain,
% 22.86/3.49      ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top
% 22.86/3.49      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 22.86/3.49      inference(superposition,[status(thm)],[c_1595,c_1602]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2415,plain,
% 22.86/3.49      ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 22.86/3.49      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 22.86/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_2409]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_3036,plain,
% 22.86/3.49      ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_2840,c_26,c_25,c_1848,c_1962,c_1984,c_2373,c_2415,
% 22.86/3.49                 c_2553]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_3051,plain,
% 22.86/3.49      ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) | r2_hidden(sK4,sK5) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_3036,c_2124]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_3052,plain,
% 22.86/3.49      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 22.86/3.49      | r2_hidden(sK4,sK5) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_3051]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1593,plain,
% 22.86/3.49      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
% 22.86/3.49      | m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) = iProver_top
% 22.86/3.49      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2750,plain,
% 22.86/3.49      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 22.86/3.49      | m1_subset_1(sK6,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) = iProver_top ),
% 22.86/3.49      inference(superposition,[status(thm)],[c_1596,c_1593]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1712,plain,
% 22.86/3.49      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 22.86/3.49      | m1_subset_1(sK6,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_519,c_26]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1713,plain,
% 22.86/3.49      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 22.86/3.49      | m1_subset_1(sK6,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_1712]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_4209,plain,
% 22.86/3.49      ( m1_subset_1(sK6,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) = iProver_top ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_2750,c_35,c_1713]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_4213,plain,
% 22.86/3.49      ( v1_xboole_0(u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) != iProver_top
% 22.86/3.49      | v1_xboole_0(sK6) = iProver_top ),
% 22.86/3.49      inference(superposition,[status(thm)],[c_4209,c_1603]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2595,plain,
% 22.86/3.49      ( ~ v3_pre_topc(X0,sK3)
% 22.86/3.49      | ~ r2_hidden(X1,X0)
% 22.86/3.49      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 22.86/3.49      | ~ r2_hidden(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_604,c_15]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2058,plain,
% 22.86/3.49      ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_25,c_15]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_5163,plain,
% 22.86/3.49      ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
% 22.86/3.49      | ~ r2_hidden(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_2595,c_2058]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1714,plain,
% 22.86/3.49      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 22.86/3.49      | m1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_519,c_27]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_22,plain,
% 22.86/3.49      ( v3_pre_topc(X0,X1)
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 22.86/3.49      | v2_struct_0(X1)
% 22.86/3.49      | ~ v2_pre_topc(X1)
% 22.86/3.49      | ~ l1_pre_topc(X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f102]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_559,plain,
% 22.86/3.49      ( v3_pre_topc(X0,X1)
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 22.86/3.49      | ~ v2_pre_topc(X1)
% 22.86/3.49      | ~ l1_pre_topc(X1)
% 22.86/3.49      | sK3 != X1 ),
% 22.86/3.49      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_560,plain,
% 22.86/3.49      ( v3_pre_topc(X0,sK3)
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 22.86/3.49      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 22.86/3.49      | ~ v2_pre_topc(sK3)
% 22.86/3.49      | ~ l1_pre_topc(sK3) ),
% 22.86/3.49      inference(unflattening,[status(thm)],[c_559]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_564,plain,
% 22.86/3.49      ( v3_pre_topc(X0,sK3)
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 22.86/3.49      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_560,c_30,c_29]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2238,plain,
% 22.86/3.49      ( v3_pre_topc(X0,sK3)
% 22.86/3.49      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 22.86/3.49      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_564,c_2045]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_3030,plain,
% 22.86/3.49      ( v3_pre_topc(sK6,sK3) | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_2955,c_2238]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_3048,plain,
% 22.86/3.49      ( v3_pre_topc(sK5,sK3) | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_3036,c_2238]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_19,plain,
% 22.86/3.49      ( ~ v3_pre_topc(X0,X1)
% 22.86/3.49      | ~ v3_pre_topc(X2,X1)
% 22.86/3.49      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | ~ v2_pre_topc(X1)
% 22.86/3.49      | ~ l1_pre_topc(X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f99]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_631,plain,
% 22.86/3.49      ( ~ v3_pre_topc(X0,X1)
% 22.86/3.49      | ~ v3_pre_topc(X2,X1)
% 22.86/3.49      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
% 22.86/3.49      | ~ v2_pre_topc(X1)
% 22.86/3.49      | sK3 != X1 ),
% 22.86/3.49      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_632,plain,
% 22.86/3.49      ( ~ v3_pre_topc(X0,sK3)
% 22.86/3.49      | ~ v3_pre_topc(X1,sK3)
% 22.86/3.49      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ v2_pre_topc(sK3) ),
% 22.86/3.49      inference(unflattening,[status(thm)],[c_631]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_636,plain,
% 22.86/3.49      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
% 22.86/3.49      | ~ v3_pre_topc(X1,sK3)
% 22.86/3.49      | ~ v3_pre_topc(X0,sK3) ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_632,c_30]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_637,plain,
% 22.86/3.49      ( ~ v3_pre_topc(X0,sK3)
% 22.86/3.49      | ~ v3_pre_topc(X1,sK3)
% 22.86/3.49      | v3_pre_topc(k1_setfam_1(k2_tarski(X1,X0)),sK3)
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
% 22.86/3.49      inference(renaming,[status(thm)],[c_636]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_6582,plain,
% 22.86/3.49      ( ~ v3_pre_topc(X0,sK3)
% 22.86/3.49      | v3_pre_topc(k1_setfam_1(k2_tarski(sK5,X0)),sK3)
% 22.86/3.49      | ~ v3_pre_topc(sK5,sK3)
% 22.86/3.49      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
% 22.86/3.49      inference(instantiation,[status(thm)],[c_637]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_7913,plain,
% 22.86/3.49      ( v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
% 22.86/3.49      | ~ v3_pre_topc(sK6,sK3)
% 22.86/3.49      | ~ v3_pre_topc(sK5,sK3)
% 22.86/3.49      | ~ m1_subset_1(sK6,u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ m1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
% 22.86/3.49      inference(instantiation,[status(thm)],[c_6582]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_9512,plain,
% 22.86/3.49      ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k3_yellow_1(u1_struct_0(sK3))))
% 22.86/3.49      | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_5163,c_28,c_1712,c_1714,c_3030,c_3048,c_7913]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_3930,plain,
% 22.86/3.49      ( ~ r1_tarski(X0,X1)
% 22.86/3.49      | r2_hidden(X0,u1_struct_0(k3_yellow_1(X1)))
% 22.86/3.49      | v1_xboole_0(u1_struct_0(k3_yellow_1(X1))) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_16,c_14]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_9528,plain,
% 22.86/3.49      ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(sK3))
% 22.86/3.49      | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6)))
% 22.86/3.49      | v1_xboole_0(u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_9512,c_3930]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_9529,plain,
% 22.86/3.49      ( r1_tarski(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(sK3)) != iProver_top
% 22.86/3.49      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) != iProver_top
% 22.86/3.49      | v1_xboole_0(u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_9528]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_8,plain,
% 22.86/3.49      ( ~ r2_hidden(X0,X1)
% 22.86/3.49      | ~ r2_hidden(X0,X2)
% 22.86/3.49      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 22.86/3.49      inference(cnf_transformation,[],[f105]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_6564,plain,
% 22.86/3.49      ( ~ r2_hidden(sK4,X0)
% 22.86/3.49      | r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,X0)))
% 22.86/3.49      | ~ r2_hidden(sK4,sK5) ),
% 22.86/3.49      inference(instantiation,[status(thm)],[c_8]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_9561,plain,
% 22.86/3.49      ( r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6)))
% 22.86/3.49      | ~ r2_hidden(sK4,sK6)
% 22.86/3.49      | ~ r2_hidden(sK4,sK5) ),
% 22.86/3.49      inference(instantiation,[status(thm)],[c_6564]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_9562,plain,
% 22.86/3.49      ( r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) = iProver_top
% 22.86/3.49      | r2_hidden(sK4,sK6) != iProver_top
% 22.86/3.49      | r2_hidden(sK4,sK5) != iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_9561]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_64288,plain,
% 22.86/3.49      ( r1_tarski(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(sK3)) != iProver_top ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_45898,c_35,c_26,c_25,c_1848,c_1962,c_1985,c_2377,
% 22.86/3.49                 c_3034,c_3052,c_4213,c_9529,c_9562]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_64295,plain,
% 22.86/3.49      ( r1_tarski(sK5,u1_struct_0(sK3)) != iProver_top ),
% 22.86/3.49      inference(superposition,[status(thm)],[c_21756,c_64288]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_17,plain,
% 22.86/3.49      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
% 22.86/3.49      | r1_tarski(X0,X1) ),
% 22.86/3.49      inference(cnf_transformation,[],[f97]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_1732,plain,
% 22.86/3.49      ( m1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK3)))) ),
% 22.86/3.49      inference(global_propositional_subsumption,
% 22.86/3.49                [status(thm)],
% 22.86/3.49                [c_1714,c_28]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2946,plain,
% 22.86/3.49      ( r1_tarski(sK5,u1_struct_0(sK3)) ),
% 22.86/3.49      inference(resolution,[status(thm)],[c_17,c_1732]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(c_2947,plain,
% 22.86/3.49      ( r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top ),
% 22.86/3.49      inference(predicate_to_equality,[status(thm)],[c_2946]) ).
% 22.86/3.49  
% 22.86/3.49  cnf(contradiction,plain,
% 22.86/3.49      ( $false ),
% 22.86/3.49      inference(minisat,[status(thm)],[c_64295,c_2947]) ).
% 22.86/3.49  
% 22.86/3.49  
% 22.86/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 22.86/3.49  
% 22.86/3.49  ------                               Statistics
% 22.86/3.49  
% 22.86/3.49  ------ Selected
% 22.86/3.49  
% 22.86/3.49  total_time:                             2.55
% 22.86/3.49  
%------------------------------------------------------------------------------
