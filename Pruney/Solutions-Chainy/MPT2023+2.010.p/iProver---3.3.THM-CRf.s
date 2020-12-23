%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:47 EST 2020

% Result     : Theorem 11.32s
% Output     : CNFRefutation 11.32s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 747 expanded)
%              Number of clauses        :   90 ( 170 expanded)
%              Number of leaves         :   22 ( 268 expanded)
%              Depth                    :   20
%              Number of atoms          :  692 (4508 expanded)
%              Number of equality atoms :  130 ( 353 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k3_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f42,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f41,f40,f39,f38])).

fof(f71,plain,(
    ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(definition_unfolding,[],[f71,f52])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK2(X0,X1,X2),X0)
        & r2_hidden(X1,sK2(X0,X1,X2))
        & sK2(X0,X1,X2) = X2
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(sK2(X0,X1,X2),X0)
                & r2_hidden(X1,sK2(X0,X1,X2))
                & sK2(X0,X1,X2) = X2
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f34])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f57,f52])).

fof(f69,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK2(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5024,plain,
    ( r2_hidden(sK1(X0,X1,X1),X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X1 ),
    inference(factoring,[status(thm)],[c_4])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_315,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4643,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_320,c_315])).

cnf(c_5312,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | r2_hidden(sK1(X2,X0,X0),X0) ),
    inference(resolution,[status(thm)],[c_5024,c_4643])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6100,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(sK1(X2,X0,X0),X0)
    | r1_tarski(k1_setfam_1(k2_tarski(X2,X0)),X1) ),
    inference(resolution,[status(thm)],[c_5312,c_11])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_980,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_974,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2032,plain,
    ( r2_hidden(sK0(k1_setfam_1(k2_tarski(X0,X1)),X2),X1) = iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_974])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_979,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4356,plain,
    ( r2_hidden(sK0(k1_setfam_1(k2_tarski(X0,X1)),X2),X3) = iProver_top
    | r1_tarski(X1,X3) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2032,c_979])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_981,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_13327,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(X2,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4356,c_981])).

cnf(c_13420,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_tarski(X2,X0)),X1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13327])).

cnf(c_41580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(k1_setfam_1(k2_tarski(X2,X0)),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6100,c_11,c_13420])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2352,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_12,c_18])).

cnf(c_21,negated_conjecture,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1715,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(resolution,[status(thm)],[c_21,c_9])).

cnf(c_39381,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_2352,c_1715])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_40708,plain,
    ( ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6)))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39381,c_27,c_26,c_25])).

cnf(c_40709,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) ),
    inference(renaming,[status(thm)],[c_40708])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_40730,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
    | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6)))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_40709,c_10])).

cnf(c_41694,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) ),
    inference(resolution,[status(thm)],[c_41580,c_40730])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_959,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0,X2) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_965,plain,
    ( sK2(X0,X1,X2) = X2
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3237,plain,
    ( sK2(sK3,sK4,sK6) = sK6
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_959,c_965])).

cnf(c_1312,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK2(sK3,sK4,sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_26368,plain,
    ( sK2(sK3,sK4,sK6) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3237,c_27,c_26,c_25,c_24,c_22,c_1312])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_964,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0))) != iProver_top
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_26372,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_26368,c_964])).

cnf(c_26398,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26372])).

cnf(c_41697,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
    | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41694,c_27,c_26,c_25,c_24,c_22,c_26398])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_41713,plain,
    ( ~ v3_pre_topc(sK6,sK3)
    | ~ v3_pre_topc(sK5,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_41697,c_13])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_14,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1300,plain,
    ( v3_pre_topc(sK2(sK3,sK4,sK6),sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1303,plain,
    ( v3_pre_topc(sK2(sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1315,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK2(sK3,sK4,sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1925,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_316,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1633,plain,
    ( X0 != X1
    | X0 = sK2(sK3,sK4,sK6)
    | sK2(sK3,sK4,sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_3593,plain,
    ( X0 = sK2(sK3,sK4,sK6)
    | X0 != sK6
    | sK2(sK3,sK4,sK6) != sK6 ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_3871,plain,
    ( sK2(sK3,sK4,sK6) != sK6
    | sK6 = sK2(sK3,sK4,sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3593])).

cnf(c_1654,plain,
    ( X0 != X1
    | X0 = sK2(sK3,sK4,sK5)
    | sK2(sK3,sK4,sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_3602,plain,
    ( X0 = sK2(sK3,sK4,sK5)
    | X0 != sK5
    | sK2(sK3,sK4,sK5) != sK5 ),
    inference(instantiation,[status(thm)],[c_1654])).

cnf(c_3876,plain,
    ( sK2(sK3,sK4,sK5) != sK5
    | sK5 = sK2(sK3,sK4,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3602])).

cnf(c_3877,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_322,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1375,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(sK2(sK3,sK4,sK6),sK3)
    | X0 != sK2(sK3,sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_11257,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4,sK6),sK3)
    | v3_pre_topc(sK6,sK3)
    | sK6 != sK2(sK3,sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_1385,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(sK2(sK3,sK4,sK5),sK3)
    | X0 != sK2(sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_11269,plain,
    ( ~ v3_pre_topc(sK2(sK3,sK4,sK5),sK3)
    | v3_pre_topc(sK5,sK3)
    | sK5 != sK2(sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_958,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3238,plain,
    ( sK2(sK3,sK4,sK5) = sK5
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_965])).

cnf(c_26832,plain,
    ( sK2(sK3,sK4,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3238,c_27,c_26,c_25,c_24,c_23,c_1315])).

cnf(c_26836,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_26832,c_964])).

cnf(c_26862,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26836])).

cnf(c_41981,plain,
    ( ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41713,c_27,c_26,c_25,c_24,c_23,c_22,c_1300,c_1303,c_1312,c_1315,c_1925,c_3871,c_3876,c_3877,c_11257,c_11269,c_26398,c_26862])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_41993,plain,
    ( ~ r2_hidden(sK4,sK6)
    | ~ r2_hidden(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_41981,c_6])).

cnf(c_317,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2841,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4,X2)
    | X1 != X2
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_7102,plain,
    ( ~ r2_hidden(sK4,X0)
    | r2_hidden(sK4,X1)
    | X1 != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2841])).

cnf(c_14409,plain,
    ( r2_hidden(sK4,X0)
    | ~ r2_hidden(sK4,sK2(sK3,sK4,sK5))
    | X0 != sK2(sK3,sK4,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_7102])).

cnf(c_18560,plain,
    ( ~ r2_hidden(sK4,sK2(sK3,sK4,sK5))
    | r2_hidden(sK4,sK5)
    | sK4 != sK4
    | sK5 != sK2(sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_14409])).

cnf(c_14404,plain,
    ( r2_hidden(sK4,X0)
    | ~ r2_hidden(sK4,sK2(sK3,sK4,sK6))
    | X0 != sK2(sK3,sK4,sK6)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_7102])).

cnf(c_18553,plain,
    ( ~ r2_hidden(sK4,sK2(sK3,sK4,sK6))
    | r2_hidden(sK4,sK6)
    | sK4 != sK4
    | sK6 != sK2(sK3,sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_14404])).

cnf(c_1535,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK2(X1,X0,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1309,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | r2_hidden(sK4,sK2(sK3,sK4,sK5))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1306,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    | r2_hidden(sK4,sK2(sK3,sK4,sK6))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41993,c_18560,c_18553,c_3877,c_3876,c_3871,c_1925,c_1535,c_1315,c_1312,c_1309,c_1306,c_22,c_23,c_24,c_25,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:55:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.32/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.32/1.98  
% 11.32/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.32/1.98  
% 11.32/1.98  ------  iProver source info
% 11.32/1.98  
% 11.32/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.32/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.32/1.98  git: non_committed_changes: false
% 11.32/1.98  git: last_make_outside_of_git: false
% 11.32/1.98  
% 11.32/1.98  ------ 
% 11.32/1.98  
% 11.32/1.98  ------ Input Options
% 11.32/1.98  
% 11.32/1.98  --out_options                           all
% 11.32/1.98  --tptp_safe_out                         true
% 11.32/1.98  --problem_path                          ""
% 11.32/1.98  --include_path                          ""
% 11.32/1.98  --clausifier                            res/vclausify_rel
% 11.32/1.98  --clausifier_options                    --mode clausify
% 11.32/1.98  --stdin                                 false
% 11.32/1.98  --stats_out                             sel
% 11.32/1.98  
% 11.32/1.98  ------ General Options
% 11.32/1.98  
% 11.32/1.98  --fof                                   false
% 11.32/1.98  --time_out_real                         604.99
% 11.32/1.98  --time_out_virtual                      -1.
% 11.32/1.98  --symbol_type_check                     false
% 11.32/1.98  --clausify_out                          false
% 11.32/1.98  --sig_cnt_out                           false
% 11.32/1.98  --trig_cnt_out                          false
% 11.32/1.98  --trig_cnt_out_tolerance                1.
% 11.32/1.98  --trig_cnt_out_sk_spl                   false
% 11.32/1.98  --abstr_cl_out                          false
% 11.32/1.98  
% 11.32/1.98  ------ Global Options
% 11.32/1.98  
% 11.32/1.98  --schedule                              none
% 11.32/1.98  --add_important_lit                     false
% 11.32/1.98  --prop_solver_per_cl                    1000
% 11.32/1.98  --min_unsat_core                        false
% 11.32/1.98  --soft_assumptions                      false
% 11.32/1.98  --soft_lemma_size                       3
% 11.32/1.98  --prop_impl_unit_size                   0
% 11.32/1.98  --prop_impl_unit                        []
% 11.32/1.98  --share_sel_clauses                     true
% 11.32/1.98  --reset_solvers                         false
% 11.32/1.98  --bc_imp_inh                            [conj_cone]
% 11.32/1.98  --conj_cone_tolerance                   3.
% 11.32/1.98  --extra_neg_conj                        none
% 11.32/1.98  --large_theory_mode                     true
% 11.32/1.98  --prolific_symb_bound                   200
% 11.32/1.98  --lt_threshold                          2000
% 11.32/1.98  --clause_weak_htbl                      true
% 11.32/1.98  --gc_record_bc_elim                     false
% 11.32/1.98  
% 11.32/1.98  ------ Preprocessing Options
% 11.32/1.98  
% 11.32/1.98  --preprocessing_flag                    true
% 11.32/1.98  --time_out_prep_mult                    0.1
% 11.32/1.98  --splitting_mode                        input
% 11.32/1.98  --splitting_grd                         true
% 11.32/1.98  --splitting_cvd                         false
% 11.32/1.98  --splitting_cvd_svl                     false
% 11.32/1.98  --splitting_nvd                         32
% 11.32/1.98  --sub_typing                            true
% 11.32/1.98  --prep_gs_sim                           false
% 11.32/1.98  --prep_unflatten                        true
% 11.32/1.98  --prep_res_sim                          true
% 11.32/1.98  --prep_upred                            true
% 11.32/1.98  --prep_sem_filter                       exhaustive
% 11.32/1.98  --prep_sem_filter_out                   false
% 11.32/1.98  --pred_elim                             false
% 11.32/1.98  --res_sim_input                         true
% 11.32/1.98  --eq_ax_congr_red                       true
% 11.32/1.98  --pure_diseq_elim                       true
% 11.32/1.98  --brand_transform                       false
% 11.32/1.98  --non_eq_to_eq                          false
% 11.32/1.98  --prep_def_merge                        true
% 11.32/1.98  --prep_def_merge_prop_impl              false
% 11.32/1.98  --prep_def_merge_mbd                    true
% 11.32/1.98  --prep_def_merge_tr_red                 false
% 11.32/1.98  --prep_def_merge_tr_cl                  false
% 11.32/1.98  --smt_preprocessing                     true
% 11.32/1.98  --smt_ac_axioms                         fast
% 11.32/1.98  --preprocessed_out                      false
% 11.32/1.98  --preprocessed_stats                    false
% 11.32/1.98  
% 11.32/1.98  ------ Abstraction refinement Options
% 11.32/1.98  
% 11.32/1.98  --abstr_ref                             []
% 11.32/1.98  --abstr_ref_prep                        false
% 11.32/1.98  --abstr_ref_until_sat                   false
% 11.32/1.98  --abstr_ref_sig_restrict                funpre
% 11.32/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.32/1.98  --abstr_ref_under                       []
% 11.32/1.98  
% 11.32/1.98  ------ SAT Options
% 11.32/1.98  
% 11.32/1.98  --sat_mode                              false
% 11.32/1.98  --sat_fm_restart_options                ""
% 11.32/1.98  --sat_gr_def                            false
% 11.32/1.98  --sat_epr_types                         true
% 11.32/1.98  --sat_non_cyclic_types                  false
% 11.32/1.98  --sat_finite_models                     false
% 11.32/1.98  --sat_fm_lemmas                         false
% 11.32/1.98  --sat_fm_prep                           false
% 11.32/1.98  --sat_fm_uc_incr                        true
% 11.32/1.98  --sat_out_model                         small
% 11.32/1.98  --sat_out_clauses                       false
% 11.32/1.98  
% 11.32/1.98  ------ QBF Options
% 11.32/1.98  
% 11.32/1.98  --qbf_mode                              false
% 11.32/1.98  --qbf_elim_univ                         false
% 11.32/1.98  --qbf_dom_inst                          none
% 11.32/1.98  --qbf_dom_pre_inst                      false
% 11.32/1.98  --qbf_sk_in                             false
% 11.32/1.98  --qbf_pred_elim                         true
% 11.32/1.98  --qbf_split                             512
% 11.32/1.98  
% 11.32/1.98  ------ BMC1 Options
% 11.32/1.98  
% 11.32/1.98  --bmc1_incremental                      false
% 11.32/1.98  --bmc1_axioms                           reachable_all
% 11.32/1.98  --bmc1_min_bound                        0
% 11.32/1.98  --bmc1_max_bound                        -1
% 11.32/1.98  --bmc1_max_bound_default                -1
% 11.32/1.98  --bmc1_symbol_reachability              true
% 11.32/1.98  --bmc1_property_lemmas                  false
% 11.32/1.98  --bmc1_k_induction                      false
% 11.32/1.98  --bmc1_non_equiv_states                 false
% 11.32/1.98  --bmc1_deadlock                         false
% 11.32/1.98  --bmc1_ucm                              false
% 11.32/1.98  --bmc1_add_unsat_core                   none
% 11.32/1.98  --bmc1_unsat_core_children              false
% 11.32/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.32/1.98  --bmc1_out_stat                         full
% 11.32/1.98  --bmc1_ground_init                      false
% 11.32/1.98  --bmc1_pre_inst_next_state              false
% 11.32/1.98  --bmc1_pre_inst_state                   false
% 11.32/1.98  --bmc1_pre_inst_reach_state             false
% 11.32/1.98  --bmc1_out_unsat_core                   false
% 11.32/1.98  --bmc1_aig_witness_out                  false
% 11.32/1.98  --bmc1_verbose                          false
% 11.32/1.98  --bmc1_dump_clauses_tptp                false
% 11.32/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.32/1.98  --bmc1_dump_file                        -
% 11.32/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.32/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.32/1.98  --bmc1_ucm_extend_mode                  1
% 11.32/1.98  --bmc1_ucm_init_mode                    2
% 11.32/1.98  --bmc1_ucm_cone_mode                    none
% 11.32/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.32/1.98  --bmc1_ucm_relax_model                  4
% 11.32/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.32/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.32/1.98  --bmc1_ucm_layered_model                none
% 11.32/1.98  --bmc1_ucm_max_lemma_size               10
% 11.32/1.98  
% 11.32/1.98  ------ AIG Options
% 11.32/1.98  
% 11.32/1.98  --aig_mode                              false
% 11.32/1.98  
% 11.32/1.98  ------ Instantiation Options
% 11.32/1.98  
% 11.32/1.98  --instantiation_flag                    true
% 11.32/1.98  --inst_sos_flag                         false
% 11.32/1.98  --inst_sos_phase                        true
% 11.32/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.32/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.32/1.98  --inst_lit_sel_side                     num_symb
% 11.32/1.98  --inst_solver_per_active                1400
% 11.32/1.98  --inst_solver_calls_frac                1.
% 11.32/1.98  --inst_passive_queue_type               priority_queues
% 11.32/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.32/1.98  --inst_passive_queues_freq              [25;2]
% 11.32/1.98  --inst_dismatching                      true
% 11.32/1.98  --inst_eager_unprocessed_to_passive     true
% 11.32/1.98  --inst_prop_sim_given                   true
% 11.32/1.98  --inst_prop_sim_new                     false
% 11.32/1.98  --inst_subs_new                         false
% 11.32/1.98  --inst_eq_res_simp                      false
% 11.32/1.98  --inst_subs_given                       false
% 11.32/1.98  --inst_orphan_elimination               true
% 11.32/1.98  --inst_learning_loop_flag               true
% 11.32/1.98  --inst_learning_start                   3000
% 11.32/1.98  --inst_learning_factor                  2
% 11.32/1.98  --inst_start_prop_sim_after_learn       3
% 11.32/1.98  --inst_sel_renew                        solver
% 11.32/1.98  --inst_lit_activity_flag                true
% 11.32/1.98  --inst_restr_to_given                   false
% 11.32/1.98  --inst_activity_threshold               500
% 11.32/1.98  --inst_out_proof                        true
% 11.32/1.98  
% 11.32/1.98  ------ Resolution Options
% 11.32/1.98  
% 11.32/1.98  --resolution_flag                       true
% 11.32/1.98  --res_lit_sel                           adaptive
% 11.32/1.98  --res_lit_sel_side                      none
% 11.32/1.98  --res_ordering                          kbo
% 11.32/1.98  --res_to_prop_solver                    active
% 11.32/1.98  --res_prop_simpl_new                    false
% 11.32/1.98  --res_prop_simpl_given                  true
% 11.32/1.98  --res_passive_queue_type                priority_queues
% 11.32/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.32/1.98  --res_passive_queues_freq               [15;5]
% 11.32/1.98  --res_forward_subs                      full
% 11.32/1.98  --res_backward_subs                     full
% 11.32/1.98  --res_forward_subs_resolution           true
% 11.32/1.98  --res_backward_subs_resolution          true
% 11.32/1.98  --res_orphan_elimination                true
% 11.32/1.98  --res_time_limit                        2.
% 11.32/1.98  --res_out_proof                         true
% 11.32/1.98  
% 11.32/1.98  ------ Superposition Options
% 11.32/1.98  
% 11.32/1.98  --superposition_flag                    true
% 11.32/1.98  --sup_passive_queue_type                priority_queues
% 11.32/1.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.32/1.98  --sup_passive_queues_freq               [1;4]
% 11.32/1.98  --demod_completeness_check              fast
% 11.32/1.98  --demod_use_ground                      true
% 11.32/1.98  --sup_to_prop_solver                    passive
% 11.32/1.98  --sup_prop_simpl_new                    true
% 11.32/1.98  --sup_prop_simpl_given                  true
% 11.32/1.98  --sup_fun_splitting                     false
% 11.32/1.98  --sup_smt_interval                      50000
% 11.32/1.98  
% 11.32/1.98  ------ Superposition Simplification Setup
% 11.32/1.98  
% 11.32/1.98  --sup_indices_passive                   []
% 11.32/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.32/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.32/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.32/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.32/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.32/1.98  --sup_full_bw                           [BwDemod]
% 11.32/1.98  --sup_immed_triv                        [TrivRules]
% 11.32/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.32/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.32/1.98  --sup_immed_bw_main                     []
% 11.32/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.32/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.32/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.32/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.32/1.98  
% 11.32/1.98  ------ Combination Options
% 11.32/1.98  
% 11.32/1.98  --comb_res_mult                         3
% 11.32/1.98  --comb_sup_mult                         2
% 11.32/1.98  --comb_inst_mult                        10
% 11.32/1.98  
% 11.32/1.98  ------ Debug Options
% 11.32/1.98  
% 11.32/1.98  --dbg_backtrace                         false
% 11.32/1.98  --dbg_dump_prop_clauses                 false
% 11.32/1.98  --dbg_dump_prop_clauses_file            -
% 11.32/1.98  --dbg_out_stat                          false
% 11.32/1.98  ------ Parsing...
% 11.32/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.32/1.98  
% 11.32/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.32/1.98  
% 11.32/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.32/1.98  
% 11.32/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.32/1.98  ------ Proving...
% 11.32/1.98  ------ Problem Properties 
% 11.32/1.98  
% 11.32/1.98  
% 11.32/1.98  clauses                                 28
% 11.32/1.98  conjectures                             7
% 11.32/1.98  EPR                                     5
% 11.32/1.98  Horn                                    18
% 11.32/1.98  unary                                   7
% 11.32/1.98  binary                                  7
% 11.32/1.98  lits                                    93
% 11.32/1.98  lits eq                                 4
% 11.32/1.98  fd_pure                                 0
% 11.32/1.98  fd_pseudo                               0
% 11.32/1.98  fd_cond                                 0
% 11.32/1.98  fd_pseudo_cond                          3
% 11.32/1.98  AC symbols                              0
% 11.32/1.98  
% 11.32/1.98  ------ Input Options Time Limit: Unbounded
% 11.32/1.98  
% 11.32/1.98  
% 11.32/1.98  ------ 
% 11.32/1.98  Current options:
% 11.32/1.98  ------ 
% 11.32/1.98  
% 11.32/1.98  ------ Input Options
% 11.32/1.98  
% 11.32/1.98  --out_options                           all
% 11.32/1.98  --tptp_safe_out                         true
% 11.32/1.98  --problem_path                          ""
% 11.32/1.98  --include_path                          ""
% 11.32/1.98  --clausifier                            res/vclausify_rel
% 11.32/1.98  --clausifier_options                    --mode clausify
% 11.32/1.98  --stdin                                 false
% 11.32/1.98  --stats_out                             sel
% 11.32/1.98  
% 11.32/1.98  ------ General Options
% 11.32/1.98  
% 11.32/1.98  --fof                                   false
% 11.32/1.98  --time_out_real                         604.99
% 11.32/1.98  --time_out_virtual                      -1.
% 11.32/1.98  --symbol_type_check                     false
% 11.32/1.98  --clausify_out                          false
% 11.32/1.98  --sig_cnt_out                           false
% 11.32/1.98  --trig_cnt_out                          false
% 11.32/1.98  --trig_cnt_out_tolerance                1.
% 11.32/1.98  --trig_cnt_out_sk_spl                   false
% 11.32/1.98  --abstr_cl_out                          false
% 11.32/1.98  
% 11.32/1.98  ------ Global Options
% 11.32/1.98  
% 11.32/1.98  --schedule                              none
% 11.32/1.98  --add_important_lit                     false
% 11.32/1.98  --prop_solver_per_cl                    1000
% 11.32/1.98  --min_unsat_core                        false
% 11.32/1.98  --soft_assumptions                      false
% 11.32/1.98  --soft_lemma_size                       3
% 11.32/1.98  --prop_impl_unit_size                   0
% 11.32/1.98  --prop_impl_unit                        []
% 11.32/1.98  --share_sel_clauses                     true
% 11.32/1.98  --reset_solvers                         false
% 11.32/1.98  --bc_imp_inh                            [conj_cone]
% 11.32/1.98  --conj_cone_tolerance                   3.
% 11.32/1.98  --extra_neg_conj                        none
% 11.32/1.98  --large_theory_mode                     true
% 11.32/1.98  --prolific_symb_bound                   200
% 11.32/1.98  --lt_threshold                          2000
% 11.32/1.98  --clause_weak_htbl                      true
% 11.32/1.98  --gc_record_bc_elim                     false
% 11.32/1.98  
% 11.32/1.98  ------ Preprocessing Options
% 11.32/1.98  
% 11.32/1.98  --preprocessing_flag                    true
% 11.32/1.98  --time_out_prep_mult                    0.1
% 11.32/1.98  --splitting_mode                        input
% 11.32/1.98  --splitting_grd                         true
% 11.32/1.98  --splitting_cvd                         false
% 11.32/1.98  --splitting_cvd_svl                     false
% 11.32/1.98  --splitting_nvd                         32
% 11.32/1.98  --sub_typing                            true
% 11.32/1.98  --prep_gs_sim                           false
% 11.32/1.98  --prep_unflatten                        true
% 11.32/1.98  --prep_res_sim                          true
% 11.32/1.98  --prep_upred                            true
% 11.32/1.98  --prep_sem_filter                       exhaustive
% 11.32/1.98  --prep_sem_filter_out                   false
% 11.32/1.98  --pred_elim                             false
% 11.32/1.98  --res_sim_input                         true
% 11.32/1.98  --eq_ax_congr_red                       true
% 11.32/1.98  --pure_diseq_elim                       true
% 11.32/1.98  --brand_transform                       false
% 11.32/1.98  --non_eq_to_eq                          false
% 11.32/1.98  --prep_def_merge                        true
% 11.32/1.98  --prep_def_merge_prop_impl              false
% 11.32/1.98  --prep_def_merge_mbd                    true
% 11.32/1.98  --prep_def_merge_tr_red                 false
% 11.32/1.98  --prep_def_merge_tr_cl                  false
% 11.32/1.98  --smt_preprocessing                     true
% 11.32/1.98  --smt_ac_axioms                         fast
% 11.32/1.98  --preprocessed_out                      false
% 11.32/1.98  --preprocessed_stats                    false
% 11.32/1.98  
% 11.32/1.98  ------ Abstraction refinement Options
% 11.32/1.98  
% 11.32/1.98  --abstr_ref                             []
% 11.32/1.98  --abstr_ref_prep                        false
% 11.32/1.98  --abstr_ref_until_sat                   false
% 11.32/1.98  --abstr_ref_sig_restrict                funpre
% 11.32/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.32/1.98  --abstr_ref_under                       []
% 11.32/1.98  
% 11.32/1.98  ------ SAT Options
% 11.32/1.98  
% 11.32/1.98  --sat_mode                              false
% 11.32/1.98  --sat_fm_restart_options                ""
% 11.32/1.98  --sat_gr_def                            false
% 11.32/1.98  --sat_epr_types                         true
% 11.32/1.98  --sat_non_cyclic_types                  false
% 11.32/1.98  --sat_finite_models                     false
% 11.32/1.98  --sat_fm_lemmas                         false
% 11.32/1.98  --sat_fm_prep                           false
% 11.32/1.98  --sat_fm_uc_incr                        true
% 11.32/1.98  --sat_out_model                         small
% 11.32/1.98  --sat_out_clauses                       false
% 11.32/1.98  
% 11.32/1.98  ------ QBF Options
% 11.32/1.98  
% 11.32/1.98  --qbf_mode                              false
% 11.32/1.98  --qbf_elim_univ                         false
% 11.32/1.98  --qbf_dom_inst                          none
% 11.32/1.98  --qbf_dom_pre_inst                      false
% 11.32/1.98  --qbf_sk_in                             false
% 11.32/1.98  --qbf_pred_elim                         true
% 11.32/1.98  --qbf_split                             512
% 11.32/1.98  
% 11.32/1.98  ------ BMC1 Options
% 11.32/1.98  
% 11.32/1.98  --bmc1_incremental                      false
% 11.32/1.98  --bmc1_axioms                           reachable_all
% 11.32/1.98  --bmc1_min_bound                        0
% 11.32/1.98  --bmc1_max_bound                        -1
% 11.32/1.98  --bmc1_max_bound_default                -1
% 11.32/1.98  --bmc1_symbol_reachability              true
% 11.32/1.98  --bmc1_property_lemmas                  false
% 11.32/1.98  --bmc1_k_induction                      false
% 11.32/1.98  --bmc1_non_equiv_states                 false
% 11.32/1.98  --bmc1_deadlock                         false
% 11.32/1.98  --bmc1_ucm                              false
% 11.32/1.98  --bmc1_add_unsat_core                   none
% 11.32/1.98  --bmc1_unsat_core_children              false
% 11.32/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.32/1.98  --bmc1_out_stat                         full
% 11.32/1.98  --bmc1_ground_init                      false
% 11.32/1.98  --bmc1_pre_inst_next_state              false
% 11.32/1.98  --bmc1_pre_inst_state                   false
% 11.32/1.98  --bmc1_pre_inst_reach_state             false
% 11.32/1.98  --bmc1_out_unsat_core                   false
% 11.32/1.98  --bmc1_aig_witness_out                  false
% 11.32/1.98  --bmc1_verbose                          false
% 11.32/1.98  --bmc1_dump_clauses_tptp                false
% 11.32/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.32/1.98  --bmc1_dump_file                        -
% 11.32/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.32/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.32/1.98  --bmc1_ucm_extend_mode                  1
% 11.32/1.98  --bmc1_ucm_init_mode                    2
% 11.32/1.98  --bmc1_ucm_cone_mode                    none
% 11.32/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.32/1.98  --bmc1_ucm_relax_model                  4
% 11.32/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.32/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.32/1.98  --bmc1_ucm_layered_model                none
% 11.32/1.98  --bmc1_ucm_max_lemma_size               10
% 11.32/1.98  
% 11.32/1.98  ------ AIG Options
% 11.32/1.98  
% 11.32/1.98  --aig_mode                              false
% 11.32/1.98  
% 11.32/1.98  ------ Instantiation Options
% 11.32/1.98  
% 11.32/1.98  --instantiation_flag                    true
% 11.32/1.98  --inst_sos_flag                         false
% 11.32/1.98  --inst_sos_phase                        true
% 11.32/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.32/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.32/1.98  --inst_lit_sel_side                     num_symb
% 11.32/1.98  --inst_solver_per_active                1400
% 11.32/1.98  --inst_solver_calls_frac                1.
% 11.32/1.98  --inst_passive_queue_type               priority_queues
% 11.32/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.32/1.98  --inst_passive_queues_freq              [25;2]
% 11.32/1.98  --inst_dismatching                      true
% 11.32/1.98  --inst_eager_unprocessed_to_passive     true
% 11.32/1.98  --inst_prop_sim_given                   true
% 11.32/1.98  --inst_prop_sim_new                     false
% 11.32/1.98  --inst_subs_new                         false
% 11.32/1.98  --inst_eq_res_simp                      false
% 11.32/1.98  --inst_subs_given                       false
% 11.32/1.98  --inst_orphan_elimination               true
% 11.32/1.98  --inst_learning_loop_flag               true
% 11.32/1.98  --inst_learning_start                   3000
% 11.32/1.98  --inst_learning_factor                  2
% 11.32/1.98  --inst_start_prop_sim_after_learn       3
% 11.32/1.98  --inst_sel_renew                        solver
% 11.32/1.98  --inst_lit_activity_flag                true
% 11.32/1.98  --inst_restr_to_given                   false
% 11.32/1.98  --inst_activity_threshold               500
% 11.32/1.98  --inst_out_proof                        true
% 11.32/1.98  
% 11.32/1.98  ------ Resolution Options
% 11.32/1.98  
% 11.32/1.98  --resolution_flag                       true
% 11.32/1.98  --res_lit_sel                           adaptive
% 11.32/1.98  --res_lit_sel_side                      none
% 11.32/1.98  --res_ordering                          kbo
% 11.32/1.98  --res_to_prop_solver                    active
% 11.32/1.98  --res_prop_simpl_new                    false
% 11.32/1.98  --res_prop_simpl_given                  true
% 11.32/1.98  --res_passive_queue_type                priority_queues
% 11.32/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.32/1.98  --res_passive_queues_freq               [15;5]
% 11.32/1.98  --res_forward_subs                      full
% 11.32/1.98  --res_backward_subs                     full
% 11.32/1.98  --res_forward_subs_resolution           true
% 11.32/1.98  --res_backward_subs_resolution          true
% 11.32/1.98  --res_orphan_elimination                true
% 11.32/1.98  --res_time_limit                        2.
% 11.32/1.98  --res_out_proof                         true
% 11.32/1.98  
% 11.32/1.98  ------ Superposition Options
% 11.32/1.98  
% 11.32/1.98  --superposition_flag                    true
% 11.32/1.98  --sup_passive_queue_type                priority_queues
% 11.32/1.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.32/1.98  --sup_passive_queues_freq               [1;4]
% 11.32/1.98  --demod_completeness_check              fast
% 11.32/1.98  --demod_use_ground                      true
% 11.32/1.98  --sup_to_prop_solver                    passive
% 11.32/1.98  --sup_prop_simpl_new                    true
% 11.32/1.98  --sup_prop_simpl_given                  true
% 11.32/1.98  --sup_fun_splitting                     false
% 11.32/1.98  --sup_smt_interval                      50000
% 11.32/1.98  
% 11.32/1.98  ------ Superposition Simplification Setup
% 11.32/1.98  
% 11.32/1.98  --sup_indices_passive                   []
% 11.32/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.32/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.32/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.32/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.32/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.32/1.98  --sup_full_bw                           [BwDemod]
% 11.32/1.98  --sup_immed_triv                        [TrivRules]
% 11.32/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.32/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.32/1.98  --sup_immed_bw_main                     []
% 11.32/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.32/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.32/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.32/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.32/1.98  
% 11.32/1.98  ------ Combination Options
% 11.32/1.98  
% 11.32/1.98  --comb_res_mult                         3
% 11.32/1.98  --comb_sup_mult                         2
% 11.32/1.98  --comb_inst_mult                        10
% 11.32/1.98  
% 11.32/1.98  ------ Debug Options
% 11.32/1.98  
% 11.32/1.98  --dbg_backtrace                         false
% 11.32/1.98  --dbg_dump_prop_clauses                 false
% 11.32/1.98  --dbg_dump_prop_clauses_file            -
% 11.32/1.98  --dbg_out_stat                          false
% 11.32/1.98  
% 11.32/1.98  
% 11.32/1.98  
% 11.32/1.98  
% 11.32/1.98  ------ Proving...
% 11.32/1.98  
% 11.32/1.98  
% 11.32/1.98  % SZS status Theorem for theBenchmark.p
% 11.32/1.98  
% 11.32/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.32/1.98  
% 11.32/1.98  fof(f2,axiom,(
% 11.32/1.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.32/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.32/1.98  
% 11.32/1.98  fof(f28,plain,(
% 11.32/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.32/1.98    inference(nnf_transformation,[],[f2])).
% 11.32/1.98  
% 11.32/1.98  fof(f29,plain,(
% 11.32/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.32/1.98    inference(flattening,[],[f28])).
% 11.32/1.98  
% 11.32/1.98  fof(f30,plain,(
% 11.32/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.32/1.98    inference(rectify,[],[f29])).
% 11.32/1.98  
% 11.32/1.98  fof(f31,plain,(
% 11.32/1.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 11.32/1.98    introduced(choice_axiom,[])).
% 11.32/1.98  
% 11.32/1.98  fof(f32,plain,(
% 11.32/1.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.32/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 11.32/1.98  
% 11.32/1.98  fof(f50,plain,(
% 11.32/1.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f32])).
% 11.32/1.98  
% 11.32/1.98  fof(f3,axiom,(
% 11.32/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.32/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.32/1.98  
% 11.32/1.98  fof(f52,plain,(
% 11.32/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.32/1.98    inference(cnf_transformation,[],[f3])).
% 11.32/1.98  
% 11.32/1.98  fof(f73,plain,(
% 11.32/1.98    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 11.32/1.98    inference(definition_unfolding,[],[f50,f52])).
% 11.32/1.98  
% 11.32/1.98  fof(f5,axiom,(
% 11.32/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.32/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.32/1.98  
% 11.32/1.98  fof(f33,plain,(
% 11.32/1.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.32/1.98    inference(nnf_transformation,[],[f5])).
% 11.32/1.98  
% 11.32/1.98  fof(f54,plain,(
% 11.32/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.32/1.98    inference(cnf_transformation,[],[f33])).
% 11.32/1.98  
% 11.32/1.98  fof(f1,axiom,(
% 11.32/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.32/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.32/1.98  
% 11.32/1.98  fof(f12,plain,(
% 11.32/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.32/1.98    inference(ennf_transformation,[],[f1])).
% 11.32/1.98  
% 11.32/1.98  fof(f24,plain,(
% 11.32/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.32/1.98    inference(nnf_transformation,[],[f12])).
% 11.32/1.98  
% 11.32/1.98  fof(f25,plain,(
% 11.32/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.32/1.98    inference(rectify,[],[f24])).
% 11.32/1.98  
% 11.32/1.98  fof(f26,plain,(
% 11.32/1.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.32/1.98    introduced(choice_axiom,[])).
% 11.32/1.98  
% 11.32/1.98  fof(f27,plain,(
% 11.32/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.32/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 11.32/1.98  
% 11.32/1.98  fof(f44,plain,(
% 11.32/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f27])).
% 11.32/1.98  
% 11.32/1.98  fof(f47,plain,(
% 11.32/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 11.32/1.98    inference(cnf_transformation,[],[f32])).
% 11.32/1.98  
% 11.32/1.98  fof(f76,plain,(
% 11.32/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 11.32/1.98    inference(definition_unfolding,[],[f47,f52])).
% 11.32/1.98  
% 11.32/1.98  fof(f81,plain,(
% 11.32/1.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 11.32/1.98    inference(equality_resolution,[],[f76])).
% 11.32/1.98  
% 11.32/1.98  fof(f43,plain,(
% 11.32/1.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f27])).
% 11.32/1.98  
% 11.32/1.98  fof(f45,plain,(
% 11.32/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f27])).
% 11.32/1.98  
% 11.32/1.98  fof(f6,axiom,(
% 11.32/1.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 11.32/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.32/1.98  
% 11.32/1.98  fof(f14,plain,(
% 11.32/1.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 11.32/1.98    inference(ennf_transformation,[],[f6])).
% 11.32/1.98  
% 11.32/1.98  fof(f15,plain,(
% 11.32/1.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.32/1.98    inference(flattening,[],[f14])).
% 11.32/1.98  
% 11.32/1.98  fof(f56,plain,(
% 11.32/1.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f15])).
% 11.32/1.98  
% 11.32/1.98  fof(f9,axiom,(
% 11.32/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 11.32/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.32/1.98  
% 11.32/1.98  fof(f20,plain,(
% 11.32/1.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.32/1.98    inference(ennf_transformation,[],[f9])).
% 11.32/1.98  
% 11.32/1.98  fof(f21,plain,(
% 11.32/1.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.32/1.98    inference(flattening,[],[f20])).
% 11.32/1.98  
% 11.32/1.98  fof(f36,plain,(
% 11.32/1.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.32/1.98    inference(nnf_transformation,[],[f21])).
% 11.32/1.98  
% 11.32/1.98  fof(f37,plain,(
% 11.32/1.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.32/1.98    inference(flattening,[],[f36])).
% 11.32/1.98  
% 11.32/1.98  fof(f64,plain,(
% 11.32/1.98    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f37])).
% 11.32/1.98  
% 11.32/1.98  fof(f10,conjecture,(
% 11.32/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 11.32/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.32/1.98  
% 11.32/1.98  fof(f11,negated_conjecture,(
% 11.32/1.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 11.32/1.98    inference(negated_conjecture,[],[f10])).
% 11.32/1.98  
% 11.32/1.98  fof(f22,plain,(
% 11.32/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.32/1.98    inference(ennf_transformation,[],[f11])).
% 11.32/1.98  
% 11.32/1.98  fof(f23,plain,(
% 11.32/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.32/1.98    inference(flattening,[],[f22])).
% 11.32/1.98  
% 11.32/1.98  fof(f41,plain,(
% 11.32/1.98    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k3_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 11.32/1.98    introduced(choice_axiom,[])).
% 11.32/1.98  
% 11.32/1.98  fof(f40,plain,(
% 11.32/1.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 11.32/1.98    introduced(choice_axiom,[])).
% 11.32/1.98  
% 11.32/1.98  fof(f39,plain,(
% 11.32/1.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 11.32/1.98    introduced(choice_axiom,[])).
% 11.32/1.98  
% 11.32/1.98  fof(f38,plain,(
% 11.32/1.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 11.32/1.98    introduced(choice_axiom,[])).
% 11.32/1.98  
% 11.32/1.98  fof(f42,plain,(
% 11.32/1.98    (((~m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 11.32/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f41,f40,f39,f38])).
% 11.32/1.98  
% 11.32/1.98  fof(f71,plain,(
% 11.32/1.98    ~m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 11.32/1.98    inference(cnf_transformation,[],[f42])).
% 11.32/1.98  
% 11.32/1.98  fof(f79,plain,(
% 11.32/1.98    ~m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 11.32/1.98    inference(definition_unfolding,[],[f71,f52])).
% 11.32/1.98  
% 11.32/1.98  fof(f4,axiom,(
% 11.32/1.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 11.32/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.32/1.98  
% 11.32/1.98  fof(f13,plain,(
% 11.32/1.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 11.32/1.98    inference(ennf_transformation,[],[f4])).
% 11.32/1.98  
% 11.32/1.98  fof(f53,plain,(
% 11.32/1.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f13])).
% 11.32/1.98  
% 11.32/1.98  fof(f65,plain,(
% 11.32/1.98    ~v2_struct_0(sK3)),
% 11.32/1.98    inference(cnf_transformation,[],[f42])).
% 11.32/1.98  
% 11.32/1.98  fof(f66,plain,(
% 11.32/1.98    v2_pre_topc(sK3)),
% 11.32/1.98    inference(cnf_transformation,[],[f42])).
% 11.32/1.98  
% 11.32/1.98  fof(f67,plain,(
% 11.32/1.98    l1_pre_topc(sK3)),
% 11.32/1.98    inference(cnf_transformation,[],[f42])).
% 11.32/1.98  
% 11.32/1.98  fof(f55,plain,(
% 11.32/1.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f33])).
% 11.32/1.98  
% 11.32/1.98  fof(f68,plain,(
% 11.32/1.98    m1_subset_1(sK4,u1_struct_0(sK3))),
% 11.32/1.98    inference(cnf_transformation,[],[f42])).
% 11.32/1.98  
% 11.32/1.98  fof(f70,plain,(
% 11.32/1.98    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 11.32/1.98    inference(cnf_transformation,[],[f42])).
% 11.32/1.98  
% 11.32/1.98  fof(f8,axiom,(
% 11.32/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 11.32/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.32/1.98  
% 11.32/1.98  fof(f18,plain,(
% 11.32/1.98    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.32/1.98    inference(ennf_transformation,[],[f8])).
% 11.32/1.98  
% 11.32/1.98  fof(f19,plain,(
% 11.32/1.98    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.32/1.98    inference(flattening,[],[f18])).
% 11.32/1.98  
% 11.32/1.98  fof(f34,plain,(
% 11.32/1.98    ! [X2,X1,X0] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK2(X0,X1,X2),X0) & r2_hidden(X1,sK2(X0,X1,X2)) & sK2(X0,X1,X2) = X2 & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.32/1.98    introduced(choice_axiom,[])).
% 11.32/1.98  
% 11.32/1.98  fof(f35,plain,(
% 11.32/1.98    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(sK2(X0,X1,X2),X0) & r2_hidden(X1,sK2(X0,X1,X2)) & sK2(X0,X1,X2) = X2 & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.32/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f34])).
% 11.32/1.98  
% 11.32/1.98  fof(f59,plain,(
% 11.32/1.98    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f35])).
% 11.32/1.98  
% 11.32/1.98  fof(f58,plain,(
% 11.32/1.98    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f35])).
% 11.32/1.98  
% 11.32/1.98  fof(f7,axiom,(
% 11.32/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 11.32/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.32/1.98  
% 11.32/1.98  fof(f16,plain,(
% 11.32/1.98    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.32/1.98    inference(ennf_transformation,[],[f7])).
% 11.32/1.98  
% 11.32/1.98  fof(f17,plain,(
% 11.32/1.98    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.32/1.98    inference(flattening,[],[f16])).
% 11.32/1.98  
% 11.32/1.98  fof(f57,plain,(
% 11.32/1.98    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f17])).
% 11.32/1.98  
% 11.32/1.98  fof(f78,plain,(
% 11.32/1.98    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.32/1.98    inference(definition_unfolding,[],[f57,f52])).
% 11.32/1.98  
% 11.32/1.98  fof(f69,plain,(
% 11.32/1.98    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 11.32/1.98    inference(cnf_transformation,[],[f42])).
% 11.32/1.98  
% 11.32/1.98  fof(f61,plain,(
% 11.32/1.98    ( ! [X2,X0,X1] : (v3_pre_topc(sK2(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f35])).
% 11.32/1.98  
% 11.32/1.98  fof(f48,plain,(
% 11.32/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 11.32/1.98    inference(cnf_transformation,[],[f32])).
% 11.32/1.98  
% 11.32/1.98  fof(f75,plain,(
% 11.32/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 11.32/1.98    inference(definition_unfolding,[],[f48,f52])).
% 11.32/1.98  
% 11.32/1.98  fof(f80,plain,(
% 11.32/1.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 11.32/1.98    inference(equality_resolution,[],[f75])).
% 11.32/1.98  
% 11.32/1.98  fof(f60,plain,(
% 11.32/1.98    ( ! [X2,X0,X1] : (r2_hidden(X1,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.32/1.98    inference(cnf_transformation,[],[f35])).
% 11.32/1.98  
% 11.32/1.98  cnf(c_4,plain,
% 11.32/1.98      ( r2_hidden(sK1(X0,X1,X2),X1)
% 11.32/1.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 11.32/1.98      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
% 11.32/1.98      inference(cnf_transformation,[],[f73]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_5024,plain,
% 11.32/1.98      ( r2_hidden(sK1(X0,X1,X1),X1)
% 11.32/1.98      | k1_setfam_1(k2_tarski(X0,X1)) = X1 ),
% 11.32/1.98      inference(factoring,[status(thm)],[c_4]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_320,plain,
% 11.32/1.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.32/1.98      theory(equality) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_315,plain,( X0 = X0 ),theory(equality) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_4643,plain,
% 11.32/1.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X1) | X2 != X0 ),
% 11.32/1.98      inference(resolution,[status(thm)],[c_320,c_315]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_5312,plain,
% 11.32/1.98      ( ~ m1_subset_1(X0,X1)
% 11.32/1.98      | m1_subset_1(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 11.32/1.98      | r2_hidden(sK1(X2,X0,X0),X0) ),
% 11.32/1.98      inference(resolution,[status(thm)],[c_5024,c_4643]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_11,plain,
% 11.32/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.32/1.98      inference(cnf_transformation,[],[f54]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_6100,plain,
% 11.32/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.32/1.98      | r2_hidden(sK1(X2,X0,X0),X0)
% 11.32/1.98      | r1_tarski(k1_setfam_1(k2_tarski(X2,X0)),X1) ),
% 11.32/1.98      inference(resolution,[status(thm)],[c_5312,c_11]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1,plain,
% 11.32/1.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.32/1.98      inference(cnf_transformation,[],[f44]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_980,plain,
% 11.32/1.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.32/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.32/1.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_7,plain,
% 11.32/1.98      ( r2_hidden(X0,X1)
% 11.32/1.98      | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 11.32/1.98      inference(cnf_transformation,[],[f81]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_974,plain,
% 11.32/1.98      ( r2_hidden(X0,X1) = iProver_top
% 11.32/1.98      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) != iProver_top ),
% 11.32/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_2032,plain,
% 11.32/1.98      ( r2_hidden(sK0(k1_setfam_1(k2_tarski(X0,X1)),X2),X1) = iProver_top
% 11.32/1.98      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
% 11.32/1.98      inference(superposition,[status(thm)],[c_980,c_974]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_2,plain,
% 11.32/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.32/1.98      inference(cnf_transformation,[],[f43]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_979,plain,
% 11.32/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.32/1.98      | r2_hidden(X0,X2) = iProver_top
% 11.32/1.98      | r1_tarski(X1,X2) != iProver_top ),
% 11.32/1.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_4356,plain,
% 11.32/1.98      ( r2_hidden(sK0(k1_setfam_1(k2_tarski(X0,X1)),X2),X3) = iProver_top
% 11.32/1.98      | r1_tarski(X1,X3) != iProver_top
% 11.32/1.98      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) = iProver_top ),
% 11.32/1.98      inference(superposition,[status(thm)],[c_2032,c_979]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_0,plain,
% 11.32/1.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.32/1.98      inference(cnf_transformation,[],[f45]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_981,plain,
% 11.32/1.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.32/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.32/1.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_13327,plain,
% 11.32/1.98      ( r1_tarski(X0,X1) != iProver_top
% 11.32/1.98      | r1_tarski(k1_setfam_1(k2_tarski(X2,X0)),X1) = iProver_top ),
% 11.32/1.98      inference(superposition,[status(thm)],[c_4356,c_981]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_13420,plain,
% 11.32/1.98      ( ~ r1_tarski(X0,X1)
% 11.32/1.98      | r1_tarski(k1_setfam_1(k2_tarski(X2,X0)),X1) ),
% 11.32/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_13327]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_41580,plain,
% 11.32/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.32/1.98      | r1_tarski(k1_setfam_1(k2_tarski(X2,X0)),X1) ),
% 11.32/1.98      inference(global_propositional_subsumption,
% 11.32/1.98                [status(thm)],
% 11.32/1.98                [c_6100,c_11,c_13420]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_12,plain,
% 11.32/1.98      ( m1_subset_1(X0,X1)
% 11.32/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.32/1.98      | ~ r2_hidden(X0,X2) ),
% 11.32/1.98      inference(cnf_transformation,[],[f56]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_18,plain,
% 11.32/1.98      ( ~ v3_pre_topc(X0,X1)
% 11.32/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.32/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.32/1.98      | ~ r2_hidden(X2,X0)
% 11.32/1.98      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 11.32/1.98      | v2_struct_0(X1)
% 11.32/1.98      | ~ v2_pre_topc(X1)
% 11.32/1.98      | ~ l1_pre_topc(X1) ),
% 11.32/1.98      inference(cnf_transformation,[],[f64]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_2352,plain,
% 11.32/1.98      ( ~ v3_pre_topc(X0,X1)
% 11.32/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.32/1.98      | ~ r2_hidden(X2,X0)
% 11.32/1.98      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 11.32/1.98      | v2_struct_0(X1)
% 11.32/1.98      | ~ v2_pre_topc(X1)
% 11.32/1.98      | ~ l1_pre_topc(X1) ),
% 11.32/1.98      inference(backward_subsumption_resolution,
% 11.32/1.98                [status(thm)],
% 11.32/1.98                [c_12,c_18]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_21,negated_conjecture,
% 11.32/1.98      ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 11.32/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_9,plain,
% 11.32/1.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 11.32/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1715,plain,
% 11.32/1.98      ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 11.32/1.98      inference(resolution,[status(thm)],[c_21,c_9]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_39381,plain,
% 11.32/1.98      ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
% 11.32/1.98      | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.32/1.98      | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6)))
% 11.32/1.98      | v2_struct_0(sK3)
% 11.32/1.98      | ~ v2_pre_topc(sK3)
% 11.32/1.98      | ~ l1_pre_topc(sK3) ),
% 11.32/1.98      inference(resolution,[status(thm)],[c_2352,c_1715]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_27,negated_conjecture,
% 11.32/1.98      ( ~ v2_struct_0(sK3) ),
% 11.32/1.98      inference(cnf_transformation,[],[f65]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_26,negated_conjecture,
% 11.32/1.98      ( v2_pre_topc(sK3) ),
% 11.32/1.98      inference(cnf_transformation,[],[f66]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_25,negated_conjecture,
% 11.32/1.98      ( l1_pre_topc(sK3) ),
% 11.32/1.98      inference(cnf_transformation,[],[f67]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_40708,plain,
% 11.32/1.98      ( ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6)))
% 11.32/1.98      | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.32/1.98      | ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3) ),
% 11.32/1.98      inference(global_propositional_subsumption,
% 11.32/1.98                [status(thm)],
% 11.32/1.98                [c_39381,c_27,c_26,c_25]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_40709,plain,
% 11.32/1.98      ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
% 11.32/1.98      | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK3)))
% 11.32/1.98      | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) ),
% 11.32/1.98      inference(renaming,[status(thm)],[c_40708]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_10,plain,
% 11.32/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.32/1.98      inference(cnf_transformation,[],[f55]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_40730,plain,
% 11.32/1.98      ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
% 11.32/1.98      | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6)))
% 11.32/1.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK5,sK6)),u1_struct_0(sK3)) ),
% 11.32/1.98      inference(resolution,[status(thm)],[c_40709,c_10]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_41694,plain,
% 11.32/1.98      ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
% 11.32/1.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.32/1.98      | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) ),
% 11.32/1.98      inference(resolution,[status(thm)],[c_41580,c_40730]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_24,negated_conjecture,
% 11.32/1.98      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 11.32/1.98      inference(cnf_transformation,[],[f68]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_22,negated_conjecture,
% 11.32/1.98      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 11.32/1.98      inference(cnf_transformation,[],[f70]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_959,plain,
% 11.32/1.98      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 11.32/1.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_16,plain,
% 11.32/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.32/1.98      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 11.32/1.98      | v2_struct_0(X1)
% 11.32/1.98      | ~ v2_pre_topc(X1)
% 11.32/1.98      | ~ l1_pre_topc(X1)
% 11.32/1.98      | sK2(X1,X0,X2) = X2 ),
% 11.32/1.98      inference(cnf_transformation,[],[f59]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_965,plain,
% 11.32/1.98      ( sK2(X0,X1,X2) = X2
% 11.32/1.98      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 11.32/1.98      | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) != iProver_top
% 11.32/1.98      | v2_struct_0(X0) = iProver_top
% 11.32/1.98      | v2_pre_topc(X0) != iProver_top
% 11.32/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.32/1.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_3237,plain,
% 11.32/1.98      ( sK2(sK3,sK4,sK6) = sK6
% 11.32/1.98      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 11.32/1.98      | v2_struct_0(sK3) = iProver_top
% 11.32/1.98      | v2_pre_topc(sK3) != iProver_top
% 11.32/1.98      | l1_pre_topc(sK3) != iProver_top ),
% 11.32/1.98      inference(superposition,[status(thm)],[c_959,c_965]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1312,plain,
% 11.32/1.98      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 11.32/1.98      | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 11.32/1.98      | v2_struct_0(sK3)
% 11.32/1.98      | ~ v2_pre_topc(sK3)
% 11.32/1.98      | ~ l1_pre_topc(sK3)
% 11.32/1.98      | sK2(sK3,sK4,sK6) = sK6 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_16]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_26368,plain,
% 11.32/1.98      ( sK2(sK3,sK4,sK6) = sK6 ),
% 11.32/1.98      inference(global_propositional_subsumption,
% 11.32/1.98                [status(thm)],
% 11.32/1.98                [c_3237,c_27,c_26,c_25,c_24,c_22,c_1312]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_17,plain,
% 11.32/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.32/1.98      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 11.32/1.98      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 11.32/1.98      | v2_struct_0(X1)
% 11.32/1.98      | ~ v2_pre_topc(X1)
% 11.32/1.98      | ~ l1_pre_topc(X1) ),
% 11.32/1.98      inference(cnf_transformation,[],[f58]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_964,plain,
% 11.32/1.98      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 11.32/1.98      | m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0))) != iProver_top
% 11.32/1.98      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.32/1.98      | v2_struct_0(X1) = iProver_top
% 11.32/1.98      | v2_pre_topc(X1) != iProver_top
% 11.32/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.32/1.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_26372,plain,
% 11.32/1.98      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 11.32/1.98      | m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 11.32/1.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 11.32/1.98      | v2_struct_0(sK3) = iProver_top
% 11.32/1.98      | v2_pre_topc(sK3) != iProver_top
% 11.32/1.98      | l1_pre_topc(sK3) != iProver_top ),
% 11.32/1.98      inference(superposition,[status(thm)],[c_26368,c_964]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_26398,plain,
% 11.32/1.98      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 11.32/1.98      | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 11.32/1.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.32/1.98      | v2_struct_0(sK3)
% 11.32/1.98      | ~ v2_pre_topc(sK3)
% 11.32/1.98      | ~ l1_pre_topc(sK3) ),
% 11.32/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_26372]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_41697,plain,
% 11.32/1.98      ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK5,sK6)),sK3)
% 11.32/1.98      | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) ),
% 11.32/1.98      inference(global_propositional_subsumption,
% 11.32/1.98                [status(thm)],
% 11.32/1.98                [c_41694,c_27,c_26,c_25,c_24,c_22,c_26398]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_13,plain,
% 11.32/1.98      ( ~ v3_pre_topc(X0,X1)
% 11.32/1.98      | ~ v3_pre_topc(X2,X1)
% 11.32/1.98      | v3_pre_topc(k1_setfam_1(k2_tarski(X2,X0)),X1)
% 11.32/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.32/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.32/1.98      | ~ v2_pre_topc(X1)
% 11.32/1.98      | ~ l1_pre_topc(X1) ),
% 11.32/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_41713,plain,
% 11.32/1.98      ( ~ v3_pre_topc(sK6,sK3)
% 11.32/1.98      | ~ v3_pre_topc(sK5,sK3)
% 11.32/1.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.32/1.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.32/1.98      | ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6)))
% 11.32/1.98      | ~ v2_pre_topc(sK3)
% 11.32/1.98      | ~ l1_pre_topc(sK3) ),
% 11.32/1.98      inference(resolution,[status(thm)],[c_41697,c_13]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_23,negated_conjecture,
% 11.32/1.98      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 11.32/1.98      inference(cnf_transformation,[],[f69]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_14,plain,
% 11.32/1.98      ( v3_pre_topc(sK2(X0,X1,X2),X0)
% 11.32/1.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.32/1.98      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 11.32/1.98      | v2_struct_0(X0)
% 11.32/1.98      | ~ v2_pre_topc(X0)
% 11.32/1.98      | ~ l1_pre_topc(X0) ),
% 11.32/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1300,plain,
% 11.32/1.98      ( v3_pre_topc(sK2(sK3,sK4,sK6),sK3)
% 11.32/1.98      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 11.32/1.98      | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 11.32/1.98      | v2_struct_0(sK3)
% 11.32/1.98      | ~ v2_pre_topc(sK3)
% 11.32/1.98      | ~ l1_pre_topc(sK3) ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_14]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1303,plain,
% 11.32/1.98      ( v3_pre_topc(sK2(sK3,sK4,sK5),sK3)
% 11.32/1.98      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 11.32/1.98      | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 11.32/1.98      | v2_struct_0(sK3)
% 11.32/1.98      | ~ v2_pre_topc(sK3)
% 11.32/1.98      | ~ l1_pre_topc(sK3) ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_14]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1315,plain,
% 11.32/1.98      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 11.32/1.98      | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 11.32/1.98      | v2_struct_0(sK3)
% 11.32/1.98      | ~ v2_pre_topc(sK3)
% 11.32/1.98      | ~ l1_pre_topc(sK3)
% 11.32/1.98      | sK2(sK3,sK4,sK5) = sK5 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_16]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1925,plain,
% 11.32/1.98      ( sK6 = sK6 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_315]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_316,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1633,plain,
% 11.32/1.98      ( X0 != X1 | X0 = sK2(sK3,sK4,sK6) | sK2(sK3,sK4,sK6) != X1 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_316]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_3593,plain,
% 11.32/1.98      ( X0 = sK2(sK3,sK4,sK6) | X0 != sK6 | sK2(sK3,sK4,sK6) != sK6 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_1633]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_3871,plain,
% 11.32/1.98      ( sK2(sK3,sK4,sK6) != sK6 | sK6 = sK2(sK3,sK4,sK6) | sK6 != sK6 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_3593]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1654,plain,
% 11.32/1.98      ( X0 != X1 | X0 = sK2(sK3,sK4,sK5) | sK2(sK3,sK4,sK5) != X1 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_316]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_3602,plain,
% 11.32/1.98      ( X0 = sK2(sK3,sK4,sK5) | X0 != sK5 | sK2(sK3,sK4,sK5) != sK5 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_1654]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_3876,plain,
% 11.32/1.98      ( sK2(sK3,sK4,sK5) != sK5 | sK5 = sK2(sK3,sK4,sK5) | sK5 != sK5 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_3602]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_3877,plain,
% 11.32/1.98      ( sK5 = sK5 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_315]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_322,plain,
% 11.32/1.98      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X1) | X2 != X0 ),
% 11.32/1.98      theory(equality) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1375,plain,
% 11.32/1.98      ( v3_pre_topc(X0,sK3)
% 11.32/1.98      | ~ v3_pre_topc(sK2(sK3,sK4,sK6),sK3)
% 11.32/1.98      | X0 != sK2(sK3,sK4,sK6) ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_322]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_11257,plain,
% 11.32/1.98      ( ~ v3_pre_topc(sK2(sK3,sK4,sK6),sK3)
% 11.32/1.98      | v3_pre_topc(sK6,sK3)
% 11.32/1.98      | sK6 != sK2(sK3,sK4,sK6) ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_1375]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1385,plain,
% 11.32/1.98      ( v3_pre_topc(X0,sK3)
% 11.32/1.98      | ~ v3_pre_topc(sK2(sK3,sK4,sK5),sK3)
% 11.32/1.98      | X0 != sK2(sK3,sK4,sK5) ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_322]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_11269,plain,
% 11.32/1.98      ( ~ v3_pre_topc(sK2(sK3,sK4,sK5),sK3)
% 11.32/1.98      | v3_pre_topc(sK5,sK3)
% 11.32/1.98      | sK5 != sK2(sK3,sK4,sK5) ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_1385]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_958,plain,
% 11.32/1.98      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 11.32/1.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_3238,plain,
% 11.32/1.98      ( sK2(sK3,sK4,sK5) = sK5
% 11.32/1.98      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 11.32/1.98      | v2_struct_0(sK3) = iProver_top
% 11.32/1.98      | v2_pre_topc(sK3) != iProver_top
% 11.32/1.98      | l1_pre_topc(sK3) != iProver_top ),
% 11.32/1.98      inference(superposition,[status(thm)],[c_958,c_965]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_26832,plain,
% 11.32/1.98      ( sK2(sK3,sK4,sK5) = sK5 ),
% 11.32/1.98      inference(global_propositional_subsumption,
% 11.32/1.98                [status(thm)],
% 11.32/1.98                [c_3238,c_27,c_26,c_25,c_24,c_23,c_1315]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_26836,plain,
% 11.32/1.98      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 11.32/1.98      | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 11.32/1.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 11.32/1.98      | v2_struct_0(sK3) = iProver_top
% 11.32/1.98      | v2_pre_topc(sK3) != iProver_top
% 11.32/1.98      | l1_pre_topc(sK3) != iProver_top ),
% 11.32/1.98      inference(superposition,[status(thm)],[c_26832,c_964]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_26862,plain,
% 11.32/1.98      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 11.32/1.98      | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 11.32/1.98      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 11.32/1.98      | v2_struct_0(sK3)
% 11.32/1.98      | ~ v2_pre_topc(sK3)
% 11.32/1.98      | ~ l1_pre_topc(sK3) ),
% 11.32/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_26836]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_41981,plain,
% 11.32/1.98      ( ~ r2_hidden(sK4,k1_setfam_1(k2_tarski(sK5,sK6))) ),
% 11.32/1.98      inference(global_propositional_subsumption,
% 11.32/1.98                [status(thm)],
% 11.32/1.98                [c_41713,c_27,c_26,c_25,c_24,c_23,c_22,c_1300,c_1303,
% 11.32/1.98                 c_1312,c_1315,c_1925,c_3871,c_3876,c_3877,c_11257,
% 11.32/1.98                 c_11269,c_26398,c_26862]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_6,plain,
% 11.32/1.98      ( ~ r2_hidden(X0,X1)
% 11.32/1.98      | ~ r2_hidden(X0,X2)
% 11.32/1.98      | r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 11.32/1.98      inference(cnf_transformation,[],[f80]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_41993,plain,
% 11.32/1.98      ( ~ r2_hidden(sK4,sK6) | ~ r2_hidden(sK4,sK5) ),
% 11.32/1.98      inference(resolution,[status(thm)],[c_41981,c_6]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_317,plain,
% 11.32/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.32/1.98      theory(equality) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_2841,plain,
% 11.32/1.98      ( r2_hidden(X0,X1) | ~ r2_hidden(sK4,X2) | X1 != X2 | X0 != sK4 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_317]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_7102,plain,
% 11.32/1.98      ( ~ r2_hidden(sK4,X0) | r2_hidden(sK4,X1) | X1 != X0 | sK4 != sK4 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_2841]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_14409,plain,
% 11.32/1.98      ( r2_hidden(sK4,X0)
% 11.32/1.98      | ~ r2_hidden(sK4,sK2(sK3,sK4,sK5))
% 11.32/1.98      | X0 != sK2(sK3,sK4,sK5)
% 11.32/1.98      | sK4 != sK4 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_7102]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_18560,plain,
% 11.32/1.98      ( ~ r2_hidden(sK4,sK2(sK3,sK4,sK5))
% 11.32/1.98      | r2_hidden(sK4,sK5)
% 11.32/1.98      | sK4 != sK4
% 11.32/1.98      | sK5 != sK2(sK3,sK4,sK5) ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_14409]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_14404,plain,
% 11.32/1.98      ( r2_hidden(sK4,X0)
% 11.32/1.98      | ~ r2_hidden(sK4,sK2(sK3,sK4,sK6))
% 11.32/1.98      | X0 != sK2(sK3,sK4,sK6)
% 11.32/1.98      | sK4 != sK4 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_7102]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_18553,plain,
% 11.32/1.98      ( ~ r2_hidden(sK4,sK2(sK3,sK4,sK6))
% 11.32/1.98      | r2_hidden(sK4,sK6)
% 11.32/1.98      | sK4 != sK4
% 11.32/1.98      | sK6 != sK2(sK3,sK4,sK6) ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_14404]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1535,plain,
% 11.32/1.98      ( sK4 = sK4 ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_315]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_15,plain,
% 11.32/1.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 11.32/1.98      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 11.32/1.98      | r2_hidden(X0,sK2(X1,X0,X2))
% 11.32/1.98      | v2_struct_0(X1)
% 11.32/1.98      | ~ v2_pre_topc(X1)
% 11.32/1.98      | ~ l1_pre_topc(X1) ),
% 11.32/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1309,plain,
% 11.32/1.98      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 11.32/1.98      | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 11.32/1.98      | r2_hidden(sK4,sK2(sK3,sK4,sK5))
% 11.32/1.98      | v2_struct_0(sK3)
% 11.32/1.98      | ~ v2_pre_topc(sK3)
% 11.32/1.98      | ~ l1_pre_topc(sK3) ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_15]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(c_1306,plain,
% 11.32/1.98      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 11.32/1.98      | ~ m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
% 11.32/1.98      | r2_hidden(sK4,sK2(sK3,sK4,sK6))
% 11.32/1.98      | v2_struct_0(sK3)
% 11.32/1.98      | ~ v2_pre_topc(sK3)
% 11.32/1.98      | ~ l1_pre_topc(sK3) ),
% 11.32/1.98      inference(instantiation,[status(thm)],[c_15]) ).
% 11.32/1.98  
% 11.32/1.98  cnf(contradiction,plain,
% 11.32/1.98      ( $false ),
% 11.32/1.98      inference(minisat,
% 11.32/1.98                [status(thm)],
% 11.32/1.98                [c_41993,c_18560,c_18553,c_3877,c_3876,c_3871,c_1925,
% 11.32/1.98                 c_1535,c_1315,c_1312,c_1309,c_1306,c_22,c_23,c_24,c_25,
% 11.32/1.98                 c_26,c_27]) ).
% 11.32/1.98  
% 11.32/1.98  
% 11.32/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.32/1.98  
% 11.32/1.98  ------                               Statistics
% 11.32/1.98  
% 11.32/1.98  ------ Selected
% 11.32/1.98  
% 11.32/1.98  total_time:                             1.137
% 11.32/1.98  
%------------------------------------------------------------------------------
