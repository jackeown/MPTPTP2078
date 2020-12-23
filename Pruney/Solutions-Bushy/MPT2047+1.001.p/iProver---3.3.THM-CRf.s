%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2047+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:04 EST 2020

% Result     : Theorem 11.45s
% Output     : CNFRefutation 11.45s
% Verified   : 
% Statistics : Number of formulae       :  235 (1254 expanded)
%              Number of clauses        :  132 ( 247 expanded)
%              Number of leaves         :   26 ( 363 expanded)
%              Depth                    :   26
%              Number of atoms          : 1160 (17528 expanded)
%              Number of equality atoms :  175 ( 289 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f68,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f67,f68])).

fof(f110,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f17,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f114,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f139,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f114,f87])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f62])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f63])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f64,f65])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f143,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f144,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f93])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f141,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f82])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
             => ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_waybel_7(X0,X2,X1)
                  | ~ r1_tarski(k1_yellow19(X0,X1),X2) )
                & ( r1_tarski(k1_yellow19(X0,X1),X2)
                  | ~ r2_waybel_7(X0,X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X2,X1)
      | ~ r1_tarski(k1_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                        & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                        & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ( r2_waybel_7(X0,X3,X2)
                       => r2_hidden(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                          & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                          & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ( r2_waybel_7(X0,X3,X2)
                         => r2_hidden(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r2_waybel_7(X0,X3,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r2_waybel_7(X0,X3,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f74,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(X0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r2_waybel_7(X0,X3,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f75,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(X0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r2_waybel_7(X0,X3,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f76,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(X0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X1,X5)
                    | ~ r2_waybel_7(X0,X5,X4)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X5) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f75])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r2_waybel_7(X0,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X3) )
     => ( ~ r2_hidden(X1,sK6)
        & r2_waybel_7(X0,sK6,X2)
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK6,k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r2_waybel_7(X0,X3,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
              & ~ v1_xboole_0(X3) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_waybel_7(X0,X3,sK5)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X3) )
        & r2_hidden(sK5,X1)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(X0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X1,X5)
                    | ~ r2_waybel_7(X0,X5,X4)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X5) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(sK4,X3)
                  & r2_waybel_7(X0,X3,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              & r2_hidden(X2,sK4)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_pre_topc(sK4,X0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(sK4,X5)
                  | ~ r2_waybel_7(X0,X5,X4)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                  | v1_xboole_0(X5) )
              | ~ r2_hidden(X4,sK4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | v3_pre_topc(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X1,X3)
                      & r2_waybel_7(X0,X3,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X3) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X1,X5)
                      | ~ r2_waybel_7(X0,X5,X4)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X5) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(sK3,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK3)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK3)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(sK3)) )
            | ~ v3_pre_topc(X1,sK3) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X1,X5)
                    | ~ r2_waybel_7(sK3,X5,X4)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
                    | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK3)))
                    | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK3)))
                    | v1_xboole_0(X5) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
            | v3_pre_topc(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,
    ( ( ( ~ r2_hidden(sK4,sK6)
        & r2_waybel_7(sK3,sK6,sK5)
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
        & v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK3)))
        & v2_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK3)))
        & ~ v1_xboole_0(sK6)
        & r2_hidden(sK5,sK4)
        & m1_subset_1(sK5,u1_struct_0(sK3)) )
      | ~ v3_pre_topc(sK4,sK3) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(sK4,X5)
              | ~ r2_waybel_7(sK3,X5,X4)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
              | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK3)))
              | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK3)))
              | v1_xboole_0(X5) )
          | ~ r2_hidden(X4,sK4)
          | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
      | v3_pre_topc(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f76,f80,f79,f78,f77])).

fof(f124,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

fof(f125,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f81])).

fof(f126,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f81])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f58])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(X2,sK0(X0,X1,X2))
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(X2,sK0(X0,X1,X2))
              & v3_pre_topc(sK0(X0,X1,X2),X0)
              & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f59,f60])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK0(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f128,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4,X5)
      | ~ r2_waybel_7(sK3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
      | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK3)))
      | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK3)))
      | v1_xboole_0(X5)
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | v3_pre_topc(sK4,sK3) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f135,plain,
    ( r2_waybel_7(sK3,sK6,sK5)
    | ~ v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f81])).

fof(f127,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f81])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f130,plain,
    ( r2_hidden(sK5,sK4)
    | ~ v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f81])).

fof(f136,plain,
    ( ~ r2_hidden(sK4,sK6)
    | ~ v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f81])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k1_yellow19(X0,X1))
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( m1_connsp_2(X2,X0,X1)
                | ~ r2_hidden(X2,k1_yellow19(X0,X1)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f112,f87])).

fof(f84,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_28,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_5581,plain,
    ( X0 = X1
    | r2_hidden(sK2(X1,X0),X0) = iProver_top
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_31,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f139])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_5587,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7453,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_5587])).

cnf(c_18,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_40,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1098,plain,
    ( ~ r2_hidden(X0,X1)
    | o_0_0_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_40])).

cnf(c_1099,plain,
    ( ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(unflattening,[status(thm)],[c_1098])).

cnf(c_1100,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1099])).

cnf(c_7508,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7453,c_1100])).

cnf(c_8298,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(sK2(o_0_0_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5581,c_7508])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_5586,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10224,plain,
    ( k4_xboole_0(X0,X1) = o_0_0_xboole_0
    | r2_hidden(sK2(o_0_0_xboole_0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8298,c_5586])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_5592,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_38,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_tarski(k1_yellow19(X0,X2),X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_53,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_845,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_tarski(k1_yellow19(X0,X2),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_53])).

cnf(c_846,plain,
    ( r2_waybel_7(sK3,X0,X1)
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r1_tarski(k1_yellow19(sK3,X1),X0)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_845])).

cnf(c_52,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_51,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_850,plain,
    ( r2_waybel_7(sK3,X0,X1)
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r1_tarski(k1_yellow19(sK3,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_846,c_52,c_51])).

cnf(c_20,plain,
    ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_890,plain,
    ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_53])).

cnf(c_891,plain,
    ( v13_waybel_0(k1_yellow19(sK3,X0),k3_yellow_1(k2_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_890])).

cnf(c_895,plain,
    ( v13_waybel_0(k1_yellow19(sK3,X0),k3_yellow_1(k2_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_891,c_52,c_51])).

cnf(c_1219,plain,
    ( r2_waybel_7(sK3,X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r1_tarski(k1_yellow19(sK3,X1),X0)
    | k1_yellow19(sK3,X2) != X0
    | k3_yellow_1(k2_struct_0(sK3)) != k3_yellow_1(k2_struct_0(sK3)) ),
    inference(resolution_lifted,[status(thm)],[c_850,c_895])).

cnf(c_1220,plain,
    ( r2_waybel_7(sK3,k1_yellow19(sK3,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k1_yellow19(sK3,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    | ~ r1_tarski(k1_yellow19(sK3,X1),k1_yellow19(sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_1219])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_yellow19(X1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_992,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_yellow19(X1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_53])).

cnf(c_993,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k1_yellow19(sK3,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_992])).

cnf(c_997,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k1_yellow19(sK3,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_993,c_52,c_51])).

cnf(c_1224,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_waybel_7(sK3,k1_yellow19(sK3,X0),X1)
    | ~ r1_tarski(k1_yellow19(sK3,X1),k1_yellow19(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1220,c_52,c_51,c_993])).

cnf(c_1225,plain,
    ( r2_waybel_7(sK3,k1_yellow19(sK3,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r1_tarski(k1_yellow19(sK3,X1),k1_yellow19(sK3,X0)) ),
    inference(renaming,[status(thm)],[c_1224])).

cnf(c_5557,plain,
    ( r2_waybel_7(sK3,k1_yellow19(sK3,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(k1_yellow19(sK3,X1),k1_yellow19(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1225])).

cnf(c_8043,plain,
    ( r2_waybel_7(sK3,k1_yellow19(sK3,X0),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5592,c_5557])).

cnf(c_6,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK0(X0,X1,X2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1364,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK0(X0,X1,X2))
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_52])).

cnf(c_1365,plain,
    ( r2_waybel_7(sK3,X0,X1)
    | r2_hidden(X1,sK0(sK3,X0,X1))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1364])).

cnf(c_1369,plain,
    ( r2_hidden(X1,sK0(sK3,X0,X1))
    | r2_waybel_7(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1365,c_51])).

cnf(c_1370,plain,
    ( r2_waybel_7(sK3,X0,X1)
    | r2_hidden(X1,sK0(sK3,X0,X1)) ),
    inference(renaming,[status(thm)],[c_1369])).

cnf(c_5551,plain,
    ( r2_waybel_7(sK3,X0,X1) = iProver_top
    | r2_hidden(X1,sK0(sK3,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1370])).

cnf(c_8,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1328,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_52])).

cnf(c_1329,plain,
    ( r2_waybel_7(sK3,X0,X1)
    | m1_subset_1(sK0(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1328])).

cnf(c_1333,plain,
    ( m1_subset_1(sK0(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_waybel_7(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1329,c_51])).

cnf(c_1334,plain,
    ( r2_waybel_7(sK3,X0,X1)
    | m1_subset_1(sK0(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_1333])).

cnf(c_5553,plain,
    ( r2_waybel_7(sK3,X0,X1) = iProver_top
    | m1_subset_1(sK0(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1334])).

cnf(c_37,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_5576,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_8467,plain,
    ( r2_waybel_7(sK3,X0,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X2,sK0(sK3,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5553,c_5576])).

cnf(c_10428,plain,
    ( r2_waybel_7(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5551,c_8467])).

cnf(c_17171,plain,
    ( r2_waybel_7(sK3,k1_yellow19(sK3,X0),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8043,c_10428])).

cnf(c_49,negated_conjecture,
    ( ~ r2_waybel_7(sK3,X0,X1)
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK3)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK3)))
    | v3_pre_topc(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,sK4)
    | r2_hidden(sK4,X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_21,plain,
    ( v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_872,plain,
    ( v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_53])).

cnf(c_873,plain,
    ( v2_waybel_0(k1_yellow19(sK3,X0),k3_yellow_1(k2_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_872])).

cnf(c_877,plain,
    ( v2_waybel_0(k1_yellow19(sK3,X0),k3_yellow_1(k2_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_873,c_52,c_51])).

cnf(c_1049,plain,
    ( ~ r2_waybel_7(sK3,X0,X1)
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK3)))
    | v3_pre_topc(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X1,sK4)
    | r2_hidden(sK4,X0)
    | v1_xboole_0(X0)
    | k1_yellow19(sK3,X2) != X0
    | k3_yellow_1(k2_struct_0(sK3)) != k3_yellow_1(k2_struct_0(sK3)) ),
    inference(resolution_lifted,[status(thm)],[c_49,c_877])).

cnf(c_1050,plain,
    ( ~ r2_waybel_7(sK3,k1_yellow19(sK3,X0),X1)
    | ~ v13_waybel_0(k1_yellow19(sK3,X0),k3_yellow_1(k2_struct_0(sK3)))
    | v3_pre_topc(sK4,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k1_yellow19(sK3,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    | ~ r2_hidden(X1,sK4)
    | r2_hidden(sK4,k1_yellow19(sK3,X0))
    | v1_xboole_0(k1_yellow19(sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_1049])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k1_yellow19(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_956,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k1_yellow19(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_53])).

cnf(c_957,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_xboole_0(k1_yellow19(sK3,X0))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_956])).

cnf(c_961,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v1_xboole_0(k1_yellow19(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_957,c_52,c_51])).

cnf(c_1054,plain,
    ( r2_hidden(sK4,k1_yellow19(sK3,X0))
    | ~ r2_hidden(X1,sK4)
    | ~ r2_waybel_7(sK3,k1_yellow19(sK3,X0),X1)
    | v3_pre_topc(sK4,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1050,c_52,c_51,c_895,c_961,c_993])).

cnf(c_1055,plain,
    ( ~ r2_waybel_7(sK3,k1_yellow19(sK3,X0),X1)
    | v3_pre_topc(sK4,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X1,sK4)
    | r2_hidden(sK4,k1_yellow19(sK3,X0)) ),
    inference(renaming,[status(thm)],[c_1054])).

cnf(c_5560,plain,
    ( r2_waybel_7(sK3,k1_yellow19(sK3,X0),X1) != iProver_top
    | v3_pre_topc(sK4,sK3) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(sK4,k1_yellow19(sK3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1055])).

cnf(c_897,plain,
    ( v13_waybel_0(k1_yellow19(sK3,X0),k3_yellow_1(k2_struct_0(sK3))) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_895])).

cnf(c_963,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(k1_yellow19(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_961])).

cnf(c_999,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_yellow19(sK3,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_997])).

cnf(c_1051,plain,
    ( r2_waybel_7(sK3,k1_yellow19(sK3,X0),X1) != iProver_top
    | v13_waybel_0(k1_yellow19(sK3,X0),k3_yellow_1(k2_struct_0(sK3))) != iProver_top
    | v3_pre_topc(sK4,sK3) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_yellow19(sK3,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(sK4,k1_yellow19(sK3,X0)) = iProver_top
    | v1_xboole_0(k1_yellow19(sK3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1050])).

cnf(c_42,negated_conjecture,
    ( r2_waybel_7(sK3,sK6,sK5)
    | ~ v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_5573,plain,
    ( r2_waybel_7(sK3,sK6,sK5) = iProver_top
    | v3_pre_topc(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_50,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_5568,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_9,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1305,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_52])).

cnf(c_1306,plain,
    ( ~ r2_waybel_7(sK3,X0,X1)
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1305])).

cnf(c_1308,plain,
    ( r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X2,sK3)
    | ~ r2_waybel_7(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1306,c_51])).

cnf(c_1309,plain,
    ( ~ r2_waybel_7(sK3,X0,X1)
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_1308])).

cnf(c_5554,plain,
    ( r2_waybel_7(sK3,X0,X1) != iProver_top
    | v3_pre_topc(X2,sK3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1309])).

cnf(c_6878,plain,
    ( r2_waybel_7(sK3,X0,X1) != iProver_top
    | v3_pre_topc(sK4,sK3) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5568,c_5554])).

cnf(c_6959,plain,
    ( v3_pre_topc(sK4,sK3) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5573,c_6878])).

cnf(c_47,negated_conjecture,
    ( ~ v3_pre_topc(sK4,sK3)
    | r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_62,plain,
    ( v3_pre_topc(sK4,sK3) != iProver_top
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_41,negated_conjecture,
    ( ~ v3_pre_topc(sK4,sK3)
    | ~ r2_hidden(sK4,sK6) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_68,plain,
    ( v3_pre_topc(sK4,sK3) != iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_6962,plain,
    ( v3_pre_topc(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6959,c_62,c_68])).

cnf(c_7181,plain,
    ( r2_waybel_7(sK3,k1_yellow19(sK3,X0),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(sK4,k1_yellow19(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5560,c_62,c_68,c_897,c_963,c_999,c_1051,c_6959])).

cnf(c_17177,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK4,k1_yellow19(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17171,c_7181])).

cnf(c_8465,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5568,c_5576])).

cnf(c_17266,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(sK4,k1_yellow19(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17177,c_8465])).

cnf(c_35,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_4,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_749,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_35,c_4])).

cnf(c_932,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_749,c_53])).

cnf(c_933,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X0,k1_yellow19(sK3,X1))
    | r2_hidden(X1,k1_tops_1(sK3,X0))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_932])).

cnf(c_937,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X0,k1_yellow19(sK3,X1))
    | r2_hidden(X1,k1_tops_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_933,c_52,c_51])).

cnf(c_5564,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_yellow19(sK3,X1)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_6705,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK3,sK4)) = iProver_top
    | r2_hidden(sK4,k1_yellow19(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5568,c_5564])).

cnf(c_17277,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_17266,c_6705])).

cnf(c_17313,plain,
    ( r2_hidden(X0,k1_tops_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17277,c_8465])).

cnf(c_10225,plain,
    ( k4_xboole_0(X0,X1) = o_0_0_xboole_0
    | r2_hidden(sK2(o_0_0_xboole_0,k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8298,c_5587])).

cnf(c_25822,plain,
    ( k4_xboole_0(X0,k1_tops_1(sK3,sK4)) = o_0_0_xboole_0
    | r2_hidden(sK2(o_0_0_xboole_0,k4_xboole_0(X0,k1_tops_1(sK3,sK4))),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_17313,c_10225])).

cnf(c_43603,plain,
    ( k4_xboole_0(sK4,k1_tops_1(sK3,sK4)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_10224,c_25822])).

cnf(c_30,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_7420,plain,
    ( r1_tarski(sK4,k1_tops_1(sK3,sK4))
    | k4_xboole_0(sK4,k1_tops_1(sK3,sK4)) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6200,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK3,sK4))
    | ~ r1_tarski(k1_tops_1(sK3,sK4),X0)
    | X0 = k1_tops_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6765,plain,
    ( ~ r1_tarski(k1_tops_1(sK3,sK4),sK4)
    | ~ r1_tarski(sK4,k1_tops_1(sK3,sK4))
    | sK4 = k1_tops_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_6200])).

cnf(c_4526,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6015,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(k1_tops_1(sK3,sK4),sK3)
    | X0 != k1_tops_1(sK3,sK4)
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_4526])).

cnf(c_6346,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK3,sK4),sK3)
    | v3_pre_topc(sK4,sK3)
    | sK3 != sK3
    | sK4 != k1_tops_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_6015])).

cnf(c_6347,plain,
    ( sK3 != sK3
    | sK4 != k1_tops_1(sK3,sK4)
    | v3_pre_topc(k1_tops_1(sK3,sK4),sK3) != iProver_top
    | v3_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6346])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1421,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_51])).

cnf(c_1422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(k1_tops_1(sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_1421])).

cnf(c_5932,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(k1_tops_1(sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_23,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1287,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_52])).

cnf(c_1288,plain,
    ( v3_pre_topc(k1_tops_1(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1287])).

cnf(c_1292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(k1_tops_1(sK3,X0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1288,c_51])).

cnf(c_1293,plain,
    ( v3_pre_topc(k1_tops_1(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_1292])).

cnf(c_5924,plain,
    ( v3_pre_topc(k1_tops_1(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_5925,plain,
    ( v3_pre_topc(k1_tops_1(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5924])).

cnf(c_176,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_172,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_57,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43603,c_7420,c_6962,c_6765,c_6347,c_5932,c_5925,c_176,c_172,c_57,c_50])).


%------------------------------------------------------------------------------
