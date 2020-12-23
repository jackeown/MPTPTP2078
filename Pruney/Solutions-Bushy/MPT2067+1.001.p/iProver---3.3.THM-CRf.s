%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2067+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:07 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  302 (1333 expanded)
%              Number of clauses        :  205 ( 293 expanded)
%              Number of leaves         :   21 ( 380 expanded)
%              Depth                    :   26
%              Number of atoms          : 2096 (20421 expanded)
%              Number of equality atoms :  223 ( 234 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal clause size      :   42 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ? [X3] :
                      ( r1_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X4] :
                    ( r1_waybel_7(X0,X4,X2)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X4) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f69])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r1_waybel_7(X0,X4,X2)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X4) )
     => ( r1_waybel_7(X0,sK5,X2)
        & r2_hidden(X1,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r1_waybel_7(X0,X3,X2)
                | ~ r2_hidden(X1,X3)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X3) )
            | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & ( ? [X4] :
                ( r1_waybel_7(X0,X4,X2)
                & r2_hidden(X1,X4)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X4) )
            | r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ! [X3] :
              ( ~ r1_waybel_7(X0,X3,sK4)
              | ~ r2_hidden(X1,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
              | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
              | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              | v1_xboole_0(X3) )
          | ~ r2_hidden(sK4,k2_pre_topc(X0,X1)) )
        & ( ? [X4] :
              ( r1_waybel_7(X0,X4,sK4)
              & r2_hidden(X1,X4)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X4) )
          | r2_hidden(sK4,k2_pre_topc(X0,X1)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X4] :
                    ( r1_waybel_7(X0,X4,X2)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X4) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r1_waybel_7(X0,X3,X2)
                  | ~ r2_hidden(sK3,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  | v1_xboole_0(X3) )
              | ~ r2_hidden(X2,k2_pre_topc(X0,sK3)) )
            & ( ? [X4] :
                  ( r1_waybel_7(X0,X4,X2)
                  & r2_hidden(sK3,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  & ~ v1_xboole_0(X4) )
              | r2_hidden(X2,k2_pre_topc(X0,sK3)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ? [X4] :
                      ( r1_waybel_7(X0,X4,X2)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X4) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(sK2,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK2)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK2)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(sK2,X1)) )
              & ( ? [X4] :
                    ( r1_waybel_7(sK2,X4,X2)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK2)))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK2)))
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
                    & ~ v1_xboole_0(X4) )
                | r2_hidden(X2,k2_pre_topc(sK2,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,
    ( ( ! [X3] :
          ( ~ r1_waybel_7(sK2,X3,sK4)
          | ~ r2_hidden(sK3,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
          | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK2)))
          | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK2)))
          | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
          | v1_xboole_0(X3) )
      | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) )
    & ( ( r1_waybel_7(sK2,sK5,sK4)
        & r2_hidden(sK3,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
        & v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
        & v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
        & v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
        & ~ v1_xboole_0(sK5) )
      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f70,f74,f73,f72,f71])).

fof(f121,plain,
    ( r1_waybel_7(sK2,sK5,sK4)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f75])).

fof(f110,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f111,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f112,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f114,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f75])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X3] :
                      ( r3_waybel_9(X0,X3,X2)
                      & r1_waybel_0(X0,X3,X1)
                      & l1_waybel_0(X3,X0)
                      & v7_waybel_0(X3)
                      & v4_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X4] :
                      ( r3_waybel_9(X0,X4,X2)
                      & r1_waybel_0(X0,X4,X1)
                      & l1_waybel_0(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f64])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X4,X2)
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r3_waybel_9(X0,sK1(X0,X1,X2),X2)
        & r1_waybel_0(X0,sK1(X0,X1,X2),X1)
        & l1_waybel_0(sK1(X0,X1,X2),X0)
        & v7_waybel_0(sK1(X0,X1,X2))
        & v4_orders_2(sK1(X0,X1,X2))
        & ~ v2_struct_0(sK1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ( r3_waybel_9(X0,sK1(X0,X1,X2),X2)
                    & r1_waybel_0(X0,sK1(X0,X1,X2),X1)
                    & l1_waybel_0(sK1(X0,X1,X2),X0)
                    & v7_waybel_0(sK1(X0,X1,X2))
                    & v4_orders_2(sK1(X0,X1,X2))
                    & ~ v2_struct_0(sK1(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f65,f66])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r3_waybel_9(X0,X3,X2)
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK1(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK1(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_yellow19(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f122,plain,(
    ! [X3] :
      ( ~ r1_waybel_7(sK2,X3,sK4)
      | ~ r2_hidden(sK3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK2)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK2)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
      | v1_xboole_0(X3)
      | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,sK1(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f120,plain,
    ( r2_hidden(sK3,sK5)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f75])).

fof(f119,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f75])).

fof(f118,plain,
    ( v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f75])).

fof(f117,plain,
    ( v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f75])).

fof(f116,plain,
    ( v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f75])).

fof(f115,plain,
    ( ~ v1_xboole_0(sK5)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f75])).

fof(f113,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_10730,plain,
    ( ~ r2_hidden(X0_58,X1_58)
    | r2_hidden(X2_58,X3_58)
    | X2_58 != X0_58
    | X3_58 != X1_58 ),
    theory(equality)).

cnf(c_12455,plain,
    ( r2_hidden(X0_58,X1_58)
    | ~ r2_hidden(sK3,sK5)
    | X1_58 != sK5
    | X0_58 != sK3 ),
    inference(instantiation,[status(thm)],[c_10730])).

cnf(c_12827,plain,
    ( r2_hidden(X0_58,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5)))
    | ~ r2_hidden(sK3,sK5)
    | X0_58 != sK3
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5)) != sK5 ),
    inference(instantiation,[status(thm)],[c_12455])).

cnf(c_12828,plain,
    ( X0_58 != sK3
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5)) != sK5
    | r2_hidden(X0_58,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5))) = iProver_top
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12827])).

cnf(c_12830,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5)) != sK5
    | sK3 != sK3
    | r2_hidden(sK3,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5))) = iProver_top
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12828])).

cnf(c_22,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_35,negated_conjecture,
    ( r1_waybel_7(sK2,sK5,sK4)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_571,plain,
    ( r3_waybel_9(X0,X1,X2)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k2_yellow19(X0,X1) != sK5
    | sK4 != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_35])).

cnf(c_572,plain,
    ( r3_waybel_9(sK2,X0,sK4)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | k2_yellow19(sK2,X0) != sK5 ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_45,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_44,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_576,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK2)
    | r3_waybel_9(sK2,X0,sK4)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k2_yellow19(sK2,X0) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_46,c_45,c_44,c_42])).

cnf(c_577,plain,
    ( r3_waybel_9(sK2,X0,sK4)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK5 ),
    inference(renaming,[status(thm)],[c_576])).

cnf(c_26,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | r2_hidden(X2,k2_pre_topc(X0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_663,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | r2_hidden(X2,k2_pre_topc(X0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_45])).

cnf(c_664,plain,
    ( ~ r3_waybel_9(sK2,X0,X1)
    | ~ r1_waybel_0(sK2,X0,X2)
    | r2_hidden(X1,k2_pre_topc(sK2,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_668,plain,
    ( v2_struct_0(X0)
    | ~ r3_waybel_9(sK2,X0,X1)
    | ~ r1_waybel_0(sK2,X0,X2)
    | r2_hidden(X1,k2_pre_topc(sK2,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_664,c_46,c_44])).

cnf(c_669,plain,
    ( ~ r3_waybel_9(sK2,X0,X1)
    | ~ r1_waybel_0(sK2,X0,X2)
    | r2_hidden(X1,k2_pre_topc(sK2,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_668])).

cnf(c_899,plain,
    ( ~ r1_waybel_0(sK2,X0,X1)
    | r2_hidden(X2,k2_pre_topc(sK2,X1))
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ l1_waybel_0(X3,sK2)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | X0 != X3
    | k2_yellow19(sK2,X3) != sK5
    | sK4 != X2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_577,c_669])).

cnf(c_900,plain,
    ( ~ r1_waybel_0(sK2,X0,X1)
    | r2_hidden(sK4,k2_pre_topc(sK2,X1))
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK5 ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_904,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | r2_hidden(sK4,k2_pre_topc(sK2,X1))
    | ~ r1_waybel_0(sK2,X0,X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_42])).

cnf(c_905,plain,
    ( ~ r1_waybel_0(sK2,X0,X1)
    | r2_hidden(sK4,k2_pre_topc(sK2,X1))
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK2,X0) != sK5 ),
    inference(renaming,[status(thm)],[c_904])).

cnf(c_10693,plain,
    ( ~ r1_waybel_0(sK2,X0_59,X0_58)
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_58))
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_waybel_0(X0_59,sK2)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59)
    | v2_struct_0(X0_59)
    | k2_yellow19(sK2,X0_59) != sK5 ),
    inference(subtyping,[status(esa)],[c_905])).

cnf(c_12661,plain,
    ( ~ r1_waybel_0(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5),X0_58)
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_58))
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5),sK2)
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK5))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5))
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5)) != sK5 ),
    inference(instantiation,[status(thm)],[c_10693])).

cnf(c_12662,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5)) != sK5
    | r1_waybel_0(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5),X0_58) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_58)) = iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5),sK2) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12661])).

cnf(c_12664,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5)) != sK5
    | r1_waybel_0(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5),sK3) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5),sK2) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12662])).

cnf(c_21,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_838,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_44])).

cnf(c_839,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_838])).

cnf(c_1255,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_839])).

cnf(c_1256,plain,
    ( r1_waybel_0(sK2,X0,X1)
    | ~ r2_hidden(X1,k2_yellow19(sK2,X0))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1255])).

cnf(c_1260,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK2)
    | ~ r2_hidden(X1,k2_yellow19(sK2,X0))
    | r1_waybel_0(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1256,c_46])).

cnf(c_1261,plain,
    ( r1_waybel_0(sK2,X0,X1)
    | ~ r2_hidden(X1,k2_yellow19(sK2,X0))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1260])).

cnf(c_10691,plain,
    ( r1_waybel_0(sK2,X0_59,X0_58)
    | ~ r2_hidden(X0_58,k2_yellow19(sK2,X0_59))
    | ~ l1_waybel_0(X0_59,sK2)
    | v2_struct_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1261])).

cnf(c_12483,plain,
    ( r1_waybel_0(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5),X0_58)
    | ~ r2_hidden(X0_58,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5)))
    | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5),sK2)
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) ),
    inference(instantiation,[status(thm)],[c_10691])).

cnf(c_12501,plain,
    ( r1_waybel_0(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5),X0_58) = iProver_top
    | r2_hidden(X0_58,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5))) != iProver_top
    | l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5),sK2) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12483])).

cnf(c_12503,plain,
    ( r1_waybel_0(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5),sK3) = iProver_top
    | r2_hidden(sK3,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5))) != iProver_top
    | l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5),sK2) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12501])).

cnf(c_24,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1455,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_839])).

cnf(c_1456,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | v1_xboole_0(X0)
    | v2_struct_0(sK2)
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_1455])).

cnf(c_1460,plain,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK2)))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK2)))
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1456,c_46])).

cnf(c_1461,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | v1_xboole_0(X0)
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X0)) = X0 ),
    inference(renaming,[status(thm)],[c_1460])).

cnf(c_10681,plain,
    ( ~ v1_subset_1(X0_58,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | v1_xboole_0(X0_58)
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X0_58)) = X0_58 ),
    inference(subtyping,[status(esa)],[c_1461])).

cnf(c_12405,plain,
    ( ~ v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | v1_xboole_0(sK5)
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_10681])).

cnf(c_12406,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK5)) = sK5
    | v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) != iProver_top
    | v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) != iProver_top
    | v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12405])).

cnf(c_13,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1589,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_839])).

cnf(c_1590,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v7_waybel_0(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1589])).

cnf(c_1594,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v7_waybel_0(k3_yellow19(sK2,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1590,c_46])).

cnf(c_1595,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v7_waybel_0(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1594])).

cnf(c_10675,plain,
    ( ~ v1_subset_1(X0_58,u1_struct_0(k3_yellow_1(X1_58)))
    | ~ v2_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_58))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | v7_waybel_0(k3_yellow19(sK2,X1_58,X0_58))
    | v1_xboole_0(X1_58)
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_1595])).

cnf(c_12393,plain,
    ( ~ v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5))
    | v1_xboole_0(k2_struct_0(sK2))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_10675])).

cnf(c_12403,plain,
    ( v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) != iProver_top
    | v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) != iProver_top
    | v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12393])).

cnf(c_10,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1625,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_839])).

cnf(c_1626,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_orders_2(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1625])).

cnf(c_1630,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v4_orders_2(k3_yellow19(sK2,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1626,c_46])).

cnf(c_1631,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_orders_2(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1630])).

cnf(c_10674,plain,
    ( ~ v2_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_58))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_orders_2(k3_yellow19(sK2,X1_58,X0_58))
    | v1_xboole_0(X1_58)
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_1631])).

cnf(c_12394,plain,
    ( ~ v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK5))
    | v1_xboole_0(k2_struct_0(sK2))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_10674])).

cnf(c_12401,plain,
    ( v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) != iProver_top
    | v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12394])).

cnf(c_4,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1658,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_839])).

cnf(c_1659,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1658])).

cnf(c_1663,plain,
    ( ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1659,c_46])).

cnf(c_1664,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK2,X1,X0)) ),
    inference(renaming,[status(thm)],[c_1663])).

cnf(c_10673,plain,
    ( ~ v2_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_58))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X1_58)
    | v1_xboole_0(X0_58)
    | ~ v2_struct_0(k3_yellow19(sK2,X1_58,X0_58)) ),
    inference(subtyping,[status(esa)],[c_1664])).

cnf(c_12395,plain,
    ( ~ v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | v1_xboole_0(k2_struct_0(sK2))
    | v1_xboole_0(sK5)
    | ~ v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) ),
    inference(instantiation,[status(thm)],[c_10673])).

cnf(c_12399,plain,
    ( v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) != iProver_top
    | v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12395])).

cnf(c_3,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1691,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_839])).

cnf(c_1692,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | l1_waybel_0(k3_yellow19(sK2,X1,X0),sK2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1691])).

cnf(c_1696,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | l1_waybel_0(k3_yellow19(sK2,X1,X0),sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1692,c_46])).

cnf(c_1697,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | l1_waybel_0(k3_yellow19(sK2,X1,X0),sK2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1696])).

cnf(c_10672,plain,
    ( ~ v2_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_58))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | l1_waybel_0(k3_yellow19(sK2,X1_58,X0_58),sK2)
    | v1_xboole_0(X1_58)
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_1697])).

cnf(c_12396,plain,
    ( ~ v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5),sK2)
    | v1_xboole_0(k2_struct_0(sK2))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_10672])).

cnf(c_12397,plain,
    ( v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) != iProver_top
    | v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) != iProver_top
    | l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK5),sK2) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12396])).

cnf(c_19,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1277,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_839])).

cnf(c_1278,plain,
    ( ~ r1_waybel_0(sK2,X0,X1)
    | r2_hidden(X1,k2_yellow19(sK2,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1277])).

cnf(c_1282,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,k2_yellow19(sK2,X0))
    | ~ r1_waybel_0(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1278,c_46])).

cnf(c_1283,plain,
    ( ~ r1_waybel_0(sK2,X0,X1)
    | r2_hidden(X1,k2_yellow19(sK2,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1282])).

cnf(c_10690,plain,
    ( ~ r1_waybel_0(sK2,X0_59,X0_58)
    | r2_hidden(X0_58,k2_yellow19(sK2,X0_59))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_waybel_0(X0_59,sK2)
    | v2_struct_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1283])).

cnf(c_12093,plain,
    ( ~ r1_waybel_0(sK2,sK1(sK2,X0_58,sK4),X1_58)
    | r2_hidden(X1_58,k2_yellow19(sK2,sK1(sK2,X0_58,sK4)))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_waybel_0(sK1(sK2,X0_58,sK4),sK2)
    | v2_struct_0(sK1(sK2,X0_58,sK4)) ),
    inference(instantiation,[status(thm)],[c_10690])).

cnf(c_12139,plain,
    ( r1_waybel_0(sK2,sK1(sK2,X0_58,sK4),X1_58) != iProver_top
    | r2_hidden(X1_58,k2_yellow19(sK2,sK1(sK2,X0_58,sK4))) = iProver_top
    | m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_waybel_0(sK1(sK2,X0_58,sK4),sK2) != iProver_top
    | v2_struct_0(sK1(sK2,X0_58,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12093])).

cnf(c_12141,plain,
    ( r1_waybel_0(sK2,sK1(sK2,sK3,sK4),sK3) != iProver_top
    | r2_hidden(sK3,k2_yellow19(sK2,sK1(sK2,sK3,sK4))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_waybel_0(sK1(sK2,sK3,sK4),sK2) != iProver_top
    | v2_struct_0(sK1(sK2,sK3,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12139])).

cnf(c_28,plain,
    ( r1_waybel_0(X0,sK1(X0,X1,X2),X1)
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_615,plain,
    ( r1_waybel_0(X0,sK1(X0,X1,X2),X1)
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_45])).

cnf(c_616,plain,
    ( r1_waybel_0(sK2,sK1(sK2,X0,X1),X0)
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_620,plain,
    ( r1_waybel_0(sK2,sK1(sK2,X0,X1),X0)
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_46,c_44])).

cnf(c_10698,plain,
    ( r1_waybel_0(sK2,sK1(sK2,X0_58,X1_58),X0_58)
    | ~ r2_hidden(X1_58,k2_pre_topc(sK2,X0_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_620])).

cnf(c_11960,plain,
    ( r1_waybel_0(sK2,sK1(sK2,X0_58,sK4),X0_58)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_10698])).

cnf(c_11961,plain,
    ( r1_waybel_0(sK2,sK1(sK2,X0_58,sK4),X0_58) = iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_58)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11960])).

cnf(c_11963,plain,
    ( r1_waybel_0(sK2,sK1(sK2,sK3,sK4),sK3) = iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11961])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_702,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X2,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_45])).

cnf(c_703,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_struct_0(sK1(sK2,X1,X0))
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_707,plain,
    ( ~ v2_struct_0(sK1(sK2,X1,X0))
    | ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_703,c_46,c_44])).

cnf(c_708,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v2_struct_0(sK1(sK2,X1,X0)) ),
    inference(renaming,[status(thm)],[c_707])).

cnf(c_10697,plain,
    ( ~ r2_hidden(X0_58,k2_pre_topc(sK2,X1_58))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | ~ v2_struct_0(sK1(sK2,X1_58,X0_58)) ),
    inference(subtyping,[status(esa)],[c_708])).

cnf(c_11955,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v2_struct_0(sK1(sK2,X0_58,sK4)) ),
    inference(instantiation,[status(thm)],[c_10697])).

cnf(c_11956,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,X0_58)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK1(sK2,X0_58,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11955])).

cnf(c_11958,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK1(sK2,sK3,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11956])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v4_orders_2(sK1(X1,X2,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_726,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v4_orders_2(sK1(X1,X2,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_45])).

cnf(c_727,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v4_orders_2(sK1(sK2,X1,X0))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_731,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v4_orders_2(sK1(sK2,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_46,c_44])).

cnf(c_10696,plain,
    ( ~ r2_hidden(X0_58,k2_pre_topc(sK2,X1_58))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | v4_orders_2(sK1(sK2,X1_58,X0_58)) ),
    inference(subtyping,[status(esa)],[c_731])).

cnf(c_11950,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v4_orders_2(sK1(sK2,X0_58,sK4)) ),
    inference(instantiation,[status(thm)],[c_10696])).

cnf(c_11951,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,X0_58)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v4_orders_2(sK1(sK2,X0_58,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11950])).

cnf(c_11953,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v4_orders_2(sK1(sK2,sK3,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11951])).

cnf(c_30,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v7_waybel_0(sK1(X1,X2,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_750,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_waybel_0(sK1(X1,X2,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_45])).

cnf(c_751,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v7_waybel_0(sK1(sK2,X1,X0))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_755,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v7_waybel_0(sK1(sK2,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_751,c_46,c_44])).

cnf(c_10695,plain,
    ( ~ r2_hidden(X0_58,k2_pre_topc(sK2,X1_58))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | v7_waybel_0(sK1(sK2,X1_58,X0_58)) ),
    inference(subtyping,[status(esa)],[c_755])).

cnf(c_11945,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v7_waybel_0(sK1(sK2,X0_58,sK4)) ),
    inference(instantiation,[status(thm)],[c_10695])).

cnf(c_11946,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,X0_58)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v7_waybel_0(sK1(sK2,X0_58,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11945])).

cnf(c_11948,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v7_waybel_0(sK1(sK2,sK3,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11946])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | l1_waybel_0(sK1(X1,X2,X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_774,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | l1_waybel_0(sK1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_45])).

cnf(c_775,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | l1_waybel_0(sK1(sK2,X1,X0),sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_774])).

cnf(c_779,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | l1_waybel_0(sK1(sK2,X1,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_775,c_46,c_44])).

cnf(c_10694,plain,
    ( ~ r2_hidden(X0_58,k2_pre_topc(sK2,X1_58))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK2))
    | l1_waybel_0(sK1(sK2,X1_58,X0_58),sK2) ),
    inference(subtyping,[status(esa)],[c_779])).

cnf(c_11936,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | l1_waybel_0(sK1(sK2,X0_58,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_10694])).

cnf(c_11937,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,X0_58)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | l1_waybel_0(sK1(sK2,X0_58,sK4),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11936])).

cnf(c_11939,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | l1_waybel_0(sK1(sK2,sK3,sK4),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11937])).

cnf(c_7,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ v1_xboole_0(k2_yellow19(X1,X0))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1551,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ v1_xboole_0(k2_yellow19(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_839])).

cnf(c_1552,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | ~ v1_xboole_0(k2_yellow19(sK2,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1551])).

cnf(c_1556,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_yellow19(sK2,X0))
    | ~ l1_waybel_0(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1552,c_46])).

cnf(c_1557,plain,
    ( ~ l1_waybel_0(X0,sK2)
    | ~ v1_xboole_0(k2_yellow19(sK2,X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1556])).

cnf(c_2,plain,
    ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1429,plain,
    ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_839])).

cnf(c_1430,plain,
    ( m1_subset_1(k2_yellow19(sK2,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1429])).

cnf(c_1434,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK2)
    | m1_subset_1(k2_yellow19(sK2,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1430,c_46])).

cnf(c_1435,plain,
    ( m1_subset_1(k2_yellow19(sK2,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1434])).

cnf(c_6,plain,
    ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1410,plain,
    ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_839])).

cnf(c_1411,plain,
    ( v13_waybel_0(k2_yellow19(sK2,X0),k3_yellow_1(k2_struct_0(sK2)))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1410])).

cnf(c_1415,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK2)
    | v13_waybel_0(k2_yellow19(sK2,X0),k3_yellow_1(k2_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1411,c_46])).

cnf(c_1416,plain,
    ( v13_waybel_0(k2_yellow19(sK2,X0),k3_yellow_1(k2_struct_0(sK2)))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1415])).

cnf(c_8,plain,
    ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1385,plain,
    ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_839])).

cnf(c_1386,plain,
    ( v2_waybel_0(k2_yellow19(sK2,X0),k3_yellow_1(k2_struct_0(sK2)))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1385])).

cnf(c_1390,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK2)
    | v2_waybel_0(k2_yellow19(sK2,X0),k3_yellow_1(k2_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1386,c_46])).

cnf(c_1391,plain,
    ( v2_waybel_0(k2_yellow19(sK2,X0),k3_yellow_1(k2_struct_0(sK2)))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1390])).

cnf(c_9,plain,
    ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1360,plain,
    ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_839])).

cnf(c_1361,plain,
    ( v1_subset_1(k2_yellow19(sK2,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1360])).

cnf(c_1365,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK2)
    | v1_subset_1(k2_yellow19(sK2,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1361,c_46])).

cnf(c_1366,plain,
    ( v1_subset_1(k2_yellow19(sK2,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1365])).

cnf(c_23,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_34,negated_conjecture,
    ( ~ r1_waybel_7(sK2,X0,sK4)
    | ~ r2_hidden(sK3,X0)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_523,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_hidden(sK3,X3)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k2_yellow19(X0,X1) != X3
    | sK4 != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_524,plain,
    ( ~ r3_waybel_9(sK2,X0,sK4)
    | ~ r2_hidden(sK3,k2_yellow19(sK2,X0))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v1_subset_1(k2_yellow19(sK2,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(k2_yellow19(sK2,X0),k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(k2_yellow19(sK2,X0),k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(k2_yellow19(sK2,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(k2_yellow19(sK2,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_528,plain,
    ( v2_struct_0(X0)
    | v1_xboole_0(k2_yellow19(sK2,X0))
    | ~ l1_waybel_0(X0,sK2)
    | ~ r3_waybel_9(sK2,X0,sK4)
    | ~ r2_hidden(sK3,k2_yellow19(sK2,X0))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v1_subset_1(k2_yellow19(sK2,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(k2_yellow19(sK2,X0),k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(k2_yellow19(sK2,X0),k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(k2_yellow19(sK2,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_46,c_45,c_44,c_42])).

cnf(c_529,plain,
    ( ~ r3_waybel_9(sK2,X0,sK4)
    | ~ r2_hidden(sK3,k2_yellow19(sK2,X0))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v1_subset_1(k2_yellow19(sK2,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(k2_yellow19(sK2,X0),k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(k2_yellow19(sK2,X0),k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(k2_yellow19(sK2,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v1_xboole_0(k2_yellow19(sK2,X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_528])).

cnf(c_27,plain,
    ( r3_waybel_9(X0,sK1(X0,X1,X2),X2)
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_639,plain,
    ( r3_waybel_9(X0,sK1(X0,X1,X2),X2)
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_45])).

cnf(c_640,plain,
    ( r3_waybel_9(sK2,sK1(sK2,X0,X1),X1)
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_644,plain,
    ( r3_waybel_9(sK2,sK1(sK2,X0,X1),X1)
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_46,c_44])).

cnf(c_848,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ r2_hidden(sK3,k2_yellow19(sK2,X2))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v1_subset_1(k2_yellow19(sK2,X2),u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(k2_yellow19(sK2,X2),k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(k2_yellow19(sK2,X2),k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_yellow19(sK2,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ l1_waybel_0(X2,sK2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v1_xboole_0(k2_yellow19(sK2,X2))
    | v2_struct_0(X2)
    | sK1(sK2,X1,X0) != X2
    | sK4 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_529,c_644])).

cnf(c_849,plain,
    ( ~ r2_hidden(sK3,k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v1_subset_1(k2_yellow19(sK2,sK1(sK2,X0,sK4)),u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_waybel_0(sK1(sK2,X0,sK4),sK2)
    | ~ v4_orders_2(sK1(sK2,X0,sK4))
    | ~ v7_waybel_0(sK1(sK2,X0,sK4))
    | v1_xboole_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | v2_struct_0(sK1(sK2,X0,sK4)) ),
    inference(unflattening,[status(thm)],[c_848])).

cnf(c_853,plain,
    ( ~ m1_subset_1(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v13_waybel_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k3_yellow_1(k2_struct_0(sK2)))
    | ~ v2_waybel_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k3_yellow_1(k2_struct_0(sK2)))
    | ~ v1_subset_1(k2_yellow19(sK2,sK1(sK2,X0,sK4)),u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(sK3,k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | ~ l1_waybel_0(sK1(sK2,X0,sK4),sK2)
    | ~ v4_orders_2(sK1(sK2,X0,sK4))
    | ~ v7_waybel_0(sK1(sK2,X0,sK4))
    | v1_xboole_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | v2_struct_0(sK1(sK2,X0,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_849,c_42])).

cnf(c_854,plain,
    ( ~ r2_hidden(sK3,k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v1_subset_1(k2_yellow19(sK2,sK1(sK2,X0,sK4)),u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    | ~ v2_waybel_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ l1_waybel_0(sK1(sK2,X0,sK4),sK2)
    | ~ v4_orders_2(sK1(sK2,X0,sK4))
    | ~ v7_waybel_0(sK1(sK2,X0,sK4))
    | v1_xboole_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | v2_struct_0(sK1(sK2,X0,sK4)) ),
    inference(renaming,[status(thm)],[c_853])).

cnf(c_1749,plain,
    ( ~ r2_hidden(sK3,k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v2_waybel_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k3_yellow_1(k2_struct_0(sK2)))
    | ~ v13_waybel_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ l1_waybel_0(sK1(sK2,X0,sK4),sK2)
    | ~ v4_orders_2(sK1(sK2,X0,sK4))
    | ~ v7_waybel_0(sK1(sK2,X0,sK4))
    | v1_xboole_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | v2_struct_0(sK1(sK2,X0,sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1366,c_854])).

cnf(c_1759,plain,
    ( ~ r2_hidden(sK3,k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v13_waybel_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k3_yellow_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ l1_waybel_0(sK1(sK2,X0,sK4),sK2)
    | ~ v4_orders_2(sK1(sK2,X0,sK4))
    | ~ v7_waybel_0(sK1(sK2,X0,sK4))
    | v1_xboole_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | v2_struct_0(sK1(sK2,X0,sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1391,c_1749])).

cnf(c_1769,plain,
    ( ~ r2_hidden(sK3,k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_yellow19(sK2,sK1(sK2,X0,sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    | ~ l1_waybel_0(sK1(sK2,X0,sK4),sK2)
    | ~ v4_orders_2(sK1(sK2,X0,sK4))
    | ~ v7_waybel_0(sK1(sK2,X0,sK4))
    | v1_xboole_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | v2_struct_0(sK1(sK2,X0,sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1416,c_1759])).

cnf(c_1777,plain,
    ( ~ r2_hidden(sK3,k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_waybel_0(sK1(sK2,X0,sK4),sK2)
    | ~ v4_orders_2(sK1(sK2,X0,sK4))
    | ~ v7_waybel_0(sK1(sK2,X0,sK4))
    | v1_xboole_0(k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | v2_struct_0(sK1(sK2,X0,sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1435,c_1769])).

cnf(c_1810,plain,
    ( ~ r2_hidden(sK3,k2_yellow19(sK2,sK1(sK2,X0,sK4)))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_waybel_0(sK1(sK2,X0,sK4),sK2)
    | ~ v4_orders_2(sK1(sK2,X0,sK4))
    | ~ v7_waybel_0(sK1(sK2,X0,sK4))
    | v2_struct_0(sK1(sK2,X0,sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1557,c_1777])).

cnf(c_10671,plain,
    ( ~ r2_hidden(sK3,k2_yellow19(sK2,sK1(sK2,X0_58,sK4)))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_58))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_waybel_0(sK1(sK2,X0_58,sK4),sK2)
    | ~ v4_orders_2(sK1(sK2,X0_58,sK4))
    | ~ v7_waybel_0(sK1(sK2,X0_58,sK4))
    | v2_struct_0(sK1(sK2,X0_58,sK4)) ),
    inference(subtyping,[status(esa)],[c_1810])).

cnf(c_10837,plain,
    ( r2_hidden(sK3,k2_yellow19(sK2,sK1(sK2,X0_58,sK4))) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_58)) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_waybel_0(sK1(sK2,X0_58,sK4),sK2) != iProver_top
    | v4_orders_2(sK1(sK2,X0_58,sK4)) != iProver_top
    | v7_waybel_0(sK1(sK2,X0_58,sK4)) != iProver_top
    | v2_struct_0(sK1(sK2,X0_58,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10671])).

cnf(c_10839,plain,
    ( r2_hidden(sK3,k2_yellow19(sK2,sK1(sK2,sK3,sK4))) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_waybel_0(sK1(sK2,sK3,sK4),sK2) != iProver_top
    | v4_orders_2(sK1(sK2,sK3,sK4)) != iProver_top
    | v7_waybel_0(sK1(sK2,sK3,sK4)) != iProver_top
    | v2_struct_0(sK1(sK2,sK3,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10837])).

cnf(c_10711,plain,
    ( X0_58 = X0_58 ),
    theory(equality)).

cnf(c_10757,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_10711])).

cnf(c_1,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_156,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_158,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_146,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_148,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(k2_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_125,plain,
    ( v1_xboole_0(k2_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_127,plain,
    ( v1_xboole_0(k2_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_36,negated_conjecture,
    ( r2_hidden(sK3,sK5)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_57,plain,
    ( r2_hidden(sK3,sK5) = iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_37,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_56,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_38,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_55,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_39,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_54,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_40,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_53,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_41,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_52,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_51,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_49,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_47,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12830,c_12664,c_12503,c_12406,c_12403,c_12401,c_12399,c_12397,c_12141,c_11963,c_11958,c_11953,c_11948,c_11939,c_10839,c_10757,c_158,c_148,c_127,c_57,c_56,c_55,c_54,c_53,c_52,c_51,c_50,c_49,c_47])).


%------------------------------------------------------------------------------
