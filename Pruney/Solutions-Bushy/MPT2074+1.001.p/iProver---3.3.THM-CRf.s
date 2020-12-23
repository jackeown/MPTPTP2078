%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2074+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:08 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  303 (1910 expanded)
%              Number of clauses        :  210 ( 393 expanded)
%              Number of leaves         :   20 ( 498 expanded)
%              Depth                    :   21
%              Number of atoms          : 1868 (22151 expanded)
%              Number of equality atoms :  107 ( 121 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( r1_waybel_7(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X1) )
             => ? [X2] :
                  ( r1_waybel_7(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f55,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r1_waybel_7(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            | v1_xboole_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f56,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r1_waybel_7(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            | v1_xboole_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f67,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r1_waybel_7(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r1_waybel_7(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            | v1_xboole_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f68,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r1_waybel_7(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r1_waybel_7(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            | v1_xboole_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f69,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r1_waybel_7(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r1_waybel_7(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            | v1_xboole_0(X3) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f68])).

fof(f72,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( r1_waybel_7(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r1_waybel_7(X0,X3,sK6(X3))
        & m1_subset_1(sK6(X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r1_waybel_7(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( ! [X2] :
            ( ~ r1_waybel_7(X0,sK5,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( ~ r1_waybel_7(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r1_waybel_7(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
              | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
              | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              | v1_xboole_0(X3) )
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r1_waybel_7(sK4,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(sK4)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK4)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK4)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
            & ~ v1_xboole_0(X1) )
        | ~ v1_compts_1(sK4) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r1_waybel_7(sK4,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK4)) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
            | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK4)))
            | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK4)))
            | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
            | v1_xboole_0(X3) )
        | v1_compts_1(sK4) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,
    ( ( ( ! [X2] :
            ( ~ r1_waybel_7(sK4,sK5,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK4)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
        & v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
        & v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
        & v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
        & ~ v1_xboole_0(sK5) )
      | ~ v1_compts_1(sK4) )
    & ( ! [X3] :
          ( ( r1_waybel_7(sK4,X3,sK6(X3))
            & m1_subset_1(sK6(X3),u1_struct_0(sK4)) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
          | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK4)))
          | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK4)))
          | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
          | v1_xboole_0(X3) )
      | v1_compts_1(sK4) )
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f69,f72,f71,f70])).

fof(f116,plain,(
    ! [X2] :
      ( ~ r1_waybel_7(sK4,sK5,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                  | ~ r1_waybel_7(X0,X1,X2) )
                & ( r1_waybel_7(X0,X1,X2)
                  | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_7(X0,X1,X2)
      | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f107,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f106,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f108,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f110,plain,(
    ! [X3] :
      ( r1_waybel_7(sK4,X3,sK6(X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK4)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK4)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
      | v1_xboole_0(X3)
      | v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) )
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK3(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK3(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK3(X0),X0)
        & v7_waybel_0(sK3(X0))
        & v4_orders_2(sK3(X0))
        & ~ v2_struct_0(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK3(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK3(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK3(X0),X0)
        & v7_waybel_0(sK3(X0))
        & v4_orders_2(sK3(X0))
        & ~ v2_struct_0(sK3(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f63])).

fof(f94,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f95,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f96,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f97,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK3(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_yellow19(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f109,plain,(
    ! [X3] :
      ( m1_subset_1(sK6(X3),u1_struct_0(sK4))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK4)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK4)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
      | v1_xboole_0(X3)
      | v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f99,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK3(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK2(X0,X1))
            & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f61])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK2(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(pure_predicate_removal,[],[f13])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f91,plain,(
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
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

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
    inference(ennf_transformation,[],[f23])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f25,plain,(
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
    inference(pure_predicate_removal,[],[f22])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f74,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f115,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f114,plain,
    ( v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f113,plain,
    ( v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f112,plain,
    ( v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f111,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( ~ r1_waybel_7(sK4,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_11763,negated_conjecture,
    ( ~ r1_waybel_7(sK4,sK5,X0_58)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | ~ v1_compts_1(sK4) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_16343,plain,
    ( ~ r1_waybel_7(sK4,sK5,sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X0_58)))
    | ~ m1_subset_1(sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X0_58)),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11763])).

cnf(c_16347,plain,
    ( ~ r1_waybel_7(sK4,sK5,sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)))
    | ~ m1_subset_1(sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16343])).

cnf(c_29,plain,
    ( r1_waybel_7(X0,X1,X2)
    | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
    | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_937,plain,
    ( r1_waybel_7(X0,X1,X2)
    | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
    | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_41])).

cnf(c_938,plain,
    ( r1_waybel_7(sK4,X0,X1)
    | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X0),X1)
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_937])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_942,plain,
    ( v1_xboole_0(X0)
    | r1_waybel_7(sK4,X0,X1)
    | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X0),X1)
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_938,c_42,c_40])).

cnf(c_943,plain,
    ( r1_waybel_7(sK4,X0,X1)
    | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X0),X1)
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_942])).

cnf(c_11752,plain,
    ( r1_waybel_7(sK4,X0_58,X1_58)
    | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X0_58),X1_58)
    | ~ v1_subset_1(X0_58,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | ~ m1_subset_1(X1_58,u1_struct_0(sK4))
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_943])).

cnf(c_14989,plain,
    ( r1_waybel_7(sK4,X0_58,sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X1_58)))
    | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X0_58),sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X1_58)))
    | ~ v1_subset_1(X0_58,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | ~ m1_subset_1(sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X1_58)),u1_struct_0(sK4))
    | v1_xboole_0(X0_58) ),
    inference(instantiation,[status(thm)],[c_11752])).

cnf(c_14996,plain,
    ( r1_waybel_7(sK4,sK5,sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)))
    | ~ r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)))
    | ~ v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_14989])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k2_yellow19(X1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_672,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k2_yellow19(X1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_2])).

cnf(c_673,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k2_yellow19(X1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_2894,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k2_yellow19(X1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_673,c_40])).

cnf(c_2895,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(k2_yellow19(sK4,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2894])).

cnf(c_2899,plain,
    ( v2_struct_0(X0)
    | m1_subset_1(k2_yellow19(sK4,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | ~ l1_waybel_0(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2895,c_42])).

cnf(c_2900,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(k2_yellow19(sK4,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2899])).

cnf(c_11721,plain,
    ( ~ l1_waybel_0(X0_59,sK4)
    | m1_subset_1(k2_yellow19(sK4,X0_59),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v2_struct_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_2900])).

cnf(c_12725,plain,
    ( l1_waybel_0(X0_59,sK4) != iProver_top
    | m1_subset_1(k2_yellow19(sK4,X0_59),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) = iProver_top
    | v2_struct_0(X0_59) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11721])).

cnf(c_38,negated_conjecture,
    ( r1_waybel_7(sK4,X0,sK6(X0))
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v1_compts_1(sK4)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_11757,negated_conjecture,
    ( r1_waybel_7(sK4,X0_58,sK6(X0_58))
    | ~ v1_subset_1(X0_58,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v1_compts_1(sK4)
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_12691,plain,
    ( r1_waybel_7(sK4,X0_58,sK6(X0_58)) = iProver_top
    | v1_subset_1(X0_58,u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))) != iProver_top
    | v2_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4))) != iProver_top
    | v13_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v1_xboole_0(X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11757])).

cnf(c_13907,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,X0_59),sK6(k2_yellow19(sK4,X0_59))) = iProver_top
    | v1_subset_1(k2_yellow19(sK4,X0_59),u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))) != iProver_top
    | v2_waybel_0(k2_yellow19(sK4,X0_59),k3_yellow_1(k2_struct_0(sK4))) != iProver_top
    | v13_waybel_0(k2_yellow19(sK4,X0_59),k3_yellow_1(k2_struct_0(sK4))) != iProver_top
    | l1_waybel_0(X0_59,sK4) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v1_xboole_0(k2_yellow19(sK4,X0_59)) = iProver_top
    | v2_struct_0(X0_59) = iProver_top ),
    inference(superposition,[status(thm)],[c_12725,c_12691])).

cnf(c_25,plain,
    ( ~ v2_pre_topc(X0)
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1075,plain,
    ( v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK3(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_41])).

cnf(c_1076,plain,
    ( v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_struct_0(sK3(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1075])).

cnf(c_1078,plain,
    ( ~ v2_struct_0(sK3(sK4))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1076,c_42,c_40])).

cnf(c_1079,plain,
    ( v1_compts_1(sK4)
    | ~ v2_struct_0(sK3(sK4)) ),
    inference(renaming,[status(thm)],[c_1078])).

cnf(c_1080,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v2_struct_0(sK3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1079])).

cnf(c_24,plain,
    ( ~ v2_pre_topc(X0)
    | v1_compts_1(X0)
    | v4_orders_2(sK3(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1089,plain,
    ( v1_compts_1(X0)
    | v4_orders_2(sK3(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_41])).

cnf(c_1090,plain,
    ( v1_compts_1(sK4)
    | v4_orders_2(sK3(sK4))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1089])).

cnf(c_1092,plain,
    ( v1_compts_1(sK4)
    | v4_orders_2(sK3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1090,c_42,c_40])).

cnf(c_1094,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v4_orders_2(sK3(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1092])).

cnf(c_23,plain,
    ( ~ v2_pre_topc(X0)
    | v1_compts_1(X0)
    | v7_waybel_0(sK3(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1103,plain,
    ( v1_compts_1(X0)
    | v7_waybel_0(sK3(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_41])).

cnf(c_1104,plain,
    ( v1_compts_1(sK4)
    | v7_waybel_0(sK3(sK4))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1103])).

cnf(c_85,plain,
    ( ~ v2_pre_topc(sK4)
    | v1_compts_1(sK4)
    | v7_waybel_0(sK3(sK4))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1106,plain,
    ( v1_compts_1(sK4)
    | v7_waybel_0(sK3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1104,c_42,c_41,c_40,c_85])).

cnf(c_1108,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v7_waybel_0(sK3(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(c_22,plain,
    ( l1_waybel_0(sK3(X0),X0)
    | ~ v2_pre_topc(X0)
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1117,plain,
    ( l1_waybel_0(sK3(X0),X0)
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_41])).

cnf(c_1118,plain,
    ( l1_waybel_0(sK3(sK4),sK4)
    | v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1117])).

cnf(c_1120,plain,
    ( l1_waybel_0(sK3(sK4),sK4)
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1118,c_42,c_40])).

cnf(c_1122,plain,
    ( l1_waybel_0(sK3(sK4),sK4) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_13,plain,
    ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_532,plain,
    ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_5,c_13])).

cnf(c_2710,plain,
    ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_532,c_40])).

cnf(c_2711,plain,
    ( v1_subset_1(k2_yellow19(sK4,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2710])).

cnf(c_2715,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK4)
    | v1_subset_1(k2_yellow19(sK4,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2711,c_42])).

cnf(c_2716,plain,
    ( v1_subset_1(k2_yellow19(sK4,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2715])).

cnf(c_4009,plain,
    ( v1_subset_1(k2_yellow19(sK4,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2716,c_1092])).

cnf(c_4010,plain,
    ( v1_subset_1(k2_yellow19(sK4,sK3(sK4)),u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ l1_waybel_0(sK3(sK4),sK4)
    | v1_compts_1(sK4)
    | ~ v7_waybel_0(sK3(sK4))
    | v2_struct_0(sK3(sK4)) ),
    inference(unflattening,[status(thm)],[c_4009])).

cnf(c_88,plain,
    ( l1_waybel_0(sK3(sK4),sK4)
    | ~ v2_pre_topc(sK4)
    | v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2274,plain,
    ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ l1_waybel_0(X1,X0)
    | v1_compts_1(sK4)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK3(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_532,c_1092])).

cnf(c_2275,plain,
    ( v1_subset_1(k2_yellow19(X0,sK3(sK4)),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ l1_waybel_0(sK3(sK4),X0)
    | v1_compts_1(sK4)
    | ~ v7_waybel_0(sK3(sK4))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3(sK4)) ),
    inference(unflattening,[status(thm)],[c_2274])).

cnf(c_2277,plain,
    ( v1_subset_1(k2_yellow19(sK4,sK3(sK4)),u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ l1_waybel_0(sK3(sK4),sK4)
    | v1_compts_1(sK4)
    | ~ v7_waybel_0(sK3(sK4))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK3(sK4))
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2275])).

cnf(c_4012,plain,
    ( v1_subset_1(k2_yellow19(sK4,sK3(sK4)),u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4010,c_42,c_41,c_40,c_85,c_88,c_1079,c_2277])).

cnf(c_4014,plain,
    ( v1_subset_1(k2_yellow19(sK4,sK3(sK4)),u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4012])).

cnf(c_12,plain,
    ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_558,plain,
    ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_5,c_12])).

cnf(c_2685,plain,
    ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_558,c_40])).

cnf(c_2686,plain,
    ( v2_waybel_0(k2_yellow19(sK4,X0),k3_yellow_1(k2_struct_0(sK4)))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2685])).

cnf(c_2690,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK4)
    | v2_waybel_0(k2_yellow19(sK4,X0),k3_yellow_1(k2_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2686,c_42])).

cnf(c_2691,plain,
    ( v2_waybel_0(k2_yellow19(sK4,X0),k3_yellow_1(k2_struct_0(sK4)))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2690])).

cnf(c_4023,plain,
    ( v2_waybel_0(k2_yellow19(sK4,X0),k3_yellow_1(k2_struct_0(sK4)))
    | ~ l1_waybel_0(X0,sK4)
    | v1_compts_1(sK4)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | sK3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2691,c_1092])).

cnf(c_4024,plain,
    ( v2_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4)))
    | ~ l1_waybel_0(sK3(sK4),sK4)
    | v1_compts_1(sK4)
    | ~ v7_waybel_0(sK3(sK4))
    | v2_struct_0(sK3(sK4)) ),
    inference(unflattening,[status(thm)],[c_4023])).

cnf(c_2247,plain,
    ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | v1_compts_1(sK4)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK3(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_558,c_1092])).

cnf(c_2248,plain,
    ( v2_waybel_0(k2_yellow19(X0,sK3(sK4)),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(sK3(sK4),X0)
    | v1_compts_1(sK4)
    | ~ v7_waybel_0(sK3(sK4))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3(sK4)) ),
    inference(unflattening,[status(thm)],[c_2247])).

cnf(c_2250,plain,
    ( v2_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4)))
    | ~ l1_waybel_0(sK3(sK4),sK4)
    | v1_compts_1(sK4)
    | ~ v7_waybel_0(sK3(sK4))
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK3(sK4))
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2248])).

cnf(c_4026,plain,
    ( v2_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4)))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4024,c_42,c_41,c_40,c_85,c_88,c_1079,c_2250])).

cnf(c_4028,plain,
    ( v2_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4))) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4026])).

cnf(c_11,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ v1_xboole_0(k2_yellow19(X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_651,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_xboole_0(k2_yellow19(X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_652,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(k2_yellow19(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_2913,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ v1_xboole_0(k2_yellow19(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_652,c_40])).

cnf(c_2914,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ v1_xboole_0(k2_yellow19(sK4,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2913])).

cnf(c_2918,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_yellow19(sK4,X0))
    | ~ l1_waybel_0(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2914,c_42])).

cnf(c_2919,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | ~ v1_xboole_0(k2_yellow19(sK4,X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2918])).

cnf(c_10181,plain,
    ( v1_compts_1(sK4)
    | ~ v1_xboole_0(k2_yellow19(sK4,X0))
    | v2_struct_0(X0)
    | sK3(sK4) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_1120,c_2919])).

cnf(c_10182,plain,
    ( v1_compts_1(sK4)
    | ~ v1_xboole_0(k2_yellow19(sK4,sK3(sK4)))
    | v2_struct_0(sK3(sK4)) ),
    inference(unflattening,[status(thm)],[c_10181])).

cnf(c_10184,plain,
    ( ~ v1_xboole_0(k2_yellow19(sK4,sK3(sK4)))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10182,c_1079])).

cnf(c_10185,plain,
    ( v1_compts_1(sK4)
    | ~ v1_xboole_0(k2_yellow19(sK4,sK3(sK4))) ),
    inference(renaming,[status(thm)],[c_10184])).

cnf(c_10186,plain,
    ( v1_compts_1(sK4) = iProver_top
    | v1_xboole_0(k2_yellow19(sK4,sK3(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10185])).

cnf(c_10195,plain,
    ( m1_subset_1(k2_yellow19(sK4,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | sK3(sK4) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_1120,c_2900])).

cnf(c_10196,plain,
    ( m1_subset_1(k2_yellow19(sK4,sK3(sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v1_compts_1(sK4)
    | v2_struct_0(sK3(sK4)) ),
    inference(unflattening,[status(thm)],[c_10195])).

cnf(c_10198,plain,
    ( v1_compts_1(sK4)
    | m1_subset_1(k2_yellow19(sK4,sK3(sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10196,c_1079])).

cnf(c_10199,plain,
    ( m1_subset_1(k2_yellow19(sK4,sK3(sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v1_compts_1(sK4) ),
    inference(renaming,[status(thm)],[c_10198])).

cnf(c_10200,plain,
    ( m1_subset_1(k2_yellow19(sK4,sK3(sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10199])).

cnf(c_10,plain,
    ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_584,plain,
    ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_5,c_10])).

cnf(c_2666,plain,
    ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_584,c_40])).

cnf(c_2667,plain,
    ( v13_waybel_0(k2_yellow19(sK4,X0),k3_yellow_1(k2_struct_0(sK4)))
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2666])).

cnf(c_2671,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK4)
    | v13_waybel_0(k2_yellow19(sK4,X0),k3_yellow_1(k2_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2667,c_42])).

cnf(c_2672,plain,
    ( v13_waybel_0(k2_yellow19(sK4,X0),k3_yellow_1(k2_struct_0(sK4)))
    | ~ l1_waybel_0(X0,sK4)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_2671])).

cnf(c_10237,plain,
    ( v13_waybel_0(k2_yellow19(sK4,X0),k3_yellow_1(k2_struct_0(sK4)))
    | v1_compts_1(sK4)
    | v2_struct_0(X0)
    | sK3(sK4) != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_1120,c_2672])).

cnf(c_10238,plain,
    ( v13_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4)))
    | v1_compts_1(sK4)
    | v2_struct_0(sK3(sK4)) ),
    inference(unflattening,[status(thm)],[c_10237])).

cnf(c_10240,plain,
    ( v1_compts_1(sK4)
    | v13_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10238,c_1079])).

cnf(c_10241,plain,
    ( v13_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4)))
    | v1_compts_1(sK4) ),
    inference(renaming,[status(thm)],[c_10240])).

cnf(c_10242,plain,
    ( v13_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4))) = iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10241])).

cnf(c_39,negated_conjecture,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | m1_subset_1(sK6(X0),u1_struct_0(sK4))
    | v1_compts_1(sK4)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_11756,negated_conjecture,
    ( ~ v1_subset_1(X0_58,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | m1_subset_1(sK6(X0_58),u1_struct_0(sK4))
    | v1_compts_1(sK4)
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_13753,plain,
    ( ~ v1_subset_1(k2_yellow19(sK4,sK3(sK4)),u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(k2_yellow19(sK4,sK3(sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | m1_subset_1(sK6(k2_yellow19(sK4,sK3(sK4))),u1_struct_0(sK4))
    | v1_compts_1(sK4)
    | v1_xboole_0(k2_yellow19(sK4,sK3(sK4))) ),
    inference(instantiation,[status(thm)],[c_11756])).

cnf(c_13754,plain,
    ( v1_subset_1(k2_yellow19(sK4,sK3(sK4)),u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))) != iProver_top
    | v2_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4))) != iProver_top
    | v13_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(k2_yellow19(sK4,sK3(sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) != iProver_top
    | m1_subset_1(sK6(k2_yellow19(sK4,sK3(sK4))),u1_struct_0(sK4)) = iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v1_xboole_0(k2_yellow19(sK4,sK3(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13753])).

cnf(c_13752,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,sK3(sK4)),sK6(k2_yellow19(sK4,sK3(sK4))))
    | ~ v1_subset_1(k2_yellow19(sK4,sK3(sK4)),u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(k2_yellow19(sK4,sK3(sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v1_compts_1(sK4)
    | v1_xboole_0(k2_yellow19(sK4,sK3(sK4))) ),
    inference(instantiation,[status(thm)],[c_11757])).

cnf(c_13756,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,sK3(sK4)),sK6(k2_yellow19(sK4,sK3(sK4)))) = iProver_top
    | v1_subset_1(k2_yellow19(sK4,sK3(sK4)),u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))) != iProver_top
    | v2_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4))) != iProver_top
    | v13_waybel_0(k2_yellow19(sK4,sK3(sK4)),k3_yellow_1(k2_struct_0(sK4))) != iProver_top
    | m1_subset_1(k2_yellow19(sK4,sK3(sK4)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) != iProver_top
    | v1_compts_1(sK4) = iProver_top
    | v1_xboole_0(k2_yellow19(sK4,sK3(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13752])).

cnf(c_20,plain,
    ( ~ r3_waybel_9(X0,sK3(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1131,plain,
    ( ~ r3_waybel_9(X0,sK3(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_41])).

cnf(c_1132,plain,
    ( ~ r3_waybel_9(sK4,sK3(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1131])).

cnf(c_1136,plain,
    ( ~ r3_waybel_9(sK4,sK3(sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v1_compts_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1132,c_42,c_40])).

cnf(c_11744,plain,
    ( ~ r3_waybel_9(sK4,sK3(sK4),X0_58)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | v1_compts_1(sK4) ),
    inference(subtyping,[status(esa)],[c_1136])).

cnf(c_14145,plain,
    ( ~ r3_waybel_9(sK4,sK3(sK4),sK6(k2_yellow19(sK4,sK3(sK4))))
    | ~ m1_subset_1(sK6(k2_yellow19(sK4,sK3(sK4))),u1_struct_0(sK4))
    | v1_compts_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11744])).

cnf(c_14146,plain,
    ( r3_waybel_9(sK4,sK3(sK4),sK6(k2_yellow19(sK4,sK3(sK4)))) != iProver_top
    | m1_subset_1(sK6(k2_yellow19(sK4,sK3(sK4))),u1_struct_0(sK4)) != iProver_top
    | v1_compts_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14145])).

cnf(c_26,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1042,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_41])).

cnf(c_1043,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
    | r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1042])).

cnf(c_1047,plain,
    ( v2_struct_0(X0)
    | ~ r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
    | r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1043,c_42,c_40])).

cnf(c_1048,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,X0),X1)
    | r3_waybel_9(sK4,X0,X1)
    | ~ l1_waybel_0(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1047])).

cnf(c_11749,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,X0_59),X0_58)
    | r3_waybel_9(sK4,X0_59,X0_58)
    | ~ l1_waybel_0(X0_59,sK4)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59)
    | v2_struct_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1048])).

cnf(c_13539,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,sK3(sK4)),X0_58)
    | r3_waybel_9(sK4,sK3(sK4),X0_58)
    | ~ l1_waybel_0(sK3(sK4),sK4)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | ~ v4_orders_2(sK3(sK4))
    | ~ v7_waybel_0(sK3(sK4))
    | v2_struct_0(sK3(sK4)) ),
    inference(instantiation,[status(thm)],[c_11749])).

cnf(c_14143,plain,
    ( ~ r1_waybel_7(sK4,k2_yellow19(sK4,sK3(sK4)),sK6(k2_yellow19(sK4,sK3(sK4))))
    | r3_waybel_9(sK4,sK3(sK4),sK6(k2_yellow19(sK4,sK3(sK4))))
    | ~ l1_waybel_0(sK3(sK4),sK4)
    | ~ m1_subset_1(sK6(k2_yellow19(sK4,sK3(sK4))),u1_struct_0(sK4))
    | ~ v4_orders_2(sK3(sK4))
    | ~ v7_waybel_0(sK3(sK4))
    | v2_struct_0(sK3(sK4)) ),
    inference(instantiation,[status(thm)],[c_13539])).

cnf(c_14150,plain,
    ( r1_waybel_7(sK4,k2_yellow19(sK4,sK3(sK4)),sK6(k2_yellow19(sK4,sK3(sK4)))) != iProver_top
    | r3_waybel_9(sK4,sK3(sK4),sK6(k2_yellow19(sK4,sK3(sK4)))) = iProver_top
    | l1_waybel_0(sK3(sK4),sK4) != iProver_top
    | m1_subset_1(sK6(k2_yellow19(sK4,sK3(sK4))),u1_struct_0(sK4)) != iProver_top
    | v4_orders_2(sK3(sK4)) != iProver_top
    | v7_waybel_0(sK3(sK4)) != iProver_top
    | v2_struct_0(sK3(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14143])).

cnf(c_14316,plain,
    ( v1_compts_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13907,c_1080,c_1094,c_1108,c_1122,c_4014,c_4028,c_10186,c_10200,c_10242,c_13754,c_13756,c_14146,c_14150])).

cnf(c_14318,plain,
    ( v1_compts_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14316])).

cnf(c_18,plain,
    ( r3_waybel_9(X0,X1,sK2(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1152,plain,
    ( r3_waybel_9(X0,X1,sK2(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_41])).

cnf(c_1153,plain,
    ( r3_waybel_9(sK4,X0,sK2(sK4,X0))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1152])).

cnf(c_1157,plain,
    ( v2_struct_0(X0)
    | r3_waybel_9(sK4,X0,sK2(sK4,X0))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1153,c_42,c_40])).

cnf(c_1158,plain,
    ( r3_waybel_9(sK4,X0,sK2(sK4,X0))
    | ~ l1_waybel_0(X0,sK4)
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1157])).

cnf(c_11743,plain,
    ( r3_waybel_9(sK4,X0_59,sK2(sK4,X0_59))
    | ~ l1_waybel_0(X0_59,sK4)
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59)
    | v2_struct_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1158])).

cnf(c_14275,plain,
    ( r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X0_58),sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X0_58)))
    | ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),X0_58),sK4)
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),X0_58))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),X0_58))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),X0_58)) ),
    inference(instantiation,[status(thm)],[c_11743])).

cnf(c_14292,plain,
    ( r3_waybel_9(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)))
    | ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_14275])).

cnf(c_19,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v1_compts_1(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1182,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_41])).

cnf(c_1183,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1182])).

cnf(c_1187,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1183,c_42,c_40])).

cnf(c_1188,plain,
    ( ~ l1_waybel_0(X0,sK4)
    | m1_subset_1(sK2(sK4,X0),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1187])).

cnf(c_11742,plain,
    ( ~ l1_waybel_0(X0_59,sK4)
    | m1_subset_1(sK2(sK4,X0_59),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59)
    | v2_struct_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1188])).

cnf(c_14276,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),X0_58),sK4)
    | m1_subset_1(sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),X0_58)),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),X0_58))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),X0_58))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),X0_58)) ),
    inference(instantiation,[status(thm)],[c_11742])).

cnf(c_14288,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
    | m1_subset_1(sK2(sK4,k3_yellow19(sK4,k2_struct_0(sK4),sK5)),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | ~ v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | ~ v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_14276])).

cnf(c_16,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_693,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | ~ l1_pre_topc(X3)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | X2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_694,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | ~ l1_pre_topc(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_3031,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_694])).

cnf(c_3032,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v7_waybel_0(k3_yellow19(sK4,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_3031])).

cnf(c_3036,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v7_waybel_0(k3_yellow19(sK4,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3032,c_42])).

cnf(c_3037,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v7_waybel_0(k3_yellow19(sK4,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_3036])).

cnf(c_11716,plain,
    ( ~ v1_subset_1(X0_58,u1_struct_0(k3_yellow_1(X1_58)))
    | ~ v2_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_58))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK4)))
    | v7_waybel_0(k3_yellow19(sK4,X1_58,X0_58))
    | v1_xboole_0(X1_58)
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_3037])).

cnf(c_13327,plain,
    ( ~ v1_subset_1(X0_58,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),X0_58))
    | v1_xboole_0(X0_58)
    | v1_xboole_0(k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_11716])).

cnf(c_13329,plain,
    ( ~ v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v7_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(k2_struct_0(sK4))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_13327])).

cnf(c_3,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_795,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ l1_pre_topc(X3)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | X2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_3])).

cnf(c_796,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ l1_pre_topc(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2) ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_2932,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_796])).

cnf(c_2933,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(sK4,X1,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2932])).

cnf(c_2937,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | l1_waybel_0(k3_yellow19(sK4,X1,X0),sK4)
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2933,c_42])).

cnf(c_2938,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(sK4,X1,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_2937])).

cnf(c_11719,plain,
    ( ~ v2_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(X1_58))
    | l1_waybel_0(k3_yellow19(sK4,X1_58,X0_58),sK4)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_58))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X1_58)
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_2938])).

cnf(c_13322,plain,
    ( ~ v2_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),X0_58),sK4)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0_58)
    | v1_xboole_0(k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_11719])).

cnf(c_13324,plain,
    ( ~ v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | l1_waybel_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5),sK4)
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v1_xboole_0(k2_struct_0(sK4))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_13322])).

cnf(c_4,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_762,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ l1_pre_topc(X3)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | X2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_4])).

cnf(c_763,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ l1_pre_topc(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_2965,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_763])).

cnf(c_2966,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK4,X1,X0))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2965])).

cnf(c_2970,plain,
    ( ~ v2_struct_0(k3_yellow19(sK4,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2966,c_42])).

cnf(c_2971,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK4,X1,X0)) ),
    inference(renaming,[status(thm)],[c_2970])).

cnf(c_11718,plain,
    ( ~ v2_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_58))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X1_58)
    | v1_xboole_0(X0_58)
    | ~ v2_struct_0(k3_yellow19(sK4,X1_58,X0_58)) ),
    inference(subtyping,[status(esa)],[c_2971])).

cnf(c_13317,plain,
    ( ~ v2_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0_58)
    | v1_xboole_0(k2_struct_0(sK4))
    | ~ v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),X0_58)) ),
    inference(instantiation,[status(thm)],[c_11718])).

cnf(c_13319,plain,
    ( ~ v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v1_xboole_0(k2_struct_0(sK4))
    | v1_xboole_0(sK5)
    | ~ v2_struct_0(k3_yellow19(sK4,k2_struct_0(sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_13317])).

cnf(c_14,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_729,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | ~ l1_pre_topc(X3)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | X2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_730,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | ~ l1_pre_topc(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_2998,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_730])).

cnf(c_2999,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_orders_2(k3_yellow19(sK4,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2998])).

cnf(c_3003,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v4_orders_2(k3_yellow19(sK4,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2999,c_42])).

cnf(c_3004,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_orders_2(k3_yellow19(sK4,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_3003])).

cnf(c_11717,plain,
    ( ~ v2_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(X1_58))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_58))))
    | ~ m1_subset_1(X1_58,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_orders_2(k3_yellow19(sK4,X1_58,X0_58))
    | v1_xboole_0(X1_58)
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_3004])).

cnf(c_13312,plain,
    ( ~ v2_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(X0_58,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),X0_58))
    | v1_xboole_0(X0_58)
    | v1_xboole_0(k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_11717])).

cnf(c_13314,plain,
    ( ~ v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | v4_orders_2(k3_yellow19(sK4,k2_struct_0(sK4),sK5))
    | v1_xboole_0(k2_struct_0(sK4))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_13312])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_604,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_5,c_9])).

cnf(c_2655,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_604,c_40])).

cnf(c_2656,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2655])).

cnf(c_127,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_137,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2658,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2656,c_42,c_40,c_127,c_137])).

cnf(c_11731,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_2658])).

cnf(c_12715,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11731])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_640,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_5,c_0])).

cnf(c_2636,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_640,c_40])).

cnf(c_2637,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2636])).

cnf(c_11734,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_2637])).

cnf(c_12739,plain,
    ( v1_xboole_0(k2_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12715,c_11734])).

cnf(c_13217,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12739])).

cnf(c_1,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_147,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_34,negated_conjecture,
    ( v13_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_35,negated_conjecture,
    ( v2_waybel_0(sK5,k3_yellow_1(k2_struct_0(sK4)))
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_36,negated_conjecture,
    ( v1_subset_1(sK5,u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_37,negated_conjecture,
    ( ~ v1_compts_1(sK4)
    | ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f111])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16347,c_14996,c_14318,c_14292,c_14288,c_13329,c_13324,c_13319,c_13314,c_13217,c_147,c_137,c_33,c_34,c_35,c_36,c_37,c_40])).


%------------------------------------------------------------------------------
