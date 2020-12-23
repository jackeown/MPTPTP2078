%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1648+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:28 EST 2020

% Result     : Theorem 18.46s
% Output     : Refutation 18.46s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 712 expanded)
%              Number of leaves         :   15 ( 228 expanded)
%              Depth                    :   16
%              Number of atoms          :  365 (4444 expanded)
%              Number of equality atoms :   14 ( 120 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18655,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18607,f5185])).

fof(f5185,plain,(
    r2_hidden(sK6(sK0,k3_tarski(sK1)),sK18(sK1,sK6(sK0,k3_tarski(sK1)))) ),
    inference(unit_resulting_resolution,[],[f4385,f3995])).

fof(f3995,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK18(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f3686])).

fof(f3686,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK18(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3433])).

fof(f3433,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK16(X0,X1),X3) )
            | ~ r2_hidden(sK16(X0,X1),X1) )
          & ( ( r2_hidden(sK17(X0,X1),X0)
              & r2_hidden(sK16(X0,X1),sK17(X0,X1)) )
            | r2_hidden(sK16(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK18(X0,X5),X0)
                & r2_hidden(X5,sK18(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18])],[f3429,f3432,f3431,f3430])).

fof(f3430,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK16(X0,X1),X3) )
          | ~ r2_hidden(sK16(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK16(X0,X1),X4) )
          | r2_hidden(sK16(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f3431,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK16(X0,X1),X4) )
     => ( r2_hidden(sK17(X0,X1),X0)
        & r2_hidden(sK16(X0,X1),sK17(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3432,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK18(X0,X5),X0)
        & r2_hidden(X5,sK18(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3429,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f3428])).

fof(f3428,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f287])).

fof(f287,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f4385,plain,(
    r2_hidden(sK6(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f3623,f4249,f4238,f3654])).

fof(f3654,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK6(X0,X1),X1)
      | v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3405])).

fof(f3405,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK7(X0,X1),X1)
                & r1_orders_2(X0,sK6(X0,X1),sK7(X0,X1))
                & r2_hidden(sK6(X0,X1),X1)
                & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f3402,f3404,f3403])).

fof(f3403,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK6(X0,X1),X3)
            & r2_hidden(sK6(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3404,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK6(X0,X1),X3)
          & r2_hidden(sK6(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r1_orders_2(X0,sK6(X0,X1),sK7(X0,X1))
        & r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3402,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3401])).

fof(f3401,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3251])).

fof(f3251,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3250])).

fof(f3250,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3164])).

fof(f3164,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f4238,plain,(
    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f4208,f4209])).

fof(f4209,plain,(
    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(unit_resulting_resolution,[],[f3624,f3628])).

fof(f3628,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3245])).

fof(f3245,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f581])).

fof(f581,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f3624,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f3391])).

fof(f3391,plain,
    ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) )
    & ! [X2] :
        ( v13_waybel_0(X2,sK0)
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f3243,f3390,f3389])).

fof(f3389,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) )
            & ! [X2] :
                ( v13_waybel_0(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),X1),k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(sK0),X1),sK0) )
          & ! [X2] :
              ( v13_waybel_0(X2,sK0)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3390,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),X1),k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(sK0),X1),sK0) )
        & ! [X2] :
            ( v13_waybel_0(X2,sK0)
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) )
      & ! [X2] :
          ( v13_waybel_0(X2,sK0)
          | ~ r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f3243,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) )
          & ! [X2] :
              ( v13_waybel_0(X2,X0)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f3242])).

fof(f3242,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) )
          & ! [X2] :
              ( v13_waybel_0(X2,X0)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3213])).

fof(f3213,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X2,X1)
                   => v13_waybel_0(X2,X0) ) )
             => ( m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f3212])).

fof(f3212,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v13_waybel_0(X2,X0) ) )
           => ( m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_waybel_0)).

fof(f4208,plain,(
    m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f3624,f3627])).

fof(f3627,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3244])).

fof(f3244,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f563])).

fof(f563,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f4249,plain,(
    ~ v13_waybel_0(k3_tarski(sK1),sK0) ),
    inference(global_subsumption,[],[f4237,f4238])).

fof(f4237,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k3_tarski(sK1),sK0) ),
    inference(forward_demodulation,[],[f4236,f4209])).

fof(f4236,plain,
    ( ~ v13_waybel_0(k3_tarski(sK1),sK0)
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f3626,f4209])).

fof(f3626,plain,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f3391])).

fof(f3623,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3391])).

fof(f18607,plain,(
    ~ r2_hidden(sK6(sK0,k3_tarski(sK1)),sK18(sK1,sK6(sK0,k3_tarski(sK1)))) ),
    inference(unit_resulting_resolution,[],[f5184,f11096])).

fof(f11096,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK0,k3_tarski(sK1)),X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f11095,f5222])).

fof(f5222,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(sK0,k3_tarski(sK1)),X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f4387,f3993])).

fof(f3993,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f3688])).

fof(f3688,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3433])).

fof(f4387,plain,(
    ~ r2_hidden(sK7(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f3623,f4249,f4238,f3656])).

fof(f3656,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK7(X0,X1),X1)
      | v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3405])).

fof(f11095,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK6(sK0,k3_tarski(sK1)),X0)
      | r2_hidden(sK7(sK0,k3_tarski(sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f11094,f4383])).

fof(f4383,plain,(
    m1_subset_1(sK6(sK0,k3_tarski(sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f3623,f4249,f4238,f3652])).

fof(f3652,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3405])).

fof(f11094,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK6(sK0,k3_tarski(sK1)),X0)
      | ~ m1_subset_1(sK6(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
      | r2_hidden(sK7(sK0,k3_tarski(sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f11088,f4384])).

fof(f4384,plain,(
    m1_subset_1(sK7(sK0,k3_tarski(sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f3623,f4249,f4238,f3653])).

fof(f3653,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3405])).

fof(f11088,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK6(sK0,k3_tarski(sK1)),X0)
      | ~ m1_subset_1(sK7(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
      | r2_hidden(sK7(sK0,k3_tarski(sK1)),X0) ) ),
    inference(resolution,[],[f4533,f4386])).

fof(f4386,plain,(
    r1_orders_2(sK0,sK6(sK0,k3_tarski(sK1)),sK7(sK0,k3_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f3623,f4249,f4238,f3655])).

fof(f3655,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,sK6(X0,X1),sK7(X0,X1))
      | v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3405])).

fof(f4533,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_orders_2(sK0,X2,X3)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X3,X1) ) ),
    inference(subsumption_resolution,[],[f4532,f4294])).

fof(f4294,plain,(
    ! [X66] :
      ( v13_waybel_0(X66,sK0)
      | ~ r2_hidden(X66,sK1) ) ),
    inference(subsumption_resolution,[],[f4287,f4226])).

fof(f4226,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f3624,f3676])).

fof(f3676,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f3267])).

fof(f3267,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f488])).

fof(f488,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f4287,plain,(
    ! [X66] :
      ( ~ r2_hidden(X66,sK1)
      | v13_waybel_0(X66,sK0)
      | ~ r2_hidden(X66,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f3625,f3679])).

fof(f3679,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3270])).

fof(f3270,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f3625,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,sK1)
      | v13_waybel_0(X2,sK0) ) ),
    inference(cnf_transformation,[],[f3391])).

fof(f4532,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r1_orders_2(sK0,X2,X3)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v13_waybel_0(X1,sK0)
      | r2_hidden(X3,X1) ) ),
    inference(subsumption_resolution,[],[f4511,f3623])).

fof(f4511,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r1_orders_2(sK0,X2,X3)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v13_waybel_0(X1,sK0)
      | r2_hidden(X3,X1)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f4227,f3651])).

fof(f3651,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | r2_hidden(X5,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3405])).

fof(f4227,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f3624,f3665])).

fof(f3665,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3260])).

fof(f3260,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f3259])).

fof(f3259,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f5184,plain,(
    r2_hidden(sK18(sK1,sK6(sK0,k3_tarski(sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f4385,f3994])).

fof(f3994,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK18(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f3687])).

fof(f3687,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK18(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3433])).
%------------------------------------------------------------------------------
