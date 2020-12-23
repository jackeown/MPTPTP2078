%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1646+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:28 EST 2020

% Result     : Theorem 12.95s
% Output     : Refutation 12.95s
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
fof(f13338,plain,(
    $false ),
    inference(subsumption_resolution,[],[f13292,f4815])).

fof(f4815,plain,(
    r2_hidden(sK5(sK0,k3_tarski(sK1)),sK17(sK1,sK5(sK0,k3_tarski(sK1)))) ),
    inference(unit_resulting_resolution,[],[f4251,f3930])).

fof(f3930,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK17(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f3649])).

fof(f3649,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK17(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3410])).

fof(f3410,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK15(X0,X1),X3) )
            | ~ r2_hidden(sK15(X0,X1),X1) )
          & ( ( r2_hidden(sK16(X0,X1),X0)
              & r2_hidden(sK15(X0,X1),sK16(X0,X1)) )
            | r2_hidden(sK15(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK17(X0,X5),X0)
                & r2_hidden(X5,sK17(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f3406,f3409,f3408,f3407])).

fof(f3407,plain,(
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
              | ~ r2_hidden(sK15(X0,X1),X3) )
          | ~ r2_hidden(sK15(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK15(X0,X1),X4) )
          | r2_hidden(sK15(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f3408,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK15(X0,X1),X4) )
     => ( r2_hidden(sK16(X0,X1),X0)
        & r2_hidden(sK15(X0,X1),sK16(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3409,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK17(X0,X5),X0)
        & r2_hidden(X5,sK17(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3406,plain,(
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
    inference(rectify,[],[f3405])).

fof(f3405,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f4251,plain,(
    r2_hidden(sK5(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f3591,f4180,f4169,f3619])).

fof(f3619,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK5(X0,X1),X1)
      | v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3382])).

fof(f3382,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK6(X0,X1),X1)
                & r1_orders_2(X0,sK6(X0,X1),sK5(X0,X1))
                & r2_hidden(sK5(X0,X1),X1)
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f3379,f3381,f3380])).

fof(f3380,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X3,X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,X3,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3381,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,sK5(X0,X1))
          & r2_hidden(sK5(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r1_orders_2(X0,sK6(X0,X1),sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3379,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3378])).

fof(f3378,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3247])).

fof(f3247,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3246])).

fof(f3246,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3162])).

fof(f3162,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_waybel_0)).

fof(f4169,plain,(
    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f4139,f4140])).

fof(f4140,plain,(
    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(unit_resulting_resolution,[],[f3592,f3596])).

fof(f3596,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3242])).

fof(f3242,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f581])).

fof(f581,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f3592,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f3370])).

fof(f3370,plain,
    ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) )
    & ! [X2] :
        ( v12_waybel_0(X2,sK0)
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f3240,f3369,f3368])).

fof(f3368,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v12_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) )
            & ! [X2] :
                ( v12_waybel_0(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),X1),k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v12_waybel_0(k5_setfam_1(u1_struct_0(sK0),X1),sK0) )
          & ! [X2] :
              ( v12_waybel_0(X2,sK0)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3369,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),X1),k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v12_waybel_0(k5_setfam_1(u1_struct_0(sK0),X1),sK0) )
        & ! [X2] :
            ( v12_waybel_0(X2,sK0)
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) )
      & ! [X2] :
          ( v12_waybel_0(X2,sK0)
          | ~ r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f3240,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) )
          & ! [X2] :
              ( v12_waybel_0(X2,X0)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f3239])).

fof(f3239,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) )
          & ! [X2] :
              ( v12_waybel_0(X2,X0)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3211])).

fof(f3211,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X2,X1)
                   => v12_waybel_0(X2,X0) ) )
             => ( m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v12_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f3210])).

fof(f3210,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v12_waybel_0(X2,X0) ) )
           => ( m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_waybel_0)).

fof(f4139,plain,(
    m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f3592,f3595])).

fof(f3595,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3241])).

fof(f3241,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f563])).

fof(f563,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f4180,plain,(
    ~ v12_waybel_0(k3_tarski(sK1),sK0) ),
    inference(global_subsumption,[],[f4168,f4169])).

fof(f4168,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k3_tarski(sK1),sK0) ),
    inference(forward_demodulation,[],[f4167,f4140])).

fof(f4167,plain,
    ( ~ v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f3594,f4140])).

fof(f3594,plain,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f3370])).

fof(f3591,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3370])).

fof(f13292,plain,(
    ~ r2_hidden(sK5(sK0,k3_tarski(sK1)),sK17(sK1,sK5(sK0,k3_tarski(sK1)))) ),
    inference(unit_resulting_resolution,[],[f4814,f8803])).

fof(f8803,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK0,k3_tarski(sK1)),X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f8802,f4852])).

fof(f4852,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK0,k3_tarski(sK1)),X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f4253,f3928])).

fof(f3928,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f3651])).

fof(f3651,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3410])).

fof(f4253,plain,(
    ~ r2_hidden(sK6(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f3591,f4180,f4169,f3621])).

fof(f3621,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK6(X0,X1),X1)
      | v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3382])).

fof(f8802,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK5(sK0,k3_tarski(sK1)),X0)
      | r2_hidden(sK6(sK0,k3_tarski(sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f8801,f4249])).

fof(f4249,plain,(
    m1_subset_1(sK5(sK0,k3_tarski(sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f3591,f4180,f4169,f3617])).

fof(f3617,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3382])).

fof(f8801,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK5(sK0,k3_tarski(sK1)),X0)
      | ~ m1_subset_1(sK5(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,k3_tarski(sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f8796,f4250])).

fof(f4250,plain,(
    m1_subset_1(sK6(sK0,k3_tarski(sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f3591,f4180,f4169,f3618])).

fof(f3618,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3382])).

fof(f8796,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK5(sK0,k3_tarski(sK1)),X0)
      | ~ m1_subset_1(sK6(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
      | ~ m1_subset_1(sK5(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,k3_tarski(sK1)),X0) ) ),
    inference(resolution,[],[f4368,f4252])).

fof(f4252,plain,(
    r1_orders_2(sK0,sK6(sK0,k3_tarski(sK1)),sK5(sK0,k3_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f3591,f4180,f4169,f3620])).

fof(f3620,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,sK6(X0,X1),sK5(X0,X1))
      | v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3382])).

fof(f4368,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_orders_2(sK0,X2,X3)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f4367,f4216])).

fof(f4216,plain,(
    ! [X62] :
      ( v12_waybel_0(X62,sK0)
      | ~ r2_hidden(X62,sK1) ) ),
    inference(subsumption_resolution,[],[f4213,f4157])).

fof(f4157,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f3592,f3639])).

fof(f3639,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f3261])).

fof(f3261,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f4213,plain,(
    ! [X62] :
      ( ~ r2_hidden(X62,sK1)
      | v12_waybel_0(X62,sK0)
      | ~ r2_hidden(X62,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f3593,f3642])).

fof(f3642,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3264,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f3593,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,sK1)
      | v12_waybel_0(X2,sK0) ) ),
    inference(cnf_transformation,[],[f3370])).

fof(f4367,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r1_orders_2(sK0,X2,X3)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v12_waybel_0(X1,sK0)
      | r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f4351,f3591])).

fof(f4351,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r1_orders_2(sK0,X2,X3)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v12_waybel_0(X1,sK0)
      | r2_hidden(X2,X1)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f4158,f3616])).

fof(f3616,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | r2_hidden(X5,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3382])).

fof(f4158,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f3592,f3628])).

fof(f3628,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3254])).

fof(f3254,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f3253])).

fof(f3253,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f4814,plain,(
    r2_hidden(sK17(sK1,sK5(sK0,k3_tarski(sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f4251,f3929])).

fof(f3929,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK17(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f3650])).

fof(f3650,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK17(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3410])).
%------------------------------------------------------------------------------
