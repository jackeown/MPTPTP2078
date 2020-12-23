%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1624+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:27 EST 2020

% Result     : Theorem 4.08s
% Output     : Refutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  125 (1319 expanded)
%              Number of leaves         :   12 ( 548 expanded)
%              Depth                    :   55
%              Number of atoms          :  839 (11651 expanded)
%              Number of equality atoms :   71 (2175 expanded)
%              Maximal formula depth    :   21 (   9 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5585,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5584,f3250])).

fof(f3250,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f3215,f3217])).

fof(f3217,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f3198])).

fof(f3198,plain,
    ( ~ v2_waybel_0(sK3,sK1)
    & v2_waybel_0(sK2,sK0)
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3174,f3197,f3196,f3195,f3194])).

fof(f3194,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_waybel_0(X3,X1)
                    & v2_waybel_0(X2,X0)
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_waybel_0(X3,X1)
                  & v2_waybel_0(X2,sK0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3195,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_waybel_0(X3,X1)
                & v2_waybel_0(X2,sK0)
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_waybel_0(X3,sK1)
              & v2_waybel_0(X2,sK0)
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3196,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_waybel_0(X3,sK1)
            & v2_waybel_0(X2,sK0)
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ~ v2_waybel_0(X3,sK1)
          & v2_waybel_0(sK2,sK0)
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f3197,plain,
    ( ? [X3] :
        ( ~ v2_waybel_0(X3,sK1)
        & v2_waybel_0(sK2,sK0)
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ~ v2_waybel_0(sK3,sK1)
      & v2_waybel_0(sK2,sK0)
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f3174,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_waybel_0(X3,X1)
                  & v2_waybel_0(X2,X0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f3173])).

fof(f3173,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_waybel_0(X3,X1)
                  & v2_waybel_0(X2,X0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3164])).

fof(f3164,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( ( v2_waybel_0(X2,X0)
                          & X2 = X3 )
                       => v2_waybel_0(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3163])).

fof(f3163,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_waybel_0(X2,X0)
                        & X2 = X3 )
                     => v2_waybel_0(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_0)).

fof(f3215,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3198])).

fof(f5584,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f5583,f3219])).

fof(f3219,plain,(
    ~ v2_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f3198])).

fof(f5583,plain,
    ( v2_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f5580,f3322])).

fof(f3322,plain,(
    ! [X3] :
      ( m1_subset_1(sK5(sK1,X3),u1_struct_0(sK0))
      | v2_waybel_0(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3312,f3213])).

fof(f3213,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f3198])).

fof(f3312,plain,(
    ! [X3] :
      ( m1_subset_1(sK5(sK1,X3),u1_struct_0(sK0))
      | v2_waybel_0(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f3226,f3302])).

fof(f3302,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(equality_resolution,[],[f3297])).

fof(f3297,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f3294,f3213])).

fof(f3294,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK1) = X0
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f3281,f3214])).

fof(f3214,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f3198])).

fof(f3281,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)
      | u1_struct_0(X0) = X1
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f3234,f3247])).

fof(f3247,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3193])).

fof(f3193,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f3234,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f3182])).

fof(f3182,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f1926])).

fof(f1926,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f3226,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3206])).

fof(f3206,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,sK6(X0,X1))
                    | ~ r1_orders_2(X0,X4,sK5(X0,X1))
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(sK6(X0,X1),X1)
                & r2_hidden(sK5(X0,X1),X1)
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ( r1_orders_2(X0,sK7(X0,X1,X5,X6),X6)
                        & r1_orders_2(X0,sK7(X0,X1,X5,X6),X5)
                        & r2_hidden(sK7(X0,X1,X5,X6),X1)
                        & m1_subset_1(sK7(X0,X1,X5,X6),u1_struct_0(X0)) )
                      | ~ r2_hidden(X6,X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f3202,f3205,f3204,f3203])).

fof(f3203,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  | ~ r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                | ~ r1_orders_2(X0,X4,sK5(X0,X1))
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK5(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3204,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              | ~ r1_orders_2(X0,X4,sK5(X0,X1))
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(sK5(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,X4,sK6(X0,X1))
            | ~ r1_orders_2(X0,X4,sK5(X0,X1))
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3205,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X7,X6)
          & r1_orders_2(X0,X7,X5)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,sK7(X0,X1,X5,X6),X6)
        & r1_orders_2(X0,sK7(X0,X1,X5,X6),X5)
        & r2_hidden(sK7(X0,X1,X5,X6),X1)
        & m1_subset_1(sK7(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3202,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r2_hidden(X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ? [X7] :
                          ( r1_orders_2(X0,X7,X6)
                          & r1_orders_2(X0,X7,X5)
                          & r2_hidden(X7,X1)
                          & m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ r2_hidden(X6,X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3201])).

fof(f3201,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r2_hidden(X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3177])).

fof(f3177,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3176])).

fof(f3176,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3155])).

fof(f3155,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X4,X3)
                                & r1_orders_2(X0,X4,X2)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_waybel_0)).

fof(f5580,plain,(
    ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f5579,f3250])).

fof(f5579,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f5578,f3219])).

fof(f5578,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | v2_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f5573,f3323])).

fof(f3323,plain,(
    ! [X4] :
      ( m1_subset_1(sK6(sK1,X4),u1_struct_0(sK0))
      | v2_waybel_0(X4,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3313,f3213])).

fof(f3313,plain,(
    ! [X4] :
      ( m1_subset_1(sK6(sK1,X4),u1_struct_0(sK0))
      | v2_waybel_0(X4,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f3227,f3302])).

fof(f3227,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3206])).

fof(f5573,plain,
    ( ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f5572,f3212])).

fof(f3212,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3198])).

fof(f5572,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f5571,f3250])).

fof(f5571,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f5570,f3249])).

fof(f3249,plain,(
    v2_waybel_0(sK3,sK0) ),
    inference(definition_unfolding,[],[f3218,f3217])).

fof(f3218,plain,(
    v2_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f3198])).

fof(f5570,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ v2_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f5569,f3280])).

fof(f3280,plain,(
    r2_hidden(sK6(sK1,sK3),sK3) ),
    inference(subsumption_resolution,[],[f3279,f3213])).

fof(f3279,plain,
    ( r2_hidden(sK6(sK1,sK3),sK3)
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3274,f3219])).

fof(f3274,plain,
    ( r2_hidden(sK6(sK1,sK3),sK3)
    | v2_waybel_0(sK3,sK1)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f3229,f3216])).

fof(f3216,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f3198])).

fof(f3229,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK6(X0,X1),X1)
      | v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3206])).

fof(f5569,plain,
    ( ~ r2_hidden(sK6(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ v2_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f5568,f3273])).

fof(f3273,plain,(
    r2_hidden(sK5(sK1,sK3),sK3) ),
    inference(subsumption_resolution,[],[f3272,f3213])).

fof(f3272,plain,
    ( r2_hidden(sK5(sK1,sK3),sK3)
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3267,f3219])).

fof(f3267,plain,
    ( r2_hidden(sK5(sK1,sK3),sK3)
    | v2_waybel_0(sK3,sK1)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f3228,f3216])).

fof(f3228,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK5(X0,X1),X1)
      | v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3206])).

fof(f5568,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK3)
    | ~ r2_hidden(sK6(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ v2_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f5555,f3223])).

fof(f3223,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(sK7(X0,X1,X5,X6),X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3206])).

fof(f5555,plain,(
    ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3) ),
    inference(subsumption_resolution,[],[f5554,f3250])).

fof(f5554,plain,
    ( ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f5553,f3219])).

fof(f5553,plain,
    ( ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | v2_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f5548,f3322])).

fof(f5548,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3) ),
    inference(subsumption_resolution,[],[f5547,f3250])).

fof(f5547,plain,
    ( ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f5546,f3219])).

fof(f5546,plain,
    ( ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | v2_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f5396,f3323])).

fof(f5396,plain,
    ( ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f5395,f3212])).

fof(f5395,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f5394,f3250])).

fof(f5394,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f5393,f3249])).

fof(f5393,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ v2_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f5392,f3280])).

fof(f5392,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK6(sK1,sK3),sK3)
    | ~ v2_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f5391,f3273])).

fof(f5391,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK1,sK3),sK3)
    | ~ r2_hidden(sK6(sK1,sK3),sK3)
    | ~ v2_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f5390])).

fof(f5390,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK1,sK3),sK3)
    | ~ r2_hidden(sK6(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ v2_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f5344,f3222])).

fof(f3222,plain,(
    ! [X6,X0,X5,X1] :
      ( m1_subset_1(sK7(X0,X1,X5,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3206])).

fof(f5344,plain,
    ( ~ m1_subset_1(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f5343,f3280])).

fof(f5343,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ r2_hidden(sK6(sK1,sK3),sK3)
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f5342,f3273])).

fof(f5342,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ r2_hidden(sK6(sK1,sK3),sK3)
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f5341])).

fof(f5341,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ r2_hidden(sK5(sK1,sK3),sK3)
    | ~ r2_hidden(sK6(sK1,sK3),sK3)
    | ~ m1_subset_1(sK6(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0)) ),
    inference(resolution,[],[f4872,f3970])).

fof(f3970,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK1,sK7(sK0,sK3,X0,X1),X1)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3968,f3250])).

fof(f3968,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK1,sK7(sK0,sK3,X0,X1),X1)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f3812,f3249])).

fof(f3812,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_waybel_0(X1,sK0)
      | r1_orders_2(sK1,sK7(sK0,X1,X2,X0),X0)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3811,f3212])).

fof(f3811,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK1,sK7(sK0,X1,X2,X0),X0)
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(trivial_inequality_removal,[],[f3810])).

fof(f3810,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK1,sK7(sK0,X1,X2,X0),X0)
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f3809])).

fof(f3809,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK1,sK7(sK0,X1,X2,X0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3370,f3222])).

fof(f3370,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_orders_2(sK1,sK7(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(forward_demodulation,[],[f3369,f3304])).

fof(f3304,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ),
    inference(backward_demodulation,[],[f3214,f3302])).

fof(f3369,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_orders_2(sK1,sK7(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f3366,f3213])).

fof(f3366,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_orders_2(sK1,sK7(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f3337,f3302])).

fof(f3337,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK7(X6,X7,X8,X9),u1_struct_0(X5))
      | ~ m1_subset_1(X9,u1_struct_0(X5))
      | r1_orders_2(X5,sK7(X6,X7,X8,X9),X9)
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | g1_orders_2(u1_struct_0(X6),u1_orders_2(X6)) != g1_orders_2(u1_struct_0(X5),u1_orders_2(X5))
      | ~ l1_orders_2(X5)
      | ~ l1_orders_2(X6)
      | ~ r2_hidden(X9,X7)
      | ~ r2_hidden(X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v2_waybel_0(X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(subsumption_resolution,[],[f3334,f3222])).

fof(f3334,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r1_orders_2(X5,sK7(X6,X7,X8,X9),X9)
      | ~ m1_subset_1(X9,u1_struct_0(X5))
      | ~ m1_subset_1(sK7(X6,X7,X8,X9),u1_struct_0(X5))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ m1_subset_1(sK7(X6,X7,X8,X9),u1_struct_0(X6))
      | g1_orders_2(u1_struct_0(X6),u1_orders_2(X6)) != g1_orders_2(u1_struct_0(X5),u1_orders_2(X5))
      | ~ l1_orders_2(X5)
      | ~ l1_orders_2(X6)
      | ~ r2_hidden(X9,X7)
      | ~ r2_hidden(X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v2_waybel_0(X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(duplicate_literal_removal,[],[f3333])).

fof(f3333,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r1_orders_2(X5,sK7(X6,X7,X8,X9),X9)
      | ~ m1_subset_1(X9,u1_struct_0(X5))
      | ~ m1_subset_1(sK7(X6,X7,X8,X9),u1_struct_0(X5))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ m1_subset_1(sK7(X6,X7,X8,X9),u1_struct_0(X6))
      | g1_orders_2(u1_struct_0(X6),u1_orders_2(X6)) != g1_orders_2(u1_struct_0(X5),u1_orders_2(X5))
      | ~ l1_orders_2(X5)
      | ~ l1_orders_2(X6)
      | ~ r2_hidden(X9,X7)
      | ~ r2_hidden(X8,X7)
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v2_waybel_0(X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_orders_2(X6) ) ),
    inference(resolution,[],[f3256,f3225])).

fof(f3225,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X5,X6),X6)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3206])).

fof(f3256,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r1_orders_2(X0,X4,X5)
      | r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3255])).

fof(f3255,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3240])).

fof(f3240,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3187])).

fof(f3187,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3186])).

fof(f3186,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3014])).

fof(f3014,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_0)).

fof(f4872,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK1,sK7(sK0,sK3,sK6(sK1,sK3),X0),sK5(sK1,sK3))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK7(sK0,sK3,sK6(sK1,sK3),X0),u1_struct_0(sK0))
      | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),X0),sK3) ) ),
    inference(subsumption_resolution,[],[f4871,f3219])).

fof(f4871,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(sK0,sK3,sK6(sK1,sK3),X0),u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_waybel_0(sK3,sK1)
      | ~ r1_orders_2(sK1,sK7(sK0,sK3,sK6(sK1,sK3),X0),sK5(sK1,sK3))
      | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),X0),sK3) ) ),
    inference(subsumption_resolution,[],[f4870,f3250])).

fof(f4870,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(sK0,sK3,sK6(sK1,sK3),X0),u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_waybel_0(sK3,sK1)
      | ~ r1_orders_2(sK1,sK7(sK0,sK3,sK6(sK1,sK3),X0),sK5(sK1,sK3))
      | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,sK3),X0),sK3) ) ),
    inference(resolution,[],[f3981,f3280])).

fof(f3981,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK6(sK1,X5),sK3)
      | ~ m1_subset_1(sK7(sK0,sK3,sK6(sK1,X5),X4),u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v2_waybel_0(X5,sK1)
      | ~ r1_orders_2(sK1,sK7(sK0,sK3,sK6(sK1,X5),X4),sK5(sK1,X5))
      | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,X5),X4),X5) ) ),
    inference(subsumption_resolution,[],[f3980,f3323])).

fof(f3980,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK7(sK0,sK3,sK6(sK1,X5),X4),u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(sK6(sK1,X5),sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(sK1,X5),u1_struct_0(sK0))
      | v2_waybel_0(X5,sK1)
      | ~ r1_orders_2(sK1,sK7(sK0,sK3,sK6(sK1,X5),X4),sK5(sK1,X5))
      | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,X5),X4),X5) ) ),
    inference(forward_demodulation,[],[f3979,f3302])).

fof(f3979,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(sK7(sK0,sK3,sK6(sK1,X5),X4),u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(sK6(sK1,X5),sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(sK1,X5),u1_struct_0(sK0))
      | v2_waybel_0(X5,sK1)
      | ~ r1_orders_2(sK1,sK7(sK0,sK3,sK6(sK1,X5),X4),sK5(sK1,X5))
      | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,X5),X4),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f3978,f3302])).

fof(f3978,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(sK6(sK1,X5),sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(sK1,X5),u1_struct_0(sK0))
      | v2_waybel_0(X5,sK1)
      | ~ r1_orders_2(sK1,sK7(sK0,sK3,sK6(sK1,X5),X4),sK5(sK1,X5))
      | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,X5),X4),X5)
      | ~ m1_subset_1(sK7(sK0,sK3,sK6(sK1,X5),X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f3974,f3213])).

fof(f3974,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(sK6(sK1,X5),sK3)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(sK1,X5),u1_struct_0(sK0))
      | v2_waybel_0(X5,sK1)
      | ~ r1_orders_2(sK1,sK7(sK0,sK3,sK6(sK1,X5),X4),sK5(sK1,X5))
      | ~ r2_hidden(sK7(sK0,sK3,sK6(sK1,X5),X4),X5)
      | ~ m1_subset_1(sK7(sK0,sK3,sK6(sK1,X5),X4),u1_struct_0(sK1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f3966,f3230])).

fof(f3230,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_orders_2(X0,X4,sK6(X0,X1))
      | v2_waybel_0(X1,X0)
      | ~ r1_orders_2(X0,X4,sK5(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3206])).

fof(f3966,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK1,sK7(sK0,sK3,X0,X1),X0)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3964,f3250])).

fof(f3964,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK1,sK7(sK0,sK3,X0,X1),X0)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f3803,f3249])).

fof(f3803,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_waybel_0(X1,sK0)
      | r1_orders_2(sK1,sK7(sK0,X1,X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3802,f3212])).

fof(f3802,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK1,sK7(sK0,X1,X0,X2),X0)
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(trivial_inequality_removal,[],[f3801])).

fof(f3801,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK1,sK7(sK0,X1,X0,X2),X0)
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f3800])).

fof(f3800,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK1,sK7(sK0,X1,X0,X2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_waybel_0(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3364,f3222])).

fof(f3364,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK1,sK7(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(forward_demodulation,[],[f3363,f3304])).

fof(f3363,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK1,sK7(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f3360,f3213])).

fof(f3360,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK1,sK7(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f3336,f3302])).

fof(f3336,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X1,X2,X3,X4),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,sK7(X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X3,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ v2_waybel_0(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(subsumption_resolution,[],[f3335,f3222])).

fof(f3335,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X1,X2,X3,X4),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(sK7(X1,X2,X3,X4),u1_struct_0(X1))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X3,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ v2_waybel_0(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f3332])).

fof(f3332,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X1,X2,X3,X4),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(sK7(X1,X2,X3,X4),u1_struct_0(X1))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X3,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v2_waybel_0(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f3256,f3224])).

fof(f3224,plain,(
    ! [X6,X0,X5,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X5,X6),X5)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3206])).
%------------------------------------------------------------------------------
