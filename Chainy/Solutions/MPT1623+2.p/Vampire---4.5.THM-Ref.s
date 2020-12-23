%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1623+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:27 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  156 (1787 expanded)
%              Number of leaves         :   13 ( 747 expanded)
%              Depth                    :   71
%              Number of atoms          :  936 (15312 expanded)
%              Number of equality atoms :   79 (3036 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5086,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5085,f3237])).

fof(f3237,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f3206,f3208])).

fof(f3208,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f3191])).

fof(f3191,plain,
    ( ~ v1_waybel_0(sK3,sK1)
    & v1_waybel_0(sK2,sK0)
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3172,f3190,f3189,f3188,f3187])).

fof(f3187,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v1_waybel_0(X3,X1)
                    & v1_waybel_0(X2,X0)
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_waybel_0(X3,X1)
                  & v1_waybel_0(X2,sK0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3188,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v1_waybel_0(X3,X1)
                & v1_waybel_0(X2,sK0)
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v1_waybel_0(X3,sK1)
              & v1_waybel_0(X2,sK0)
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3189,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v1_waybel_0(X3,sK1)
            & v1_waybel_0(X2,sK0)
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ~ v1_waybel_0(X3,sK1)
          & v1_waybel_0(sK2,sK0)
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f3190,plain,
    ( ? [X3] :
        ( ~ v1_waybel_0(X3,sK1)
        & v1_waybel_0(sK2,sK0)
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ~ v1_waybel_0(sK3,sK1)
      & v1_waybel_0(sK2,sK0)
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f3172,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_waybel_0(X3,X1)
                  & v1_waybel_0(X2,X0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f3171])).

fof(f3171,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_waybel_0(X3,X1)
                  & v1_waybel_0(X2,X0)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3163])).

fof(f3163,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( ( v1_waybel_0(X2,X0)
                          & X2 = X3 )
                       => v1_waybel_0(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3162])).

fof(f3162,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v1_waybel_0(X2,X0)
                        & X2 = X3 )
                     => v1_waybel_0(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_0)).

fof(f3206,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3191])).

fof(f5085,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f5084,f3210])).

fof(f3210,plain,(
    ~ v1_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f3191])).

fof(f5084,plain,
    ( v1_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f5075,f3301])).

fof(f3301,plain,(
    ! [X3] :
      ( m1_subset_1(sK4(sK1,X3),u1_struct_0(sK0))
      | v1_waybel_0(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3292,f3204])).

fof(f3204,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f3191])).

fof(f3292,plain,(
    ! [X3] :
      ( m1_subset_1(sK4(sK1,X3),u1_struct_0(sK0))
      | v1_waybel_0(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f3215,f3286])).

fof(f3286,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(equality_resolution,[],[f3278])).

fof(f3278,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f3275,f3204])).

fof(f3275,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK1) = X0
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f3260,f3205])).

fof(f3205,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f3191])).

fof(f3260,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)
      | u1_struct_0(X0) = X1
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f3221,f3234])).

fof(f3234,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3186])).

fof(f3186,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f3221,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f3175])).

fof(f3175,plain,(
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

fof(f3215,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3197])).

fof(f3197,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              | ( ! [X4] :
                    ( ~ r1_orders_2(X0,sK5(X0,X1),X4)
                    | ~ r1_orders_2(X0,sK4(X0,X1),X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(sK5(X0,X1),X1)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ( r1_orders_2(X0,X6,sK6(X0,X1,X5,X6))
                        & r1_orders_2(X0,X5,sK6(X0,X1,X5,X6))
                        & r2_hidden(sK6(X0,X1,X5,X6),X1)
                        & m1_subset_1(sK6(X0,X1,X5,X6),u1_struct_0(X0)) )
                      | ~ r2_hidden(X6,X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f3193,f3196,f3195,f3194])).

fof(f3194,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  | ~ r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                | ~ r1_orders_2(X0,sK4(X0,X1),X4)
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3195,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X3,X4)
              | ~ r1_orders_2(X0,sK4(X0,X1),X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(sK4(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,sK5(X0,X1),X4)
            | ~ r1_orders_2(X0,sK4(X0,X1),X4)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3196,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X6,sK6(X0,X1,X5,X6))
        & r1_orders_2(X0,X5,sK6(X0,X1,X5,X6))
        & r2_hidden(sK6(X0,X1,X5,X6),X1)
        & m1_subset_1(sK6(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3193,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r2_hidden(X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ? [X7] :
                          ( r1_orders_2(X0,X6,X7)
                          & r1_orders_2(X0,X5,X7)
                          & r2_hidden(X7,X1)
                          & m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ r2_hidden(X6,X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3192])).

fof(f3192,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r2_hidden(X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3174])).

fof(f3174,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3173])).

fof(f3173,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3154])).

fof(f3154,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X3,X4)
                                & r1_orders_2(X0,X2,X4)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_0)).

fof(f5075,plain,(
    ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f5074,f3237])).

fof(f5074,plain,
    ( ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f5073,f3210])).

fof(f5073,plain,
    ( ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | v1_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f5000,f3302])).

fof(f3302,plain,(
    ! [X4] :
      ( m1_subset_1(sK5(sK1,X4),u1_struct_0(sK0))
      | v1_waybel_0(X4,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3293,f3204])).

fof(f3293,plain,(
    ! [X4] :
      ( m1_subset_1(sK5(sK1,X4),u1_struct_0(sK0))
      | v1_waybel_0(X4,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f3216,f3286])).

fof(f3216,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3197])).

fof(f5000,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4999,f3203])).

fof(f3203,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3191])).

fof(f4999,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f4998,f3237])).

fof(f4998,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f4997,f3236])).

fof(f3236,plain,(
    v1_waybel_0(sK3,sK0) ),
    inference(definition_unfolding,[],[f3209,f3208])).

fof(f3209,plain,(
    v1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f3191])).

fof(f4997,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ v1_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f4996,f3254])).

fof(f3254,plain,(
    r2_hidden(sK4(sK1,sK3),sK3) ),
    inference(subsumption_resolution,[],[f3253,f3204])).

fof(f3253,plain,
    ( r2_hidden(sK4(sK1,sK3),sK3)
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3251,f3210])).

fof(f3251,plain,
    ( r2_hidden(sK4(sK1,sK3),sK3)
    | v1_waybel_0(sK3,sK1)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f3217,f3207])).

fof(f3207,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f3191])).

fof(f3217,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1),X1)
      | v1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3197])).

fof(f4996,plain,
    ( ~ r2_hidden(sK4(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ v1_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f4995,f3259])).

fof(f3259,plain,(
    r2_hidden(sK5(sK1,sK3),sK3) ),
    inference(subsumption_resolution,[],[f3258,f3204])).

fof(f3258,plain,
    ( r2_hidden(sK5(sK1,sK3),sK3)
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3256,f3210])).

fof(f3256,plain,
    ( r2_hidden(sK5(sK1,sK3),sK3)
    | v1_waybel_0(sK3,sK1)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f3218,f3207])).

fof(f3218,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK5(X0,X1),X1)
      | v1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3197])).

fof(f4995,plain,
    ( ~ r2_hidden(sK5(sK1,sK3),sK3)
    | ~ r2_hidden(sK4(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ v1_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f4914,f3212])).

fof(f3212,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(sK6(X0,X1,X5,X6),X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3197])).

fof(f4914,plain,(
    ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3) ),
    inference(subsumption_resolution,[],[f4913,f3237])).

fof(f4913,plain,
    ( ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f4912,f3210])).

fof(f4912,plain,
    ( ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | v1_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f4769,f3301])).

fof(f4769,plain,
    ( ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3) ),
    inference(subsumption_resolution,[],[f4768,f3237])).

fof(f4768,plain,
    ( ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f4767,f3210])).

fof(f4767,plain,
    ( ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | v1_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f4724,f3302])).

fof(f4724,plain,
    ( ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3) ),
    inference(subsumption_resolution,[],[f4723,f3203])).

fof(f4723,plain,
    ( ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f4722,f3237])).

fof(f4722,plain,
    ( ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f4721,f3236])).

fof(f4721,plain,
    ( ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ v1_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f4720,f3254])).

fof(f4720,plain,
    ( ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK4(sK1,sK3),sK3)
    | ~ v1_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f4719,f3259])).

fof(f4719,plain,
    ( ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK1,sK3),sK3)
    | ~ r2_hidden(sK4(sK1,sK3),sK3)
    | ~ v1_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f4718])).

fof(f4718,plain,
    ( ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK1,sK3),sK3)
    | ~ r2_hidden(sK4(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ v1_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f4717,f3211])).

fof(f3211,plain,(
    ! [X6,X0,X5,X1] :
      ( m1_subset_1(sK6(X0,X1,X5,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3197])).

fof(f4717,plain,
    ( ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),u1_struct_0(sK0))
    | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4716,f3254])).

fof(f4716,plain,
    ( ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),u1_struct_0(sK0))
    | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK4(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4715,f3237])).

fof(f4715,plain,
    ( ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK4(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4714,f3210])).

fof(f4714,plain,
    ( ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),u1_struct_0(sK0))
    | v1_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK4(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4713,f3259])).

fof(f4713,plain,
    ( ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK1,sK3),sK3)
    | v1_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK4(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f4712])).

fof(f4712,plain,
    ( ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK1,sK3),sK3)
    | v1_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,sK3)),sK3)
    | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK4(sK1,sK3),sK3)
    | ~ m1_subset_1(sK5(sK1,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK1,sK3),sK3) ),
    inference(resolution,[],[f4024,f4049])).

fof(f4049,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK1,X0,sK6(sK0,sK3,X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(subsumption_resolution,[],[f4048,f3203])).

fof(f4048,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK1,X0,sK6(sK0,sK3,X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK3)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f4047,f3237])).

fof(f4047,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK1,X0,sK6(sK0,sK3,X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f4046,f3236])).

fof(f4046,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK1,X0,sK6(sK0,sK3,X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK3)
      | ~ v1_waybel_0(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f4045])).

fof(f4045,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK1,X0,sK6(sK0,sK3,X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_waybel_0(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3652,f3211])).

fof(f3652,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(sK0,sK3,X0,X1),u1_struct_0(sK0))
      | r1_orders_2(sK1,X0,sK6(sK0,sK3,X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(duplicate_literal_removal,[],[f3649])).

fof(f3649,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK1,X0,sK6(sK0,sK3,X0,X1))
      | ~ m1_subset_1(sK6(sK0,sK3,X0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f3599,f3281])).

fof(f3281,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK0,X1,sK6(sK0,sK3,X1,X0))
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f3280,f3203])).

fof(f3280,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK6(sK0,sK3,X1,X0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3279,f3237])).

fof(f3279,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK6(sK0,sK3,X1,X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3213,f3236])).

fof(f3213,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ v1_waybel_0(X1,X0)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X5,sK6(X0,X1,X5,X6))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3197])).

fof(f3599,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK1,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3598,f3203])).

fof(f3598,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK1,X1,X0)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3597])).

fof(f3597,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK1,X1,X0)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3360,f3232])).

fof(f3232,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3200])).

fof(f3200,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3185])).

fof(f3185,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1885])).

fof(f1885,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f3360,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK1,X2,X3) ) ),
    inference(forward_demodulation,[],[f3359,f3286])).

fof(f3359,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(sK0))
      | r1_orders_2(sK1,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f3358,f3286])).

fof(f3358,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(sK0))
      | r1_orders_2(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f3349,f3204])).

fof(f3349,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(sK0))
      | r1_orders_2(sK1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f3233,f3342])).

fof(f3342,plain,(
    u1_orders_2(sK0) = u1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f3341,f3203])).

fof(f3341,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ l1_orders_2(sK0) ),
    inference(equality_resolution,[],[f3312])).

fof(f3312,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_orders_2(X0) = u1_orders_2(sK1)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f3264,f3288])).

fof(f3288,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ),
    inference(backward_demodulation,[],[f3205,f3286])).

fof(f3264,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)
      | u1_orders_2(X0) = X2
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f3222,f3234])).

fof(f3222,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f3175])).

fof(f3233,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3200])).

fof(f4024,plain,(
    ! [X1] :
      ( ~ r1_orders_2(sK1,sK4(sK1,X1),sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)))
      | ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)),u1_struct_0(sK0))
      | ~ r2_hidden(sK5(sK1,X1),sK3)
      | v1_waybel_0(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)),X1) ) ),
    inference(subsumption_resolution,[],[f4023,f3302])).

fof(f4023,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)),u1_struct_0(sK0))
      | ~ m1_subset_1(sK5(sK1,X1),u1_struct_0(sK0))
      | ~ r2_hidden(sK5(sK1,X1),sK3)
      | v1_waybel_0(X1,sK1)
      | ~ r1_orders_2(sK1,sK4(sK1,X1),sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)))
      | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)),X1) ) ),
    inference(forward_demodulation,[],[f4022,f3286])).

fof(f4022,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)),u1_struct_0(sK0))
      | ~ m1_subset_1(sK5(sK1,X1),u1_struct_0(sK0))
      | ~ r2_hidden(sK5(sK1,X1),sK3)
      | v1_waybel_0(X1,sK1)
      | ~ r1_orders_2(sK1,sK4(sK1,X1),sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)))
      | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f4021,f3286])).

fof(f4021,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK5(sK1,X1),u1_struct_0(sK0))
      | ~ r2_hidden(sK5(sK1,X1),sK3)
      | v1_waybel_0(X1,sK1)
      | ~ r1_orders_2(sK1,sK4(sK1,X1),sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)))
      | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)),X1)
      | ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)),u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f4018,f3204])).

fof(f4018,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK5(sK1,X1),u1_struct_0(sK0))
      | ~ r2_hidden(sK5(sK1,X1),sK3)
      | v1_waybel_0(X1,sK1)
      | ~ r1_orders_2(sK1,sK4(sK1,X1),sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)))
      | ~ r2_hidden(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)),X1)
      | ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),sK5(sK1,X1)),u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f3963,f3219])).

fof(f3219,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1),X4)
      | v1_waybel_0(X1,X0)
      | ~ r1_orders_2(X0,sK4(X0,X1),X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3197])).

fof(f3963,plain,(
    ! [X0] :
      ( r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f3962,f3237])).

fof(f3962,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3961,f3210])).

fof(f3961,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | v1_waybel_0(sK3,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f3950,f3301])).

fof(f3950,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0)) ) ),
    inference(subsumption_resolution,[],[f3949,f3203])).

fof(f3949,plain,(
    ! [X0] :
      ( r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3948,f3237])).

fof(f3948,plain,(
    ! [X0] :
      ( r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3947,f3236])).

fof(f3947,plain,(
    ! [X0] :
      ( r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
      | ~ v1_waybel_0(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3946,f3254])).

fof(f3946,plain,(
    ! [X0] :
      ( r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK4(sK1,sK3),sK3)
      | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
      | ~ v1_waybel_0(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3945])).

fof(f3945,plain,(
    ! [X0] :
      ( r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(sK4(sK1,sK3),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
      | ~ v1_waybel_0(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3874,f3211])).

fof(f3874,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),X0),u1_struct_0(sK0))
      | r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(trivial_inequality_removal,[],[f3873])).

fof(f3873,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),X0),u1_struct_0(sK0))
      | r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f3872,f3342])).

fof(f3872,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),X0),u1_struct_0(sK0))
      | r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ) ),
    inference(subsumption_resolution,[],[f3869,f3204])).

fof(f3869,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),X0),u1_struct_0(sK0))
      | r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(duplicate_literal_removal,[],[f3864])).

fof(f3864,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),X0),u1_struct_0(sK0))
      | r1_orders_2(sK1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f3705,f3286])).

fof(f3705,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),X0),u1_struct_0(X1))
      | r1_orders_2(X1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f3704,f3237])).

fof(f3704,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | r1_orders_2(X1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),X0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3703,f3210])).

fof(f3703,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | r1_orders_2(X1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),X0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X1)
      | v1_waybel_0(sK3,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f3561,f3301])).

fof(f3561,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4(sK1,sK3),u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | r1_orders_2(X1,X0,sK6(sK0,sK3,sK4(sK1,sK3),X0))
      | ~ m1_subset_1(sK6(sK0,sK3,sK4(sK1,sK3),X0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f3406,f3254])).

fof(f3406,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | r1_orders_2(X2,X0,sK6(sK0,sK3,X1,X0))
      | ~ m1_subset_1(sK6(sK0,sK3,X1,X0),u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X2) ) ),
    inference(subsumption_resolution,[],[f3405,f3203])).

fof(f3405,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | r1_orders_2(X2,X0,sK6(sK0,sK3,X1,X0))
      | ~ m1_subset_1(sK6(sK0,sK3,X1,X0),u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X1,sK3)
      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X2)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3404,f3237])).

fof(f3404,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | r1_orders_2(X2,X0,sK6(sK0,sK3,X1,X0))
      | ~ m1_subset_1(sK6(sK0,sK3,X1,X0),u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X1,sK3)
      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3403,f3236])).

fof(f3403,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | r1_orders_2(X2,X0,sK6(sK0,sK3,X1,X0))
      | ~ m1_subset_1(sK6(sK0,sK3,X1,X0),u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X1,sK3)
      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X2)
      | ~ v1_waybel_0(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3402])).

fof(f3402,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | r1_orders_2(X2,X0,sK6(sK0,sK3,X1,X0))
      | ~ m1_subset_1(sK6(sK0,sK3,X1,X0),u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X1,sK3)
      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X2)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v1_waybel_0(sK3,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3339,f3211])).

fof(f3339,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(sK6(sK0,sK3,X2,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK3)
      | r1_orders_2(X4,X3,sK6(sK0,sK3,X2,X3))
      | ~ m1_subset_1(sK6(sK0,sK3,X2,X3),u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ r2_hidden(X2,sK3)
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
      | ~ l1_orders_2(X4) ) ),
    inference(subsumption_resolution,[],[f3337,f3203])).

fof(f3337,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK3)
      | r1_orders_2(X4,X3,sK6(sK0,sK3,X2,X3))
      | ~ m1_subset_1(sK6(sK0,sK3,X2,X3),u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(sK6(sK0,sK3,X2,X3),u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
      | ~ l1_orders_2(X4)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3336])).

fof(f3336,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK3)
      | r1_orders_2(X4,X3,sK6(sK0,sK3,X2,X3))
      | ~ m1_subset_1(sK6(sK0,sK3,X2,X3),u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(sK6(sK0,sK3,X2,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
      | ~ l1_orders_2(X4)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3284,f3243])).

fof(f3243,plain,(
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
    inference(equality_resolution,[],[f3242])).

fof(f3242,plain,(
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
    inference(equality_resolution,[],[f3227])).

fof(f3227,plain,(
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
    inference(cnf_transformation,[],[f3180])).

fof(f3180,plain,(
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
    inference(flattening,[],[f3179])).

fof(f3179,plain,(
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

fof(f3284,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK0,X0,sK6(sK0,sK3,X1,X0))
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f3283,f3203])).

fof(f3283,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,sK6(sK0,sK3,X1,X0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3282,f3237])).

fof(f3282,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,sK6(sK0,sK3,X1,X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3214,f3236])).

fof(f3214,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ v1_waybel_0(X1,X0)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X6,sK6(X0,X1,X5,X6))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3197])).
%------------------------------------------------------------------------------
