%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1923+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:38 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 638 expanded)
%              Number of leaves         :   16 ( 336 expanded)
%              Depth                    :   20
%              Number of atoms          :  497 (8486 expanded)
%              Number of equality atoms :   49 (1531 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8648,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8647,f4044])).

fof(f4044,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f3979])).

fof(f3979,plain,
    ( ~ r1_orders_2(sK2,sK5,sK6)
    & r1_orders_2(sK1,sK3,sK4)
    & sK4 = sK6
    & sK3 = sK5
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_yellow_6(sK2,sK0,sK1)
    & v2_yellow_6(sK2,sK0,sK1)
    & ~ v2_struct_0(sK2)
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f3882,f3978,f3977,f3976,f3975,f3974,f3973,f3972])).

fof(f3972,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_orders_2(X2,X5,X6)
                                & r1_orders_2(X1,X3,X4)
                                & X4 = X6
                                & X3 = X5
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_yellow_6(X2,X0,X1)
                & v2_yellow_6(X2,X0,X1)
                & ~ v2_struct_0(X2) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X2,X5,X6)
                              & r1_orders_2(X1,X3,X4)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,sK0,X1)
              & v2_yellow_6(X2,sK0,X1)
              & ~ v2_struct_0(X2) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3973,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_orders_2(X2,X5,X6)
                            & r1_orders_2(X1,X3,X4)
                            & X4 = X6
                            & X3 = X5
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_yellow_6(X2,sK0,X1)
            & v2_yellow_6(X2,sK0,X1)
            & ~ v2_struct_0(X2) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_orders_2(X2,X5,X6)
                          & r1_orders_2(sK1,X3,X4)
                          & X4 = X6
                          & X3 = X5
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & m1_yellow_6(X2,sK0,sK1)
          & v2_yellow_6(X2,sK0,sK1)
          & ~ v2_struct_0(X2) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3974,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_orders_2(X2,X5,X6)
                        & r1_orders_2(sK1,X3,X4)
                        & X4 = X6
                        & X3 = X5
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X2)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_yellow_6(X2,sK0,sK1)
        & v2_yellow_6(X2,sK0,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_orders_2(sK2,X5,X6)
                      & r1_orders_2(sK1,X3,X4)
                      & X4 = X6
                      & X3 = X5
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & m1_subset_1(X5,u1_struct_0(sK2)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_yellow_6(sK2,sK0,sK1)
      & v2_yellow_6(sK2,sK0,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3975,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_orders_2(sK2,X5,X6)
                    & r1_orders_2(sK1,X3,X4)
                    & X4 = X6
                    & X3 = X5
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & m1_subset_1(X5,u1_struct_0(sK2)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_orders_2(sK2,X5,X6)
                  & r1_orders_2(sK1,sK3,X4)
                  & X4 = X6
                  & sK3 = X5
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & m1_subset_1(X5,u1_struct_0(sK2)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f3976,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_orders_2(sK2,X5,X6)
                & r1_orders_2(sK1,sK3,X4)
                & X4 = X6
                & sK3 = X5
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & m1_subset_1(X5,u1_struct_0(sK2)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_orders_2(sK2,X5,X6)
              & r1_orders_2(sK1,sK3,sK4)
              & sK4 = X6
              & sK3 = X5
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & m1_subset_1(X5,u1_struct_0(sK2)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f3977,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_orders_2(sK2,X5,X6)
            & r1_orders_2(sK1,sK3,sK4)
            & sK4 = X6
            & sK3 = X5
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & m1_subset_1(X5,u1_struct_0(sK2)) )
   => ( ? [X6] :
          ( ~ r1_orders_2(sK2,sK5,X6)
          & r1_orders_2(sK1,sK3,sK4)
          & sK4 = X6
          & sK3 = sK5
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f3978,plain,
    ( ? [X6] :
        ( ~ r1_orders_2(sK2,sK5,X6)
        & r1_orders_2(sK1,sK3,sK4)
        & sK4 = X6
        & sK3 = sK5
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ~ r1_orders_2(sK2,sK5,sK6)
      & r1_orders_2(sK1,sK3,sK4)
      & sK4 = sK6
      & sK3 = sK5
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f3882,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X2,X5,X6)
                              & r1_orders_2(X1,X3,X4)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1)
              & v2_yellow_6(X2,X0,X1)
              & ~ v2_struct_0(X2) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f3881])).

fof(f3881,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X2,X5,X6)
                              & r1_orders_2(X1,X3,X4)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1)
              & v2_yellow_6(X2,X0,X1)
              & ~ v2_struct_0(X2) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3869])).

fof(f3869,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_yellow_6(X2,X0,X1)
                  & v2_yellow_6(X2,X0,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_orders_2(X1,X3,X4)
                                    & X4 = X6
                                    & X3 = X5 )
                                 => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3868])).

fof(f3868,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
                & v2_yellow_6(X2,X0,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_orders_2(X1,X3,X4)
                                  & X4 = X6
                                  & X3 = X5 )
                               => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow_6)).

fof(f8647,plain,(
    ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f8646,f4045])).

fof(f4045,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f3979])).

fof(f8646,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f8645,f4049])).

fof(f4049,plain,(
    ~ r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f3979])).

fof(f8645,plain,
    ( r1_orders_2(sK2,sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f8634,f4514])).

fof(f4514,plain,(
    r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(global_subsumption,[],[f4214,f4391,f4511])).

fof(f4511,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f4044,f4141])).

fof(f4141,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f4023])).

fof(f4023,plain,(
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
    inference(nnf_transformation,[],[f3967])).

fof(f3967,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f4391,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f4382,f4071])).

fof(f4071,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3908])).

fof(f3908,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1895])).

fof(f1895,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f4382,plain,(
    l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f4362,f4243])).

fof(f4243,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f4241,f4036])).

fof(f4036,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3979])).

fof(f4241,plain,
    ( l1_orders_2(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f4038,f4064])).

fof(f4064,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3900])).

fof(f3900,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3197])).

fof(f3197,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f4038,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3979])).

fof(f4362,plain,
    ( l1_orders_2(sK2)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f4324,f4104])).

fof(f4104,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3934])).

fof(f3934,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2992])).

fof(f2992,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f4324,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(global_subsumption,[],[f4041,f4323])).

fof(f4323,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ m1_yellow_6(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f4322,f4036])).

fof(f4322,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ m1_yellow_6(sK2,sK0,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4318,f4038])).

fof(f4318,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ m1_yellow_6(sK2,sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f4040,f4061])).

fof(f4061,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X1)
      | ~ v2_yellow_6(X2,X0,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3985])).

fof(f3985,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_yellow_6(X2,X0,X1)
                  | ~ m1_yellow_0(X2,X1)
                  | ~ v4_yellow_0(X2,X1) )
                & ( ( m1_yellow_0(X2,X1)
                    & v4_yellow_0(X2,X1) )
                  | ~ v2_yellow_6(X2,X0,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f3984])).

fof(f3984,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_yellow_6(X2,X0,X1)
                  | ~ m1_yellow_0(X2,X1)
                  | ~ v4_yellow_0(X2,X1) )
                & ( ( m1_yellow_0(X2,X1)
                    & v4_yellow_0(X2,X1) )
                  | ~ v2_yellow_6(X2,X0,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3898])).

fof(f3898,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3804])).

fof(f3804,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_6)).

fof(f4040,plain,(
    v2_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f3979])).

fof(f4041,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f3979])).

fof(f4214,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_struct_0(sK2) ),
    inference(resolution,[],[f4039,f4069])).

fof(f4069,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3906])).

fof(f3906,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3905])).

fof(f3905,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f4039,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3979])).

fof(f8634,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[],[f8583,f4158])).

fof(f4158,plain,(
    r1_orders_2(sK1,sK5,sK6) ),
    inference(definition_unfolding,[],[f4048,f4046,f4047])).

fof(f4047,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f3979])).

fof(f4046,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f3979])).

fof(f4048,plain,(
    r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f3979])).

fof(f8583,plain,(
    ! [X12,X11] :
      ( ~ r1_orders_2(sK1,X11,X12)
      | ~ r2_hidden(X11,u1_struct_0(sK2))
      | r1_orders_2(sK2,X11,X12)
      | ~ m1_subset_1(X12,u1_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f8582,f4380])).

fof(f4380,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4379,f4037])).

fof(f4037,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3979])).

fof(f4379,plain,(
    ! [X1] :
      ( m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4378,f4243])).

fof(f4378,plain,(
    ! [X1] :
      ( m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4359,f4039])).

fof(f4359,plain,(
    ! [X1] :
      ( m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | v2_struct_0(sK2)
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f4324,f4100])).

fof(f4100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3929])).

fof(f3929,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3928])).

fof(f3928,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3056])).

fof(f3056,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_yellow_0)).

fof(f8582,plain,(
    ! [X12,X11] :
      ( r1_orders_2(sK2,X11,X12)
      | ~ r2_hidden(X11,u1_struct_0(sK2))
      | ~ r1_orders_2(sK1,X11,X12)
      | ~ m1_subset_1(X12,u1_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4357,f4380])).

fof(f4357,plain,(
    ! [X12,X11] :
      ( r1_orders_2(sK2,X11,X12)
      | ~ r2_hidden(X11,u1_struct_0(sK2))
      | ~ r1_orders_2(sK1,X11,X12)
      | ~ m1_subset_1(X12,u1_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(sK2))
      | ~ m1_subset_1(X12,u1_struct_0(sK1))
      | ~ m1_subset_1(X11,u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f4324,f4356])).

fof(f4356,plain,(
    ! [X12,X11] :
      ( r1_orders_2(sK2,X11,X12)
      | ~ r2_hidden(X11,u1_struct_0(sK2))
      | ~ r1_orders_2(sK1,X11,X12)
      | ~ m1_subset_1(X12,u1_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(sK2))
      | ~ m1_subset_1(X12,u1_struct_0(sK1))
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | ~ m1_yellow_0(sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f4337,f4243])).

fof(f4337,plain,(
    ! [X12,X11] :
      ( r1_orders_2(sK2,X11,X12)
      | ~ r2_hidden(X11,u1_struct_0(sK2))
      | ~ r1_orders_2(sK1,X11,X12)
      | ~ m1_subset_1(X12,u1_struct_0(sK2))
      | ~ m1_subset_1(X11,u1_struct_0(sK2))
      | ~ m1_subset_1(X12,u1_struct_0(sK1))
      | ~ m1_subset_1(X11,u1_struct_0(sK1))
      | ~ m1_yellow_0(sK2,sK1)
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f4321,f4172])).

fof(f4172,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f4171])).

fof(f4171,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f4126])).

fof(f4126,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3954])).

fof(f3954,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3953])).

fof(f3953,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3059])).

fof(f3059,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r2_hidden(X4,u1_struct_0(X1))
                              & r1_orders_2(X0,X2,X3)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_yellow_0)).

fof(f4321,plain,(
    v4_yellow_0(sK2,sK1) ),
    inference(global_subsumption,[],[f4041,f4320])).

fof(f4320,plain,
    ( v4_yellow_0(sK2,sK1)
    | ~ m1_yellow_6(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f4319,f4036])).

fof(f4319,plain,
    ( v4_yellow_0(sK2,sK1)
    | ~ m1_yellow_6(sK2,sK0,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4317,f4038])).

fof(f4317,plain,
    ( v4_yellow_0(sK2,sK1)
    | ~ m1_yellow_6(sK2,sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f4040,f4060])).

fof(f4060,plain,(
    ! [X2,X0,X1] :
      ( v4_yellow_0(X2,X1)
      | ~ v2_yellow_6(X2,X0,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3985])).
%------------------------------------------------------------------------------
