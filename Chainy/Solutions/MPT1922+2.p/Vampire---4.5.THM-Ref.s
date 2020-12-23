%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1922+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:38 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 260 expanded)
%              Number of leaves         :   12 ( 148 expanded)
%              Depth                    :    8
%              Number of atoms          :  303 (3149 expanded)
%              Number of equality atoms :   55 ( 703 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6170,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6163,f6161])).

fof(f6161,plain,(
    ~ m1_yellow_0(sK18,sK17) ),
    inference(unit_resulting_resolution,[],[f6140,f6023,f6024,f5021,f5018,f5017,f6025,f6099])).

fof(f6099,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X0,X4,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f6098])).

fof(f6098,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f5479])).

fof(f5479,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X1,X4,X5)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4153])).

fof(f4153,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f4152])).

fof(f4152,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3058])).

fof(f3058,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X4,X5)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_yellow_0)).

fof(f6025,plain,(
    m1_subset_1(sK21,u1_struct_0(sK17)) ),
    inference(definition_unfolding,[],[f5015,f5019])).

fof(f5019,plain,(
    sK19 = sK21 ),
    inference(cnf_transformation,[],[f4507])).

fof(f4507,plain,
    ( ~ r1_orders_2(sK17,sK19,sK20)
    & r1_orders_2(sK18,sK21,sK22)
    & sK20 = sK22
    & sK19 = sK21
    & m1_subset_1(sK22,u1_struct_0(sK18))
    & m1_subset_1(sK21,u1_struct_0(sK18))
    & m1_subset_1(sK20,u1_struct_0(sK17))
    & m1_subset_1(sK19,u1_struct_0(sK17))
    & m1_yellow_6(sK18,sK16,sK17)
    & l1_waybel_0(sK17,sK16)
    & l1_struct_0(sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18,sK19,sK20,sK21,sK22])],[f3886,f4506,f4505,f4504,f4503,f4502,f4501,f4500])).

fof(f4500,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_orders_2(X1,X3,X4)
                                & r1_orders_2(X2,X5,X6)
                                & X4 = X6
                                & X3 = X5
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,sK16,X1) )
          & l1_waybel_0(X1,sK16) )
      & l1_struct_0(sK16) ) ),
    introduced(choice_axiom,[])).

fof(f4501,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_orders_2(X1,X3,X4)
                            & r1_orders_2(X2,X5,X6)
                            & X4 = X6
                            & X3 = X5
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_yellow_6(X2,sK16,X1) )
        & l1_waybel_0(X1,sK16) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_orders_2(sK17,X3,X4)
                          & r1_orders_2(X2,X5,X6)
                          & X4 = X6
                          & X3 = X5
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(sK17)) )
              & m1_subset_1(X3,u1_struct_0(sK17)) )
          & m1_yellow_6(X2,sK16,sK17) )
      & l1_waybel_0(sK17,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f4502,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_orders_2(sK17,X3,X4)
                        & r1_orders_2(X2,X5,X6)
                        & X4 = X6
                        & X3 = X5
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X2)) )
                & m1_subset_1(X4,u1_struct_0(sK17)) )
            & m1_subset_1(X3,u1_struct_0(sK17)) )
        & m1_yellow_6(X2,sK16,sK17) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_orders_2(sK17,X3,X4)
                      & r1_orders_2(sK18,X5,X6)
                      & X4 = X6
                      & X3 = X5
                      & m1_subset_1(X6,u1_struct_0(sK18)) )
                  & m1_subset_1(X5,u1_struct_0(sK18)) )
              & m1_subset_1(X4,u1_struct_0(sK17)) )
          & m1_subset_1(X3,u1_struct_0(sK17)) )
      & m1_yellow_6(sK18,sK16,sK17) ) ),
    introduced(choice_axiom,[])).

fof(f4503,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_orders_2(sK17,X3,X4)
                    & r1_orders_2(sK18,X5,X6)
                    & X4 = X6
                    & X3 = X5
                    & m1_subset_1(X6,u1_struct_0(sK18)) )
                & m1_subset_1(X5,u1_struct_0(sK18)) )
            & m1_subset_1(X4,u1_struct_0(sK17)) )
        & m1_subset_1(X3,u1_struct_0(sK17)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_orders_2(sK17,sK19,X4)
                  & r1_orders_2(sK18,X5,X6)
                  & X4 = X6
                  & sK19 = X5
                  & m1_subset_1(X6,u1_struct_0(sK18)) )
              & m1_subset_1(X5,u1_struct_0(sK18)) )
          & m1_subset_1(X4,u1_struct_0(sK17)) )
      & m1_subset_1(sK19,u1_struct_0(sK17)) ) ),
    introduced(choice_axiom,[])).

fof(f4504,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_orders_2(sK17,sK19,X4)
                & r1_orders_2(sK18,X5,X6)
                & X4 = X6
                & sK19 = X5
                & m1_subset_1(X6,u1_struct_0(sK18)) )
            & m1_subset_1(X5,u1_struct_0(sK18)) )
        & m1_subset_1(X4,u1_struct_0(sK17)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_orders_2(sK17,sK19,sK20)
              & r1_orders_2(sK18,X5,X6)
              & sK20 = X6
              & sK19 = X5
              & m1_subset_1(X6,u1_struct_0(sK18)) )
          & m1_subset_1(X5,u1_struct_0(sK18)) )
      & m1_subset_1(sK20,u1_struct_0(sK17)) ) ),
    introduced(choice_axiom,[])).

fof(f4505,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_orders_2(sK17,sK19,sK20)
            & r1_orders_2(sK18,X5,X6)
            & sK20 = X6
            & sK19 = X5
            & m1_subset_1(X6,u1_struct_0(sK18)) )
        & m1_subset_1(X5,u1_struct_0(sK18)) )
   => ( ? [X6] :
          ( ~ r1_orders_2(sK17,sK19,sK20)
          & r1_orders_2(sK18,sK21,X6)
          & sK20 = X6
          & sK19 = sK21
          & m1_subset_1(X6,u1_struct_0(sK18)) )
      & m1_subset_1(sK21,u1_struct_0(sK18)) ) ),
    introduced(choice_axiom,[])).

fof(f4506,plain,
    ( ? [X6] :
        ( ~ r1_orders_2(sK17,sK19,sK20)
        & r1_orders_2(sK18,sK21,X6)
        & sK20 = X6
        & sK19 = sK21
        & m1_subset_1(X6,u1_struct_0(sK18)) )
   => ( ~ r1_orders_2(sK17,sK19,sK20)
      & r1_orders_2(sK18,sK21,sK22)
      & sK20 = sK22
      & sK19 = sK21
      & m1_subset_1(sK22,u1_struct_0(sK18)) ) ),
    introduced(choice_axiom,[])).

fof(f3886,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f3885])).

fof(f3885,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3867])).

fof(f3867,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_6(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_orders_2(X2,X5,X6)
                                    & X4 = X6
                                    & X3 = X5 )
                                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3866])).

fof(f3866,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_orders_2(X2,X5,X6)
                                  & X4 = X6
                                  & X3 = X5 )
                               => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_6)).

fof(f5015,plain,(
    m1_subset_1(sK19,u1_struct_0(sK17)) ),
    inference(cnf_transformation,[],[f4507])).

fof(f5017,plain,(
    m1_subset_1(sK21,u1_struct_0(sK18)) ),
    inference(cnf_transformation,[],[f4507])).

fof(f5018,plain,(
    m1_subset_1(sK22,u1_struct_0(sK18)) ),
    inference(cnf_transformation,[],[f4507])).

fof(f5021,plain,(
    r1_orders_2(sK18,sK21,sK22) ),
    inference(cnf_transformation,[],[f4507])).

fof(f6024,plain,(
    m1_subset_1(sK22,u1_struct_0(sK17)) ),
    inference(definition_unfolding,[],[f5016,f5020])).

fof(f5020,plain,(
    sK20 = sK22 ),
    inference(cnf_transformation,[],[f4507])).

fof(f5016,plain,(
    m1_subset_1(sK20,u1_struct_0(sK17)) ),
    inference(cnf_transformation,[],[f4507])).

fof(f6023,plain,(
    ~ r1_orders_2(sK17,sK21,sK22) ),
    inference(definition_unfolding,[],[f5022,f5019,f5020])).

fof(f5022,plain,(
    ~ r1_orders_2(sK17,sK19,sK20) ),
    inference(cnf_transformation,[],[f4507])).

fof(f6140,plain,(
    l1_orders_2(sK17) ),
    inference(unit_resulting_resolution,[],[f5012,f5013,f5064])).

fof(f5064,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3907])).

fof(f3907,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f5013,plain,(
    l1_waybel_0(sK17,sK16) ),
    inference(cnf_transformation,[],[f4507])).

fof(f5012,plain,(
    l1_struct_0(sK16) ),
    inference(cnf_transformation,[],[f4507])).

fof(f6163,plain,(
    m1_yellow_0(sK18,sK17) ),
    inference(unit_resulting_resolution,[],[f5012,f5013,f5014,f6145,f5059])).

fof(f5059,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4530])).

fof(f4530,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f4529])).

fof(f4529,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3904])).

fof(f3904,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3803])).

fof(f3803,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).

fof(f6145,plain,(
    l1_waybel_0(sK18,sK16) ),
    inference(unit_resulting_resolution,[],[f5012,f5013,f5014,f5056])).

fof(f5056,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3901])).

fof(f3901,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f3900])).

fof(f3900,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3810])).

fof(f3810,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(f5014,plain,(
    m1_yellow_6(sK18,sK16,sK17) ),
    inference(cnf_transformation,[],[f4507])).
%------------------------------------------------------------------------------
