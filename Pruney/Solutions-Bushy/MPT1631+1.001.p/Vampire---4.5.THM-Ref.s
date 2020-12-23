%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1631+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 868 expanded)
%              Number of leaves         :   18 ( 334 expanded)
%              Depth                    :   28
%              Number of atoms          :  869 (10059 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f79,f86,f114,f140,f143,f152,f166])).

fof(f166,plain,
    ( spl8_1
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl8_1
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f164,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ( ! [X3] :
            ( ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK2),k2_waybel_0(sK0,sK1,sK3(X3)))
              & r1_orders_2(sK1,X3,sK3(X3))
              & m1_subset_1(sK3(X3),u1_struct_0(sK1)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_subset_1(sK2,u1_struct_0(sK1)) )
      | ~ v10_waybel_0(sK1,sK0) )
    & ( ! [X5] :
          ( ( ! [X7] :
                ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X5),k2_waybel_0(sK0,sK1,X7))
                | ~ r1_orders_2(sK1,sK4(X5),X7)
                | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
            & m1_subset_1(sK4(X5),u1_struct_0(sK1)) )
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
      | v10_waybel_0(sK1,sK0) )
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f18,f17,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                          & r1_orders_2(X1,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  & m1_subset_1(X2,u1_struct_0(X1)) )
              | ~ v10_waybel_0(X1,X0) )
            & ( ! [X5] :
                  ( ? [X6] :
                      ( ! [X7] :
                          ( r1_orders_2(X0,k2_waybel_0(X0,X1,X5),k2_waybel_0(X0,X1,X7))
                          | ~ r1_orders_2(X1,X6,X7)
                          | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                      & m1_subset_1(X6,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | v10_waybel_0(X1,X0) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,X1,X2),k2_waybel_0(sK0,X1,X4))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v10_waybel_0(X1,sK0) )
          & ( ! [X5] :
                ( ? [X6] :
                    ( ! [X7] :
                        ( r1_orders_2(sK0,k2_waybel_0(sK0,X1,X5),k2_waybel_0(sK0,X1,X7))
                        | ~ r1_orders_2(X1,X6,X7)
                        | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | v10_waybel_0(X1,sK0) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,X1,X2),k2_waybel_0(sK0,X1,X4))
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ v10_waybel_0(X1,sK0) )
        & ( ! [X5] :
              ( ? [X6] :
                  ( ! [X7] :
                      ( r1_orders_2(sK0,k2_waybel_0(sK0,X1,X5),k2_waybel_0(sK0,X1,X7))
                      | ~ r1_orders_2(X1,X6,X7)
                      | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          | v10_waybel_0(X1,sK0) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X2),k2_waybel_0(sK0,sK1,X4))
                    & r1_orders_2(sK1,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        | ~ v10_waybel_0(sK1,sK0) )
      & ( ! [X5] :
            ( ? [X6] :
                ( ! [X7] :
                    ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X5),k2_waybel_0(sK0,sK1,X7))
                    | ~ r1_orders_2(sK1,X6,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
                & m1_subset_1(X6,u1_struct_0(sK1)) )
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        | v10_waybel_0(sK1,sK0) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X2),k2_waybel_0(sK0,sK1,X4))
                & r1_orders_2(sK1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ! [X3] :
          ( ? [X4] :
              ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK2),k2_waybel_0(sK0,sK1,X4))
              & r1_orders_2(sK1,X3,X4)
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X3] :
      ( ? [X4] :
          ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK2),k2_waybel_0(sK0,sK1,X4))
          & r1_orders_2(sK1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(sK1)) )
     => ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK2),k2_waybel_0(sK0,sK1,sK3(X3)))
        & r1_orders_2(sK1,X3,sK3(X3))
        & m1_subset_1(sK3(X3),u1_struct_0(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5] :
      ( ? [X6] :
          ( ! [X7] :
              ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X5),k2_waybel_0(sK0,sK1,X7))
              | ~ r1_orders_2(sK1,X6,X7)
              | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
          & m1_subset_1(X6,u1_struct_0(sK1)) )
     => ( ! [X7] :
            ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X5),k2_waybel_0(sK0,sK1,X7))
            | ~ r1_orders_2(sK1,sK4(X5),X7)
            | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
        & m1_subset_1(sK4(X5),u1_struct_0(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v10_waybel_0(X1,X0) )
          & ( ! [X5] :
                ( ? [X6] :
                    ( ! [X7] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X5),k2_waybel_0(X0,X1,X7))
                        | ~ r1_orders_2(X1,X6,X7)
                        | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | v10_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v10_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) )
            | v10_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v10_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) )
            | v10_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v10_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v10_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v10_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X1))
                 => ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => ( r1_orders_2(X1,X3,X4)
                           => r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4)) ) )
                      & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v10_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( r1_orders_2(X1,X3,X4)
                         => r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4)) ) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_0)).

fof(f164,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f163,f30])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f163,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f162,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f162,plain,
    ( v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f161,f32])).

fof(f32,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f161,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f159,f50])).

fof(f50,plain,
    ( ~ v10_waybel_0(sK1,sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl8_1
  <=> v10_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f159,plain,
    ( v10_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f131,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,sK5(X0,X1)))
      | v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v10_waybel_0(X1,X0)
              | ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,sK5(X0,X1)))
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) )
            & ( ! [X3] :
                  ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ v10_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,sK5(X0,X1)))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v10_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X1)) ) )
            & ( ! [X3] :
                  ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ v10_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v10_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X1)) ) )
            & ( ! [X2] :
                  ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
                  | ~ m1_subset_1(X2,u1_struct_0(X1)) )
              | ~ v10_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v10_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v10_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v10_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_waybel_0)).

fof(f131,plain,
    ( r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_5
  <=> r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f152,plain,
    ( ~ spl8_4
    | spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl8_4
    | spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(subsumption_resolution,[],[f150,f29])).

fof(f150,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_4
    | spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(subsumption_resolution,[],[f149,f30])).

fof(f149,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(subsumption_resolution,[],[f148,f31])).

fof(f148,plain,
    ( v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(subsumption_resolution,[],[f147,f32])).

fof(f147,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(subsumption_resolution,[],[f146,f77])).

fof(f77,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl8_4
  <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f146,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(subsumption_resolution,[],[f145,f134])).

fof(f134,plain,
    ( m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl8_6
  <=> m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f145,plain,
    ( ~ m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_5
    | spl8_7 ),
    inference(subsumption_resolution,[],[f144,f130])).

fof(f130,plain,
    ( ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f144,plain,
    ( r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | ~ m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_7 ),
    inference(resolution,[],[f139,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,sK6(X0,X1,X2,X3)))
                & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
                & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X6))
                | ~ r1_orders_2(X1,sK7(X0,X1,X2),X6)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f25,f27,f26])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,sK6(X0,X1,X2,X3)))
        & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X6))
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X6))
            | ~ r1_orders_2(X1,sK7(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X6))
                  | ~ r1_orders_2(X1,X5,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

% (6883)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4))
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_orders_2(X1,X3,X4)
                 => r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X4)) ) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_waybel_0__e1_34_1__waybel_0)).

fof(f139,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1))),u1_struct_0(sK1))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl8_7
  <=> m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f143,plain,
    ( spl8_1
    | ~ spl8_4
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl8_1
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f141,f77])).

fof(f141,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
    | spl8_1
    | spl8_6 ),
    inference(resolution,[],[f135,f115])).

fof(f115,plain,
    ( ! [X5] :
        ( m1_subset_1(sK4(X5),u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f33,f50])).

fof(f33,plain,(
    ! [X5] :
      ( m1_subset_1(sK4(X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f135,plain,
    ( ~ m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f140,plain,
    ( spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f127,f76,f73,f137,f133,f129])).

fof(f73,plain,
    ( spl8_3
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK4(sK5(sK0,sK1)),sK6(sK0,sK1,sK5(sK0,sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f127,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f126,f29])).

fof(f126,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f125,f30])).

fof(f125,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f124,f31])).

fof(f124,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f123,f32])).

fof(f123,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f122,f77])).

fof(f122,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | ~ m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3 ),
    inference(resolution,[],[f74,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK1,sK4(sK5(sK0,sK1)),sK6(sK0,sK1,sK5(sK0,sK1),X0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f114,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f112,f54])).

fof(f54,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl8_2
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f112,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f111,f91])).

fof(f91,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f90,f29])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
        | v2_struct_0(sK0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f89,f30])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f88,f31])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
        | v2_struct_0(sK1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f87,f32])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X0))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f49,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ v10_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X3))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,
    ( v10_waybel_0(sK1,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f111,plain,
    ( ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f110,f29])).

fof(f110,plain,
    ( ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f109,f30])).

fof(f109,plain,
    ( ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f108,f31])).

fof(f108,plain,
    ( ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f107,f32])).

fof(f107,plain,
    ( ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f106,f54])).

fof(f106,plain,
    ( ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f105,f42])).

% (6881)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f105,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f103,f94])).

fof(f94,plain,
    ( ! [X3] :
        ( r1_orders_2(sK1,X3,sK3(X3))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f37,f49])).

fof(f37,plain,(
    ! [X3] :
      ( r1_orders_2(sK1,X3,sK3(X3))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v10_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK3(X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f102,f93])).

fof(f93,plain,
    ( ! [X3] :
        ( m1_subset_1(sK3(X3),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f36,f49])).

fof(f36,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v10_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK3(X0))
        | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f99,f54])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK3(X0))
        | ~ m1_subset_1(sK3(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f98,f95])).

fof(f95,plain,
    ( ! [X3] :
        ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK2),k2_waybel_0(sK0,sK1,sK3(X3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f38,f49])).

fof(f38,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK2),k2_waybel_0(sK0,sK1,sK3(X3)))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v10_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X1),k2_waybel_0(sK0,sK1,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK7(sK0,sK1,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f97,f91])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,sK7(sK0,sK1,X1),X0)
      | r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X1),k2_waybel_0(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f96,f31])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,sK7(sK0,sK1,X1),X0)
      | v2_struct_0(sK1)
      | r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X1),k2_waybel_0(sK0,sK1,X0)) ) ),
    inference(resolution,[],[f71,f32])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_waybel_0(sK0,X0,a_3_0_waybel_0(sK0,X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK7(sK0,X0,X1),X2)
      | v2_struct_0(X0)
      | r1_orders_2(sK0,k2_waybel_0(sK0,X0,X1),k2_waybel_0(sK0,X0,X2)) ) ),
    inference(subsumption_resolution,[],[f70,f29])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK7(sK0,X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_waybel_0(sK0,X0,a_3_0_waybel_0(sK0,X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | r1_orders_2(sK0,k2_waybel_0(sK0,X0,X1),k2_waybel_0(sK0,X0,X2))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f43,f30])).

fof(f43,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X1,sK7(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,X6))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,
    ( spl8_1
    | spl8_4 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl8_1
    | spl8_4 ),
    inference(subsumption_resolution,[],[f84,f29])).

fof(f84,plain,
    ( v2_struct_0(sK0)
    | spl8_1
    | spl8_4 ),
    inference(subsumption_resolution,[],[f83,f30])).

fof(f83,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_4 ),
    inference(subsumption_resolution,[],[f82,f31])).

fof(f82,plain,
    ( v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_4 ),
    inference(subsumption_resolution,[],[f81,f32])).

fof(f81,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | spl8_4 ),
    inference(subsumption_resolution,[],[f80,f50])).

fof(f80,plain,
    ( v10_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_4 ),
    inference(resolution,[],[f78,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X1))
      | v10_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f79,plain,
    ( spl8_3
    | ~ spl8_4
    | spl8_1 ),
    inference(avatar_split_clause,[],[f69,f48,f76,f73])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK4(sK5(sK0,sK1)),sK6(sK0,sK1,sK5(sK0,sK1),X0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),X0),u1_struct_0(sK1)) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f68,f29])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK4(sK5(sK0,sK1)),sK6(sK0,sK1,sK5(sK0,sK1),X0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),X0),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f67,f30])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK4(sK5(sK0,sK1)),sK6(sK0,sK1,sK5(sK0,sK1),X0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),X0),u1_struct_0(sK1))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f66,f31])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK4(sK5(sK0,sK1)),sK6(sK0,sK1,sK5(sK0,sK1),X0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),X0),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f65,f32])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK4(sK5(sK0,sK1)),sK6(sK0,sK1,sK5(sK0,sK1),X0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),X0),u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f64,f50])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK4(sK5(sK0,sK1)),sK6(sK0,sK1,sK5(sK0,sK1),X0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),X0),u1_struct_0(sK1))
        | v10_waybel_0(sK1,sK0)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl8_1 ),
    inference(resolution,[],[f63,f41])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK4(X1),sK6(sK0,sK1,X1,X0))
        | ~ m1_subset_1(sK6(sK0,sK1,X1,X0),u1_struct_0(sK1)) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f62,f31])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X1))
        | ~ r1_orders_2(sK1,sK4(X1),sK6(sK0,sK1,X1,X0))
        | ~ m1_subset_1(sK6(sK0,sK1,X1,X0),u1_struct_0(sK1)) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f61,f32])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X1))
        | ~ r1_orders_2(sK1,sK4(X1),sK6(sK0,sK1,X1,X0))
        | ~ m1_subset_1(sK6(sK0,sK1,X1,X0),u1_struct_0(sK1)) )
    | spl8_1 ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | r1_waybel_0(sK0,sK1,a_3_0_waybel_0(sK0,sK1,X1))
        | ~ r1_orders_2(sK1,sK4(X1),sK6(sK0,sK1,X1,X0))
        | ~ m1_subset_1(sK6(sK0,sK1,X1,X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | spl8_1 ),
    inference(resolution,[],[f59,f57])).

fof(f57,plain,
    ( ! [X7,X5] :
        ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X5),k2_waybel_0(sK0,sK1,X7))
        | ~ r1_orders_2(sK1,sK4(X5),X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f34,f50])).

fof(f34,plain,(
    ! [X7,X5] :
      ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X5),k2_waybel_0(sK0,sK1,X7))
      | ~ r1_orders_2(sK1,sK4(X5),X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | v10_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,X0,X1),k2_waybel_0(sK0,X0,sK6(sK0,X0,X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,a_3_0_waybel_0(sK0,X0,X1)) ) ),
    inference(subsumption_resolution,[],[f58,f29])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,X0,X1),k2_waybel_0(sK0,X0,sK6(sK0,X0,X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,a_3_0_waybel_0(sK0,X0,X1))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f46,f30])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X2),k2_waybel_0(X0,X1,sK6(X0,X1,X2,X3)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r1_waybel_0(X0,X1,a_3_0_waybel_0(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f35,f52,f48])).

fof(f35,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v10_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
