%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1632+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 (1544 expanded)
%              Number of leaves         :   18 ( 630 expanded)
%              Depth                    :   15
%              Number of atoms          :  532 (18834 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f67,f71,f75,f106,f234])).

fof(f234,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f232,f148])).

fof(f148,plain,
    ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK3(sK7(sK0,sK1,sK2))),k2_waybel_0(sK0,sK1,sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f122,f53])).

fof(f53,plain,
    ( ! [X3] :
        ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK3(X3)),k2_waybel_0(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl8_2
  <=> ! [X3] :
        ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK3(X3)),k2_waybel_0(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f122,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f29,f30,f31,f32,f66,f108,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,sK6(X0,X1,X2,X3)),k2_waybel_0(X0,X1,X2))
                & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
                & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
                | ~ r1_orders_2(X1,sK7(X0,X1,X2),X6)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f25,f27,f26])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,sK6(X0,X1,X2,X3)),k2_waybel_0(X0,X1,X2))
        & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
            | ~ r1_orders_2(X1,sK7(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
                  | ~ r1_orders_2(X1,X5,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
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
     => ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_orders_2(X1,X3,X4)
                 => r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2)) ) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_waybel_0__e1_35_1__waybel_0)).

fof(f108,plain,
    ( r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK2))
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f29,f30,f31,f32,f49,f66,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v11_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v11_waybel_0(X1,X0)
              | ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,sK5(X0,X1)))
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) )
            & ( ! [X3] :
                  ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ v11_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,sK5(X0,X1)))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v11_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X1)) ) )
            & ( ! [X3] :
                  ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ v11_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v11_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X1)) ) )
            & ( ! [X2] :
                  ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                  | ~ m1_subset_1(X2,u1_struct_0(X1)) )
              | ~ v11_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
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
         => ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_waybel_0)).

fof(f49,plain,
    ( v11_waybel_0(sK1,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl8_1
  <=> v11_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f66,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl8_5
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f32,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ( ! [X3] :
            ( ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK3(X3)),k2_waybel_0(sK0,sK1,sK2))
              & r1_orders_2(sK1,X3,sK3(X3))
              & m1_subset_1(sK3(X3),u1_struct_0(sK1)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_subset_1(sK2,u1_struct_0(sK1)) )
      | ~ v11_waybel_0(sK1,sK0) )
    & ( ! [X5] :
          ( ( ! [X7] :
                ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
                | ~ r1_orders_2(sK1,sK4(X5),X7)
                | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
            & m1_subset_1(sK4(X5),u1_struct_0(sK1)) )
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
      | v11_waybel_0(sK1,sK0) )
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
                          ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                          & r1_orders_2(X1,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  & m1_subset_1(X2,u1_struct_0(X1)) )
              | ~ v11_waybel_0(X1,X0) )
            & ( ! [X5] :
                  ( ? [X6] :
                      ( ! [X7] :
                          ( r1_orders_2(X0,k2_waybel_0(X0,X1,X7),k2_waybel_0(X0,X1,X5))
                          | ~ r1_orders_2(X1,X6,X7)
                          | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                      & m1_subset_1(X6,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | v11_waybel_0(X1,X0) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,X1,X4),k2_waybel_0(sK0,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,sK0) )
          & ( ! [X5] :
                ( ? [X6] :
                    ( ! [X7] :
                        ( r1_orders_2(sK0,k2_waybel_0(sK0,X1,X7),k2_waybel_0(sK0,X1,X5))
                        | ~ r1_orders_2(X1,X6,X7)
                        | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | v11_waybel_0(X1,sK0) )
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
                      ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,X1,X4),k2_waybel_0(sK0,X1,X2))
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ v11_waybel_0(X1,sK0) )
        & ( ! [X5] :
              ( ? [X6] :
                  ( ! [X7] :
                      ( r1_orders_2(sK0,k2_waybel_0(sK0,X1,X7),k2_waybel_0(sK0,X1,X5))
                      | ~ r1_orders_2(X1,X6,X7)
                      | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          | v11_waybel_0(X1,sK0) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,X2))
                    & r1_orders_2(sK1,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        | ~ v11_waybel_0(sK1,sK0) )
      & ( ! [X5] :
            ( ? [X6] :
                ( ! [X7] :
                    ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
                    | ~ r1_orders_2(sK1,X6,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
                & m1_subset_1(X6,u1_struct_0(sK1)) )
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        | v11_waybel_0(sK1,sK0) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,X2))
                & r1_orders_2(sK1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ! [X3] :
          ( ? [X4] :
              ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,sK2))
              & r1_orders_2(sK1,X3,X4)
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X3] :
      ( ? [X4] :
          ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,sK2))
          & r1_orders_2(sK1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(sK1)) )
     => ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK3(X3)),k2_waybel_0(sK0,sK1,sK2))
        & r1_orders_2(sK1,X3,sK3(X3))
        & m1_subset_1(sK3(X3),u1_struct_0(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5] :
      ( ? [X6] :
          ( ! [X7] :
              ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
              | ~ r1_orders_2(sK1,X6,X7)
              | ~ m1_subset_1(X7,u1_struct_0(sK1)) )
          & m1_subset_1(X6,u1_struct_0(sK1)) )
     => ( ! [X7] :
            ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
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
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,X0) )
          & ( ! [X5] :
                ( ? [X6] :
                    ( ! [X7] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X7),k2_waybel_0(X0,X1,X5))
                        | ~ r1_orders_2(X1,X6,X7)
                        | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | v11_waybel_0(X1,X0) )
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
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) )
            | v11_waybel_0(X1,X0) )
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
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) )
            | v11_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v11_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
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
          ( ( v11_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
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
           => ( v11_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X1))
                 => ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => ( r1_orders_2(X1,X3,X4)
                           => r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2)) ) )
                      & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( r1_orders_2(X1,X3,X4)
                         => r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2)) ) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_0)).

fof(f31,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f232,plain,
    ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK3(sK7(sK0,sK1,sK2))),k2_waybel_0(sK0,sK1,sK2))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f29,f30,f31,f32,f66,f108,f149,f150,f43])).

fof(f43,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
      | ~ r1_orders_2(X1,sK7(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f150,plain,
    ( r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK3(sK7(sK0,sK1,sK2)))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f122,f57])).

fof(f57,plain,
    ( ! [X3] :
        ( r1_orders_2(sK1,X3,sK3(X3))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl8_3
  <=> ! [X3] :
        ( r1_orders_2(sK1,X3,sK3(X3))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f149,plain,
    ( m1_subset_1(sK3(sK7(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f122,f61])).

fof(f61,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK1))
        | m1_subset_1(sK3(X3),u1_struct_0(sK1)) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl8_4
  <=> ! [X3] :
        ( m1_subset_1(sK3(X3),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f106,plain,
    ( spl8_1
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f104,f86])).

fof(f86,plain,
    ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1)))),k2_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | spl8_1
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f29,f30,f31,f32,f76,f77,f78,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | ~ r1_orders_2(X0,k2_waybel_0(X0,X1,sK6(X0,X1,X2,X3)),k2_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,
    ( m1_subset_1(sK4(sK5(sK0,sK1)),u1_struct_0(sK1))
    | spl8_1
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f76,f74])).

fof(f74,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK1))
        | m1_subset_1(sK4(X5),u1_struct_0(sK1)) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl8_7
  <=> ! [X5] :
        ( m1_subset_1(sK4(X5),u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f77,plain,
    ( ~ r1_waybel_0(sK0,sK1,a_3_1_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f29,f30,f31,f32,f50,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v11_waybel_0(X1,X0)
      | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,sK5(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,
    ( ~ v11_waybel_0(sK1,sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f76,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f29,f30,f31,f32,f50,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v11_waybel_0(X1,X0)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f104,plain,
    ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1)))),k2_waybel_0(sK0,sK1,sK5(sK0,sK1)))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f76,f84,f85,f70])).

fof(f70,plain,
    ( ! [X7,X5] :
        ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ m1_subset_1(X7,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK4(X5),X7) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_6
  <=> ! [X5,X7] :
        ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ m1_subset_1(X7,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK4(X5),X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f85,plain,
    ( r1_orders_2(sK1,sK4(sK5(sK0,sK1)),sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1))))
    | spl8_1
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f29,f30,f31,f32,f76,f77,f78,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK5(sK0,sK1),sK4(sK5(sK0,sK1))),u1_struct_0(sK1))
    | spl8_1
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f29,f30,f31,f32,f76,f77,f78,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,
    ( spl8_1
    | spl8_7 ),
    inference(avatar_split_clause,[],[f33,f73,f48])).

fof(f33,plain,(
    ! [X5] :
      ( m1_subset_1(sK4(X5),u1_struct_0(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,
    ( spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f34,f69,f48])).

fof(f34,plain,(
    ! [X7,X5] :
      ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
      | ~ r1_orders_2(sK1,sK4(X5),X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f35,f64,f48])).

fof(f35,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v11_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f36,f60,f48])).

fof(f36,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f37,f56,f48])).

fof(f37,plain,(
    ! [X3] :
      ( r1_orders_2(sK1,X3,sK3(X3))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f38,f52,f48])).

fof(f38,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,k2_waybel_0(sK0,sK1,sK3(X3)),k2_waybel_0(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v11_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
