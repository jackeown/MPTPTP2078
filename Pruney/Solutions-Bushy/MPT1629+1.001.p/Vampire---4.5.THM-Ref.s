%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1629+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 520 expanded)
%              Number of leaves         :   12 ( 119 expanded)
%              Depth                    :   12
%              Number of atoms          :  323 (2595 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f79,f93,f142,f170,f253])).

fof(f253,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f24,f27,f26,f25,f74,f171,f214,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f214,plain,
    ( ! [X0] : ~ r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2))),k6_subset_1(X0,sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f213,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f44,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f213,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2))),sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f24,f26,f27,f25,f71,f173,f177,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X1,sK5(X0,X1,X2),X4)
      | r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | ~ r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f177,plain,
    ( r1_orders_2(sK1,sK5(sK0,sK1,sK2),sK4(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f24,f25,f74,f171,f88])).

fof(f88,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_waybel_0(sK0,X3,X5)
        | v2_struct_0(X3)
        | r1_orders_2(X3,X4,sK4(sK0,X3,X5,X4))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f87])).

% (8081)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f87,plain,
    ( spl8_3
  <=> ! [X3,X5,X4] :
        ( v2_struct_0(X3)
        | ~ r2_waybel_0(sK0,X3,X5)
        | r1_orders_2(X3,X4,sK4(sK0,X3,X5,X4))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f173,plain,
    ( m1_subset_1(sK4(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f27,f26,f74,f25,f24,f171,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_1
  <=> r1_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f171,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f27,f26,f24,f25,f71,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | ~ r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,
    ( r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl8_2
  <=> r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f25,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <~> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <~> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r1_waybel_0(X0,X1,X2)
              <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f170,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f24,f26,f27,f25,f75,f80,f106,f81,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X1,sK3(X0,X1,X2),X4)
      | ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,
    ( r1_orders_2(sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2)),sK6(sK0,sK1,sK2,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))))
    | spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f27,f26,f24,f77,f25,f70,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f77,plain,
    ( m1_subset_1(sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2)),u1_struct_0(sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f27,f26,f24,f25,f75,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f106,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2)))),k6_subset_1(u1_struct_0(sK0),sK2))
    | spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f82,f104,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k6_subset_1(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f45,f33])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f104,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2)))),u1_struct_0(sK0))
    | spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f57,f94,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f94,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2)))),u1_struct_0(sK0))
    | spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f26,f27,f25,f24,f80,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).

fof(f57,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f26,f27,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f82,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2)))),sK2)
    | spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f27,f26,f24,f77,f25,f70,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK6(X0,X1,X2,X3)),X2)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))),u1_struct_0(sK1))
    | spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f27,f26,f24,f77,f25,f70,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f75,plain,
    ( ~ r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f142,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f26,f92])).

fof(f92,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f93,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f59,f90,f87])).

fof(f59,plain,(
    ! [X4,X5,X3] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | r1_orders_2(X3,X4,sK4(sK0,X3,X5,X4))
      | ~ r2_waybel_0(sK0,X3,X5) ) ),
    inference(resolution,[],[f27,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_orders_2(X1,X3,sK4(X0,X1,X2,X3))
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f23,f73,f69])).

fof(f23,plain,
    ( r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
    | ~ r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f22,f73,f69])).

fof(f22,plain,
    ( ~ r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
    | r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
