%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t9_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:03 EDT 2019

% Result     : Theorem 7.77s
% Output     : Refutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 523 expanded)
%              Number of leaves         :   17 ( 125 expanded)
%              Depth                    :   11
%              Number of atoms          :  404 (2615 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30642,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f160,f408,f412,f490,f584,f731,f29533,f30640])).

fof(f30640,plain,
    ( ~ spl12_0
    | ~ spl12_2
    | ~ spl12_14
    | ~ spl12_26 ),
    inference(avatar_contradiction_clause,[],[f30636])).

fof(f30636,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_14
    | ~ spl12_26 ),
    inference(unit_resulting_resolution,[],[f5163,f5638,f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t9_waybel_0.p',d5_xboole_0)).

fof(f5638,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2))),sK2)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_14 ),
    inference(unit_resulting_resolution,[],[f66,f68,f69,f67,f135,f5157,f5162,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X1,sK5(X0,X1,X2),X4)
      | r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | ~ r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/waybel_0__t9_waybel_0.p',d11_waybel_0)).

fof(f5162,plain,
    ( r1_orders_2(sK1,sK5(sK0,sK1,sK2),sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2)))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_14 ),
    inference(unit_resulting_resolution,[],[f66,f67,f144,f4416,f407])).

fof(f407,plain,
    ( ! [X14,X12,X13] :
        ( ~ r2_waybel_0(sK0,X12,X14)
        | v2_struct_0(X12)
        | r1_orders_2(X12,X13,sK4(sK0,X12,X14,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_waybel_0(X12,sK0) )
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl12_14
  <=> ! [X13,X12,X14] :
        ( v2_struct_0(X12)
        | ~ r2_waybel_0(sK0,X12,X14)
        | r1_orders_2(X12,X13,sK4(sK0,X12,X14,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_waybel_0(X12,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f4416,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl12_0 ),
    inference(unit_resulting_resolution,[],[f69,f68,f66,f67,f135,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | ~ r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f144,plain,
    ( r2_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl12_2
  <=> r2_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f5157,plain,
    ( m1_subset_1(sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl12_0
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f69,f68,f144,f67,f66,f4416,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/waybel_0__t9_waybel_0.p',d12_waybel_0)).

fof(f135,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl12_0
  <=> r1_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f67,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <~> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <~> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r1_waybel_0(X0,X1,X2)
              <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t9_waybel_0.p',t9_waybel_0)).

fof(f69,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f5163,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2))),k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_26 ),
    inference(unit_resulting_resolution,[],[f66,f67,f144,f4416,f583])).

fof(f583,plain,
    ( ! [X17,X15,X16] :
        ( ~ r2_waybel_0(sK0,X15,X17)
        | v2_struct_0(X15)
        | r2_hidden(k2_waybel_0(sK0,X15,sK4(sK0,X15,X17,X16)),X17)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ l1_waybel_0(X15,sK0) )
    | ~ spl12_26 ),
    inference(avatar_component_clause,[],[f582])).

fof(f582,plain,
    ( spl12_26
  <=> ! [X16,X15,X17] :
        ( v2_struct_0(X15)
        | ~ r2_waybel_0(sK0,X15,X17)
        | r2_hidden(k2_waybel_0(sK0,X15,sK4(sK0,X15,X17,X16)),X17)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ l1_waybel_0(X15,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).

fof(f29533,plain,
    ( spl12_1
    | spl12_3
    | ~ spl12_20
    | ~ spl12_30 ),
    inference(avatar_contradiction_clause,[],[f29531])).

fof(f29531,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_20
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f112,f24551,f11689,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t9_waybel_0.p',t2_subset)).

fof(f11689,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)))),u1_struct_0(sK0))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_20
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f3827,f1483,f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1483,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)))),k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f66,f67,f141,f255,f256,f730])).

fof(f730,plain,
    ( ! [X10,X11,X9] :
        ( ~ r1_orders_2(X9,sK3(sK0,X9,X11),X10)
        | r2_waybel_0(sK0,X9,X11)
        | ~ r2_hidden(k2_waybel_0(sK0,X9,X10),X11)
        | v2_struct_0(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ l1_waybel_0(X9,sK0) )
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f729])).

fof(f729,plain,
    ( spl12_30
  <=> ! [X9,X11,X10] :
        ( v2_struct_0(X9)
        | r2_waybel_0(sK0,X9,X11)
        | ~ r2_hidden(k2_waybel_0(sK0,X9,X10),X11)
        | ~ r1_orders_2(X9,sK3(sK0,X9,X11),X10)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ l1_waybel_0(X9,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f256,plain,
    ( r1_orders_2(sK1,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),sK6(sK0,sK1,sK2,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))))
    | ~ spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f69,f68,f138,f67,f66,f179,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f179,plain,
    ( m1_subset_1(sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),u1_struct_0(sK1))
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f69,f68,f66,f67,f141,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f138,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK2)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl12_1
  <=> ~ r1_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f255,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))),u1_struct_0(sK1))
    | ~ spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f69,f68,f138,f67,f66,f179,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f141,plain,
    ( ~ r2_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl12_3
  <=> ~ r2_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f3827,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)))),sK2)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_20 ),
    inference(unit_resulting_resolution,[],[f66,f67,f138,f3470,f489])).

fof(f489,plain,
    ( ! [X4,X5,X3] :
        ( r1_waybel_0(sK0,X3,X5)
        | v2_struct_0(X3)
        | ~ r2_hidden(k2_waybel_0(sK0,X3,sK6(sK0,X3,X5,X4)),X5)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f488])).

fof(f488,plain,
    ( spl12_20
  <=> ! [X3,X5,X4] :
        ( v2_struct_0(X3)
        | r1_waybel_0(sK0,X3,X5)
        | ~ r2_hidden(k2_waybel_0(sK0,X3,sK6(sK0,X3,X5,X4)),X5)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f3470,plain,
    ( m1_subset_1(sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),u1_struct_0(sK1))
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f69,f68,f66,f67,f141,f74])).

fof(f24551,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)))),u1_struct_0(sK0))
    | ~ spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f68,f69,f67,f66,f24293,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t9_waybel_0.p',dt_k2_waybel_0)).

fof(f24293,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))),u1_struct_0(sK1))
    | ~ spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f69,f68,f138,f67,f66,f24244,f78])).

fof(f24244,plain,
    ( m1_subset_1(sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),u1_struct_0(sK1))
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f69,f68,f66,f67,f141,f74])).

fof(f112,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f68,f69,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t9_waybel_0.p',fc2_struct_0)).

fof(f731,plain,
    ( spl12_30
    | spl12_12 ),
    inference(avatar_split_clause,[],[f117,f339,f729])).

fof(f339,plain,
    ( spl12_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f117,plain,(
    ! [X10,X11,X9] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X9)
      | ~ l1_waybel_0(X9,sK0)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ r1_orders_2(X9,sK3(sK0,X9,X11),X10)
      | ~ r2_hidden(k2_waybel_0(sK0,X9,X10),X11)
      | r2_waybel_0(sK0,X9,X11) ) ),
    inference(resolution,[],[f69,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X1,sK3(X0,X1,X2),X4)
      | ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f584,plain,
    ( spl12_26
    | spl12_12 ),
    inference(avatar_split_clause,[],[f119,f339,f582])).

fof(f119,plain,(
    ! [X17,X15,X16] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X15)
      | ~ l1_waybel_0(X15,sK0)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | r2_hidden(k2_waybel_0(sK0,X15,sK4(sK0,X15,X17,X16)),X17)
      | ~ r2_waybel_0(sK0,X15,X17) ) ),
    inference(resolution,[],[f69,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f490,plain,
    ( spl12_20
    | spl12_12 ),
    inference(avatar_split_clause,[],[f115,f339,f488])).

fof(f115,plain,(
    ! [X4,X5,X3] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ r2_hidden(k2_waybel_0(sK0,X3,sK6(sK0,X3,X5,X4)),X5)
      | r1_waybel_0(sK0,X3,X5) ) ),
    inference(resolution,[],[f69,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK6(X0,X1,X2,X3)),X2)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f412,plain,(
    ~ spl12_12 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f68,f340])).

fof(f340,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f339])).

fof(f408,plain,
    ( spl12_14
    | spl12_12 ),
    inference(avatar_split_clause,[],[f118,f339,f406])).

fof(f118,plain,(
    ! [X14,X12,X13] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X12)
      | ~ l1_waybel_0(X12,sK0)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | r1_orders_2(X12,X13,sK4(sK0,X12,X14,X13))
      | ~ r2_waybel_0(sK0,X12,X14) ) ),
    inference(resolution,[],[f69,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_orders_2(X1,X3,sK4(X0,X1,X2,X3))
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f160,plain,
    ( spl12_0
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f107,f140,f134])).

fof(f107,plain,
    ( ~ r2_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | r1_waybel_0(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f64,f75])).

fof(f75,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t9_waybel_0.p',redefinition_k6_subset_1)).

fof(f64,plain,
    ( ~ r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
    | r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f145,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f106,f143,f137])).

fof(f106,plain,
    ( r2_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ r1_waybel_0(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f65,f75])).

fof(f65,plain,
    ( r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
    | ~ r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
