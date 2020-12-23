%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t10_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:44 EDT 2019

% Result     : Theorem 7.60s
% Output     : Refutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 540 expanded)
%              Number of leaves         :   20 ( 133 expanded)
%              Depth                    :   11
%              Number of atoms          :  434 (2660 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30031,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f158,f347,f396,f470,f550,f675,f1295,f1299,f2054,f27646,f30030])).

fof(f30030,plain,
    ( ~ spl12_0
    | ~ spl12_2
    | ~ spl12_10
    | ~ spl12_18 ),
    inference(avatar_contradiction_clause,[],[f30019])).

fof(f30019,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_10
    | ~ spl12_18 ),
    inference(unit_resulting_resolution,[],[f66,f69,f68,f67,f144,f27692,f1562,f2006,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X1,sK3(X0,X1,X2),X4)
      | r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | ~ r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/waybel_0__t10_waybel_0.p',d11_waybel_0)).

fof(f2006,plain,
    ( ! [X0] : ~ r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)))),k4_xboole_0(X0,sK2))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_18 ),
    inference(unit_resulting_resolution,[],[f1563,f110])).

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
    file('/export/starexec/sandbox/benchmark/waybel_0__t10_waybel_0.p',d5_xboole_0)).

fof(f1563,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)))),sK2)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_18 ),
    inference(unit_resulting_resolution,[],[f66,f67,f135,f1547,f469])).

fof(f469,plain,
    ( ! [X6,X8,X7] :
        ( ~ r2_waybel_0(sK0,X6,X8)
        | v2_struct_0(X6)
        | r2_hidden(k2_waybel_0(sK0,X6,sK6(sK0,X6,X8,X7)),X8)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ l1_waybel_0(X6,sK0) )
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl12_18
  <=> ! [X7,X8,X6] :
        ( v2_struct_0(X6)
        | ~ r2_waybel_0(sK0,X6,X8)
        | r2_hidden(k2_waybel_0(sK0,X6,sK6(sK0,X6,X8,X7)),X8)
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ l1_waybel_0(X6,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f1547,plain,
    ( m1_subset_1(sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),u1_struct_0(sK1))
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f69,f68,f66,f67,f144,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | ~ r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f135,plain,
    ( r2_waybel_0(sK0,sK1,sK2)
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl12_0
  <=> r2_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f1562,plain,
    ( r1_orders_2(sK1,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),sK6(sK0,sK1,sK2,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))))
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_10 ),
    inference(unit_resulting_resolution,[],[f66,f67,f135,f1547,f340])).

fof(f340,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_waybel_0(sK0,X3,X5)
        | v2_struct_0(X3)
        | r1_orders_2(X3,X4,sK6(sK0,X3,X5,X4))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_waybel_0(X3,sK0) )
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl12_10
  <=> ! [X3,X5,X4] :
        ( v2_struct_0(X3)
        | ~ r2_waybel_0(sK0,X3,X5)
        | r1_orders_2(X3,X4,sK6(sK0,X3,X5,X4))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_waybel_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f27692,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2,sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))),u1_struct_0(sK1))
    | ~ spl12_0
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f69,f68,f135,f67,f66,f27671,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox/benchmark/waybel_0__t10_waybel_0.p',d12_waybel_0)).

fof(f27671,plain,
    ( m1_subset_1(sK3(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),u1_struct_0(sK1))
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f69,f68,f66,f67,f144,f74])).

fof(f144,plain,
    ( r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl12_2
  <=> r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f67,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <~> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <~> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
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
                ( r2_waybel_0(X0,X1,X2)
              <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t10_waybel_0.p',t10_waybel_0)).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f27646,plain,
    ( spl12_1
    | spl12_3
    | ~ spl12_30
    | ~ spl12_48 ),
    inference(avatar_contradiction_clause,[],[f27644])).

fof(f27644,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_30
    | ~ spl12_48 ),
    inference(unit_resulting_resolution,[],[f112,f10016,f4531,f90])).

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
    file('/export/starexec/sandbox/benchmark/waybel_0__t10_waybel_0.p',t2_subset)).

fof(f4531,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2))),u1_struct_0(sK0))
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_30
    | ~ spl12_48 ),
    inference(unit_resulting_resolution,[],[f871,f1325,f109])).

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

fof(f1325,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2))),k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl12_1
    | ~ spl12_48 ),
    inference(unit_resulting_resolution,[],[f147,f1288])).

fof(f1288,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),X0)),k4_xboole_0(u1_struct_0(sK0),sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl12_48 ),
    inference(avatar_component_clause,[],[f1287])).

fof(f1287,plain,
    ( spl12_48
  <=> ! [X0] :
        ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),X0)),k4_xboole_0(u1_struct_0(sK0),sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_48])])).

fof(f147,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f69,f68,f66,f67,f138,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f138,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK2)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl12_1
  <=> ~ r2_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f871,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2))),sK2)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_30 ),
    inference(unit_resulting_resolution,[],[f66,f67,f138,f198,f199,f674])).

fof(f674,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(X0,sK5(sK0,X0,X2),X1)
        | r2_waybel_0(sK0,X0,X2)
        | ~ r2_hidden(k2_waybel_0(sK0,X0,X1),X2)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f673])).

fof(f673,plain,
    ( spl12_30
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | r2_waybel_0(sK0,X0,X2)
        | ~ r2_hidden(k2_waybel_0(sK0,X0,X1),X2)
        | ~ r1_orders_2(X0,sK5(sK0,X0,X2),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f199,plain,
    ( r1_orders_2(sK1,sK5(sK0,sK1,sK2),sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2)))
    | ~ spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f69,f68,f141,f67,f66,f147,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_orders_2(X1,X3,sK4(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f141,plain,
    ( ~ r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl12_3
  <=> ~ r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f198,plain,
    ( m1_subset_1(sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f69,f68,f141,f67,f66,f147,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10016,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2))),u1_struct_0(sK0))
    | ~ spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f68,f69,f67,f66,f9800,f86])).

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
    file('/export/starexec/sandbox/benchmark/waybel_0__t10_waybel_0.p',dt_k2_waybel_0)).

fof(f9800,plain,
    ( m1_subset_1(sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),sK5(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f69,f68,f141,f67,f66,f9757,f70])).

fof(f9757,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f69,f68,f66,f67,f138,f82])).

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
    file('/export/starexec/sandbox/benchmark/waybel_0__t10_waybel_0.p',fc2_struct_0)).

fof(f2054,plain,(
    ~ spl12_50 ),
    inference(avatar_contradiction_clause,[],[f2051])).

fof(f2051,plain,
    ( $false
    | ~ spl12_50 ),
    inference(unit_resulting_resolution,[],[f66,f1294])).

fof(f1294,plain,
    ( v2_struct_0(sK1)
    | ~ spl12_50 ),
    inference(avatar_component_clause,[],[f1293])).

fof(f1293,plain,
    ( spl12_50
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).

fof(f1299,plain,(
    spl12_47 ),
    inference(avatar_contradiction_clause,[],[f1296])).

fof(f1296,plain,
    ( $false
    | ~ spl12_47 ),
    inference(unit_resulting_resolution,[],[f67,f1285])).

fof(f1285,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ spl12_47 ),
    inference(avatar_component_clause,[],[f1284])).

fof(f1284,plain,
    ( spl12_47
  <=> ~ l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_47])])).

fof(f1295,plain,
    ( ~ spl12_47
    | spl12_48
    | spl12_50
    | spl12_3
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f612,f548,f140,f1293,f1287,f1284])).

fof(f548,plain,
    ( spl12_24
  <=> ! [X13,X12,X14] :
        ( v2_struct_0(X12)
        | r1_waybel_0(sK0,X12,X14)
        | ~ r2_hidden(k2_waybel_0(sK0,X12,sK4(sK0,X12,X14,X13)),X14)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_waybel_0(X12,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f612,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2),X0)),k4_xboole_0(u1_struct_0(sK0),sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0) )
    | ~ spl12_3
    | ~ spl12_24 ),
    inference(resolution,[],[f549,f141])).

fof(f549,plain,
    ( ! [X14,X12,X13] :
        ( r1_waybel_0(sK0,X12,X14)
        | v2_struct_0(X12)
        | ~ r2_hidden(k2_waybel_0(sK0,X12,sK4(sK0,X12,X14,X13)),X14)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ l1_waybel_0(X12,sK0) )
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f548])).

fof(f675,plain,
    ( spl12_30
    | spl12_12 ),
    inference(avatar_split_clause,[],[f114,f345,f673])).

fof(f345,plain,
    ( spl12_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK5(sK0,X0,X2),X1)
      | ~ r2_hidden(k2_waybel_0(sK0,X0,X1),X2)
      | r2_waybel_0(sK0,X0,X2) ) ),
    inference(resolution,[],[f69,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X1,sK5(X0,X1,X2),X4)
      | ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f550,plain,
    ( spl12_24
    | spl12_12 ),
    inference(avatar_split_clause,[],[f118,f345,f548])).

fof(f118,plain,(
    ! [X14,X12,X13] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X12)
      | ~ l1_waybel_0(X12,sK0)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ r2_hidden(k2_waybel_0(sK0,X12,sK4(sK0,X12,X14,X13)),X14)
      | r1_waybel_0(sK0,X12,X14) ) ),
    inference(resolution,[],[f69,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f470,plain,
    ( spl12_18
    | spl12_12 ),
    inference(avatar_split_clause,[],[f116,f345,f468])).

fof(f116,plain,(
    ! [X6,X8,X7] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X6)
      | ~ l1_waybel_0(X6,sK0)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | r2_hidden(k2_waybel_0(sK0,X6,sK6(sK0,X6,X8,X7)),X8)
      | ~ r2_waybel_0(sK0,X6,X8) ) ),
    inference(resolution,[],[f69,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK6(X0,X1,X2,X3)),X2)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f396,plain,(
    ~ spl12_12 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f68,f346])).

fof(f346,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f345])).

fof(f347,plain,
    ( spl12_10
    | spl12_12 ),
    inference(avatar_split_clause,[],[f115,f345,f339])).

fof(f115,plain,(
    ! [X4,X5,X3] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | r1_orders_2(X3,X4,sK6(sK0,X3,X5,X4))
      | ~ r2_waybel_0(sK0,X3,X5) ) ),
    inference(resolution,[],[f69,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f158,plain,
    ( spl12_0
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f107,f140,f134])).

fof(f107,plain,
    ( ~ r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | r2_waybel_0(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f64,f75])).

fof(f75,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t10_waybel_0.p',redefinition_k6_subset_1)).

fof(f64,plain,
    ( ~ r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
    | r2_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f145,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f106,f143,f137])).

fof(f106,plain,
    ( r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ r2_waybel_0(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f65,f75])).

fof(f65,plain,
    ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
    | ~ r2_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
