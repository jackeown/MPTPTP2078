%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1630+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:27 EST 2020

% Result     : Theorem 45.87s
% Output     : Refutation 46.10s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 280 expanded)
%              Number of leaves         :   28 ( 125 expanded)
%              Depth                    :   11
%              Number of atoms          :  625 (1448 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f7607,f7609,f7614,f7619,f7624,f7629,f8034,f8063,f9443,f9448,f9453,f127162])).

fof(f127162,plain,
    ( ~ spl554_2
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6
    | ~ spl554_227
    | ~ spl554_228
    | ~ spl554_229 ),
    inference(avatar_contradiction_clause,[],[f127161])).

fof(f127161,plain,
    ( $false
    | ~ spl554_2
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6
    | ~ spl554_227
    | ~ spl554_228
    | ~ spl554_229 ),
    inference(subsumption_resolution,[],[f127149,f126170])).

fof(f126170,plain,
    ( ! [X0] : ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)))),k4_xboole_0(X0,sK2))
    | ~ spl554_227 ),
    inference(unit_resulting_resolution,[],[f9442,f6968])).

fof(f6968,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f5617])).

fof(f5617,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4505])).

fof(f4505,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK87(X0,X1,X2),X1)
            | ~ r2_hidden(sK87(X0,X1,X2),X0)
            | ~ r2_hidden(sK87(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK87(X0,X1,X2),X1)
              & r2_hidden(sK87(X0,X1,X2),X0) )
            | r2_hidden(sK87(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK87])],[f4503,f4504])).

fof(f4504,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK87(X0,X1,X2),X1)
          | ~ r2_hidden(sK87(X0,X1,X2),X0)
          | ~ r2_hidden(sK87(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK87(X0,X1,X2),X1)
            & r2_hidden(sK87(X0,X1,X2),X0) )
          | r2_hidden(sK87(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f4503,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f4502])).

fof(f4502,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f4501])).

fof(f4501,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f9442,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)))),sK2)
    | ~ spl554_227 ),
    inference(avatar_component_clause,[],[f9440])).

fof(f9440,plain,
    ( spl554_227
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl554_227])])).

fof(f127149,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)))),k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl554_2
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6
    | ~ spl554_228
    | ~ spl554_229 ),
    inference(unit_resulting_resolution,[],[f7628,f7623,f7613,f7606,f9452,f9447,f7632])).

fof(f7632,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(X6)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | ~ r1_waybel_0(X6,sK1,X7)
        | ~ l1_waybel_0(sK1,X6)
        | r2_hidden(k2_waybel_0(X6,sK1,X8),X7)
        | ~ l1_struct_0(X6)
        | ~ r1_orders_2(sK1,sK4(X6,sK1,X7),X8) )
    | spl554_4 ),
    inference(resolution,[],[f7618,f5032])).

fof(f5032,plain,(
    ! [X6,X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ r1_orders_2(X1,sK4(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | r2_hidden(k2_waybel_0(X0,X1,X6),X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4292])).

fof(f4292,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK3(X0,X1,X2,X3))
                      & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK4(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f4289,f4291,f4290])).

fof(f4290,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4291,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK4(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4289,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f4288])).

fof(f4288,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3205])).

fof(f3205,plain,(
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
    inference(flattening,[],[f3204])).

fof(f3204,plain,(
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
    inference(ennf_transformation,[],[f3154])).

fof(f3154,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f7618,plain,
    ( ~ v2_struct_0(sK1)
    | spl554_4 ),
    inference(avatar_component_clause,[],[f7616])).

fof(f7616,plain,
    ( spl554_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl554_4])])).

fof(f9447,plain,
    ( r1_orders_2(sK1,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),sK8(sK0,sK1,sK2,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))))
    | ~ spl554_228 ),
    inference(avatar_component_clause,[],[f9445])).

fof(f9445,plain,
    ( spl554_228
  <=> r1_orders_2(sK1,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),sK8(sK0,sK1,sK2,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl554_228])])).

fof(f9452,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))),u1_struct_0(sK1))
    | ~ spl554_229 ),
    inference(avatar_component_clause,[],[f9450])).

fof(f9450,plain,
    ( spl554_229
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl554_229])])).

fof(f7606,plain,
    ( r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl554_2 ),
    inference(avatar_component_clause,[],[f7604])).

fof(f7604,plain,
    ( spl554_2
  <=> r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl554_2])])).

fof(f7613,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl554_3 ),
    inference(avatar_component_clause,[],[f7611])).

fof(f7611,plain,
    ( spl554_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl554_3])])).

fof(f7623,plain,
    ( l1_struct_0(sK0)
    | ~ spl554_5 ),
    inference(avatar_component_clause,[],[f7621])).

fof(f7621,plain,
    ( spl554_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl554_5])])).

fof(f7628,plain,
    ( ~ v2_struct_0(sK0)
    | spl554_6 ),
    inference(avatar_component_clause,[],[f7626])).

fof(f7626,plain,
    ( spl554_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl554_6])])).

fof(f9453,plain,
    ( spl554_229
    | ~ spl554_1
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6
    | ~ spl554_63 ),
    inference(avatar_split_clause,[],[f9430,f8060,f7626,f7621,f7616,f7611,f7600,f9450])).

fof(f7600,plain,
    ( spl554_1
  <=> r2_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl554_1])])).

fof(f8060,plain,
    ( spl554_63
  <=> m1_subset_1(sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl554_63])])).

fof(f9430,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))),u1_struct_0(sK1))
    | ~ spl554_1
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6
    | ~ spl554_63 ),
    inference(unit_resulting_resolution,[],[f7628,f7623,f7618,f7613,f7601,f8062,f5057])).

fof(f5057,plain,(
    ! [X2,X0,X5,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X5),u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4300])).

fof(f4300,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK7(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK8(X0,X1,X2,X5))
                      & m1_subset_1(sK8(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f4297,f4299,f4298])).

fof(f4298,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK7(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4299,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK8(X0,X1,X2,X5))
        & m1_subset_1(sK8(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4297,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f4296])).

fof(f4296,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3232])).

fof(f3232,plain,(
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
    inference(flattening,[],[f3231])).

fof(f3231,plain,(
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
    inference(ennf_transformation,[],[f3155])).

fof(f3155,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f8062,plain,
    ( m1_subset_1(sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),u1_struct_0(sK1))
    | ~ spl554_63 ),
    inference(avatar_component_clause,[],[f8060])).

fof(f7601,plain,
    ( r2_waybel_0(sK0,sK1,sK2)
    | ~ spl554_1 ),
    inference(avatar_component_clause,[],[f7600])).

fof(f9448,plain,
    ( spl554_228
    | ~ spl554_1
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6
    | ~ spl554_63 ),
    inference(avatar_split_clause,[],[f9431,f8060,f7626,f7621,f7616,f7611,f7600,f9445])).

fof(f9431,plain,
    ( r1_orders_2(sK1,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),sK8(sK0,sK1,sK2,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))))
    | ~ spl554_1
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6
    | ~ spl554_63 ),
    inference(unit_resulting_resolution,[],[f7628,f7623,f7618,f7613,f7601,f8062,f5058])).

fof(f5058,plain,(
    ! [X2,X0,X5,X1] :
      ( v2_struct_0(X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | r1_orders_2(X1,X5,sK8(X0,X1,X2,X5))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4300])).

fof(f9443,plain,
    ( spl554_227
    | ~ spl554_1
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6
    | ~ spl554_63 ),
    inference(avatar_split_clause,[],[f9432,f8060,f7626,f7621,f7616,f7611,f7600,f9440])).

fof(f9432,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)))),sK2)
    | ~ spl554_1
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6
    | ~ spl554_63 ),
    inference(unit_resulting_resolution,[],[f7628,f7623,f7618,f7613,f7601,f8062,f5059])).

fof(f5059,plain,(
    ! [X2,X0,X5,X1] :
      ( v2_struct_0(X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X5)),X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4300])).

fof(f8063,plain,
    ( spl554_63
    | ~ spl554_2
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6 ),
    inference(avatar_split_clause,[],[f8043,f7626,f7621,f7616,f7611,f7604,f8060])).

fof(f8043,plain,
    ( m1_subset_1(sK4(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2)),u1_struct_0(sK1))
    | ~ spl554_2
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6 ),
    inference(unit_resulting_resolution,[],[f7628,f7623,f7618,f7613,f7606,f5031])).

fof(f5031,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4292])).

fof(f8034,plain,
    ( spl554_1
    | spl554_2
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6 ),
    inference(avatar_contradiction_clause,[],[f8033])).

fof(f8033,plain,
    ( $false
    | spl554_1
    | spl554_2
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6 ),
    inference(subsumption_resolution,[],[f8032,f7986])).

fof(f7986,plain,
    ( ! [X0] : ~ r2_waybel_0(sK0,sK1,k3_xboole_0(sK2,X0))
    | spl554_1
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6 ),
    inference(unit_resulting_resolution,[],[f7628,f7623,f7618,f6246,f7613,f7602,f5030])).

fof(f5030,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ r1_tarski(X2,X3)
      | ~ l1_waybel_0(X1,X0)
      | r2_waybel_0(X0,X1,X3)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3203])).

fof(f3203,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3202])).

fof(f3202,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3178])).

fof(f3178,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).

fof(f7602,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK2)
    | spl554_1 ),
    inference(avatar_component_clause,[],[f7600])).

fof(f6246,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f8032,plain,
    ( r2_waybel_0(sK0,sK1,k3_xboole_0(sK2,u1_struct_0(sK0)))
    | spl554_2
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6 ),
    inference(forward_demodulation,[],[f8031,f6245])).

fof(f6245,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f8031,plain,
    ( r2_waybel_0(sK0,sK1,k3_xboole_0(u1_struct_0(sK0),sK2))
    | spl554_2
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6 ),
    inference(forward_demodulation,[],[f8030,f5683])).

fof(f5683,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f8030,plain,
    ( r2_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)))
    | spl554_2
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6 ),
    inference(forward_demodulation,[],[f7992,f5051])).

fof(f5051,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f7992,plain,
    ( r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)))
    | spl554_2
    | ~ spl554_3
    | spl554_4
    | ~ spl554_5
    | spl554_6 ),
    inference(unit_resulting_resolution,[],[f7628,f7623,f7618,f7613,f7605,f5037])).

fof(f5037,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_0(X0,X1,X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4293])).

fof(f4293,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3207])).

fof(f3207,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3206])).

fof(f3206,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3179])).

fof(f3179,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).

fof(f7605,plain,
    ( ~ r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | spl554_2 ),
    inference(avatar_component_clause,[],[f7604])).

fof(f7629,plain,(
    ~ spl554_6 ),
    inference(avatar_split_clause,[],[f5023,f7626])).

fof(f5023,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f4287])).

fof(f4287,plain,
    ( ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
      | ~ r2_waybel_0(sK0,sK1,sK2) )
    & ( ~ r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
      | r2_waybel_0(sK0,sK1,sK2) )
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4283,f4286,f4285,f4284])).

fof(f4284,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                  | r2_waybel_0(X0,X1,X2) ) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r1_waybel_0(sK0,X1,k6_subset_1(u1_struct_0(sK0),X2))
                | ~ r2_waybel_0(sK0,X1,X2) )
              & ( ~ r1_waybel_0(sK0,X1,k6_subset_1(u1_struct_0(sK0),X2))
                | r2_waybel_0(sK0,X1,X2) ) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f4285,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( r1_waybel_0(sK0,X1,k6_subset_1(u1_struct_0(sK0),X2))
              | ~ r2_waybel_0(sK0,X1,X2) )
            & ( ~ r1_waybel_0(sK0,X1,k6_subset_1(u1_struct_0(sK0),X2))
              | r2_waybel_0(sK0,X1,X2) ) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X2))
            | ~ r2_waybel_0(sK0,sK1,X2) )
          & ( ~ r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X2))
            | r2_waybel_0(sK0,sK1,X2) ) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f4286,plain,
    ( ? [X2] :
        ( ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X2))
          | ~ r2_waybel_0(sK0,sK1,X2) )
        & ( ~ r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X2))
          | r2_waybel_0(sK0,sK1,X2) ) )
   => ( ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
        | ~ r2_waybel_0(sK0,sK1,sK2) )
      & ( ~ r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
        | r2_waybel_0(sK0,sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f4283,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r2_waybel_0(X0,X1,X2) )
              & ( ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | r2_waybel_0(X0,X1,X2) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3201])).

fof(f3201,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <~> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3200])).

fof(f3200,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <~> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3170])).

fof(f3170,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r2_waybel_0(X0,X1,X2)
              <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3169])).

fof(f3169,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f7624,plain,(
    spl554_5 ),
    inference(avatar_split_clause,[],[f5024,f7621])).

fof(f5024,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f4287])).

fof(f7619,plain,(
    ~ spl554_4 ),
    inference(avatar_split_clause,[],[f5025,f7616])).

fof(f5025,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f4287])).

fof(f7614,plain,(
    spl554_3 ),
    inference(avatar_split_clause,[],[f5026,f7611])).

fof(f5026,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f4287])).

fof(f7609,plain,
    ( spl554_1
    | ~ spl554_2 ),
    inference(avatar_split_clause,[],[f7608,f7604,f7600])).

fof(f7608,plain,
    ( ~ r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | r2_waybel_0(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f5027,f5051])).

fof(f5027,plain,
    ( ~ r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
    | r2_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f4287])).

fof(f7607,plain,
    ( ~ spl554_1
    | spl554_2 ),
    inference(avatar_split_clause,[],[f7598,f7604,f7600])).

fof(f7598,plain,
    ( r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ r2_waybel_0(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f5028,f5051])).

fof(f5028,plain,
    ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK2))
    | ~ r2_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f4287])).
%------------------------------------------------------------------------------
