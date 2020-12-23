%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1626+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:27 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 234 expanded)
%              Number of leaves         :   20 ( 101 expanded)
%              Depth                    :   10
%              Number of atoms          :  425 (2021 expanded)
%              Number of equality atoms :   44 ( 305 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6374,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6045,f6050,f6055,f6060,f6065,f6070,f6075,f6080,f6085,f6090,f6095,f6109,f6353,f6373])).

fof(f6373,plain,
    ( spl366_1
    | ~ spl366_2
    | ~ spl366_3
    | spl366_4
    | ~ spl366_5
    | ~ spl366_6
    | ~ spl366_7
    | ~ spl366_8
    | ~ spl366_9
    | spl366_10
    | ~ spl366_11
    | spl366_14 ),
    inference(avatar_contradiction_clause,[],[f6372])).

fof(f6372,plain,
    ( $false
    | spl366_1
    | ~ spl366_2
    | ~ spl366_3
    | spl366_4
    | ~ spl366_5
    | ~ spl366_6
    | ~ spl366_7
    | ~ spl366_8
    | ~ spl366_9
    | spl366_10
    | ~ spl366_11
    | spl366_14 ),
    inference(subsumption_resolution,[],[f6371,f6343])).

fof(f6343,plain,
    ( r2_hidden(k2_yellow_0(sK2,sK4),u1_struct_0(sK3))
    | spl366_1
    | ~ spl366_3
    | ~ spl366_6
    | ~ spl366_7
    | ~ spl366_8
    | ~ spl366_9
    | spl366_10
    | ~ spl366_11 ),
    inference(unit_resulting_resolution,[],[f6044,f6054,f6074,f6069,f6084,f6079,f6089,f6094,f4385])).

fof(f4385,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k2_yellow_0(X0,X3),u1_struct_0(X1))
      | k1_xboole_0 = X3
      | ~ r2_yellow_0(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_waybel_0(X3,X1)
      | ~ v3_waybel_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3856])).

fof(f3856,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_waybel_0(X1,X0)
              | ( ~ r2_hidden(k2_yellow_0(X0,sK30(X0,X1)),u1_struct_0(X1))
                & k1_xboole_0 != sK30(X0,X1)
                & r2_yellow_0(X0,sK30(X0,X1))
                & m1_subset_1(sK30(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_0(sK30(X0,X1),X1) ) )
            & ( ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),u1_struct_0(X1))
                  | k1_xboole_0 = X3
                  | ~ r2_yellow_0(X0,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v2_waybel_0(X3,X1) )
              | ~ v3_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK30])],[f3854,f3855])).

fof(f3855,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
          & k1_xboole_0 != X2
          & r2_yellow_0(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v2_waybel_0(X2,X1) )
     => ( ~ r2_hidden(k2_yellow_0(X0,sK30(X0,X1)),u1_struct_0(X1))
        & k1_xboole_0 != sK30(X0,X1)
        & r2_yellow_0(X0,sK30(X0,X1))
        & m1_subset_1(sK30(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
        & v2_waybel_0(sK30(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f3854,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & k1_xboole_0 != X2
                  & r2_yellow_0(X0,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_0(X2,X1) ) )
            & ( ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),u1_struct_0(X1))
                  | k1_xboole_0 = X3
                  | ~ r2_yellow_0(X0,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v2_waybel_0(X3,X1) )
              | ~ v3_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3853])).

fof(f3853,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & k1_xboole_0 != X2
                  & r2_yellow_0(X0,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_0(X2,X1) ) )
            & ( ! [X2] :
                  ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  | k1_xboole_0 = X2
                  | ~ r2_yellow_0(X0,X2)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v2_waybel_0(X2,X1) )
              | ~ v3_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3245])).

fof(f3245,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                | k1_xboole_0 = X2
                | ~ r2_yellow_0(X0,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_0(X2,X1) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3244])).

fof(f3244,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                | k1_xboole_0 = X2
                | ~ r2_yellow_0(X0,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_0(X2,X1) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3156])).

fof(f3156,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v3_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_0(X2,X1) )
               => ( r2_yellow_0(X0,X2)
                 => ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                    | k1_xboole_0 = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_waybel_0)).

fof(f6094,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl366_11 ),
    inference(avatar_component_clause,[],[f6092])).

fof(f6092,plain,
    ( spl366_11
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_11])])).

fof(f6089,plain,
    ( k1_xboole_0 != sK4
    | spl366_10 ),
    inference(avatar_component_clause,[],[f6087])).

fof(f6087,plain,
    ( spl366_10
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_10])])).

fof(f6079,plain,
    ( v2_waybel_0(sK4,sK3)
    | ~ spl366_8 ),
    inference(avatar_component_clause,[],[f6077])).

fof(f6077,plain,
    ( spl366_8
  <=> v2_waybel_0(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_8])])).

fof(f6084,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ spl366_9 ),
    inference(avatar_component_clause,[],[f6082])).

fof(f6082,plain,
    ( spl366_9
  <=> r2_yellow_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_9])])).

fof(f6069,plain,
    ( v3_waybel_0(sK3,sK2)
    | ~ spl366_6 ),
    inference(avatar_component_clause,[],[f6067])).

fof(f6067,plain,
    ( spl366_6
  <=> v3_waybel_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_6])])).

fof(f6074,plain,
    ( m1_yellow_0(sK3,sK2)
    | ~ spl366_7 ),
    inference(avatar_component_clause,[],[f6072])).

fof(f6072,plain,
    ( spl366_7
  <=> m1_yellow_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_7])])).

fof(f6054,plain,
    ( l1_orders_2(sK2)
    | ~ spl366_3 ),
    inference(avatar_component_clause,[],[f6052])).

fof(f6052,plain,
    ( spl366_3
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_3])])).

fof(f6044,plain,
    ( ~ v2_struct_0(sK2)
    | spl366_1 ),
    inference(avatar_component_clause,[],[f6042])).

fof(f6042,plain,
    ( spl366_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_1])])).

fof(f6371,plain,
    ( ~ r2_hidden(k2_yellow_0(sK2,sK4),u1_struct_0(sK3))
    | spl366_1
    | ~ spl366_2
    | ~ spl366_3
    | spl366_4
    | ~ spl366_5
    | ~ spl366_7
    | ~ spl366_9
    | ~ spl366_11
    | spl366_14 ),
    inference(unit_resulting_resolution,[],[f6044,f6049,f6054,f6059,f6064,f6074,f6084,f6094,f6108,f4275])).

fof(f4275,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3193])).

fof(f3193,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3192])).

fof(f3192,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3062])).

fof(f3062,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & r2_yellow_0(X0,X2) )
               => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                  & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_yellow_0)).

fof(f6108,plain,
    ( k2_yellow_0(sK2,sK4) != k2_yellow_0(sK3,sK4)
    | spl366_14 ),
    inference(avatar_component_clause,[],[f6106])).

fof(f6106,plain,
    ( spl366_14
  <=> k2_yellow_0(sK2,sK4) = k2_yellow_0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_14])])).

fof(f6064,plain,
    ( v4_yellow_0(sK3,sK2)
    | ~ spl366_5 ),
    inference(avatar_component_clause,[],[f6062])).

fof(f6062,plain,
    ( spl366_5
  <=> v4_yellow_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_5])])).

fof(f6059,plain,
    ( ~ v2_struct_0(sK3)
    | spl366_4 ),
    inference(avatar_component_clause,[],[f6057])).

fof(f6057,plain,
    ( spl366_4
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_4])])).

fof(f6049,plain,
    ( v4_orders_2(sK2)
    | ~ spl366_2 ),
    inference(avatar_component_clause,[],[f6047])).

fof(f6047,plain,
    ( spl366_2
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_2])])).

fof(f6353,plain,
    ( spl366_1
    | ~ spl366_2
    | ~ spl366_3
    | spl366_4
    | ~ spl366_5
    | ~ spl366_6
    | ~ spl366_7
    | ~ spl366_8
    | ~ spl366_9
    | spl366_10
    | ~ spl366_11
    | spl366_13 ),
    inference(avatar_contradiction_clause,[],[f6352])).

fof(f6352,plain,
    ( $false
    | spl366_1
    | ~ spl366_2
    | ~ spl366_3
    | spl366_4
    | ~ spl366_5
    | ~ spl366_6
    | ~ spl366_7
    | ~ spl366_8
    | ~ spl366_9
    | spl366_10
    | ~ spl366_11
    | spl366_13 ),
    inference(subsumption_resolution,[],[f6351,f6343])).

fof(f6351,plain,
    ( ~ r2_hidden(k2_yellow_0(sK2,sK4),u1_struct_0(sK3))
    | spl366_1
    | ~ spl366_2
    | ~ spl366_3
    | spl366_4
    | ~ spl366_5
    | ~ spl366_7
    | ~ spl366_9
    | ~ spl366_11
    | spl366_13 ),
    inference(unit_resulting_resolution,[],[f6044,f6049,f6054,f6059,f6064,f6074,f6084,f6104,f6094,f4274])).

fof(f4274,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | r2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3193])).

fof(f6104,plain,
    ( ~ r2_yellow_0(sK3,sK4)
    | spl366_13 ),
    inference(avatar_component_clause,[],[f6102])).

fof(f6102,plain,
    ( spl366_13
  <=> r2_yellow_0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl366_13])])).

fof(f6109,plain,
    ( ~ spl366_13
    | ~ spl366_14 ),
    inference(avatar_split_clause,[],[f4259,f6106,f6102])).

fof(f4259,plain,
    ( k2_yellow_0(sK2,sK4) != k2_yellow_0(sK3,sK4)
    | ~ r2_yellow_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f3785])).

fof(f3785,plain,
    ( ( k2_yellow_0(sK2,sK4) != k2_yellow_0(sK3,sK4)
      | ~ r2_yellow_0(sK3,sK4) )
    & k1_xboole_0 != sK4
    & r2_yellow_0(sK2,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v2_waybel_0(sK4,sK3)
    & m1_yellow_0(sK3,sK2)
    & v3_waybel_0(sK3,sK2)
    & v4_yellow_0(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_orders_2(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f3184,f3784,f3783,f3782])).

fof(f3782,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                  | ~ r2_yellow_0(X1,X2) )
                & k1_xboole_0 != X2
                & r2_yellow_0(X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_0(X2,X1) )
            & m1_yellow_0(X1,X0)
            & v3_waybel_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X1,X2) != k2_yellow_0(sK2,X2)
                | ~ r2_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r2_yellow_0(sK2,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v2_waybel_0(X2,X1) )
          & m1_yellow_0(X1,sK2)
          & v3_waybel_0(X1,sK2)
          & v4_yellow_0(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3783,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_yellow_0(X1,X2) != k2_yellow_0(sK2,X2)
              | ~ r2_yellow_0(X1,X2) )
            & k1_xboole_0 != X2
            & r2_yellow_0(sK2,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
            & v2_waybel_0(X2,X1) )
        & m1_yellow_0(X1,sK2)
        & v3_waybel_0(X1,sK2)
        & v4_yellow_0(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_yellow_0(sK2,X2) != k2_yellow_0(sK3,X2)
            | ~ r2_yellow_0(sK3,X2) )
          & k1_xboole_0 != X2
          & r2_yellow_0(sK2,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
          & v2_waybel_0(X2,sK3) )
      & m1_yellow_0(sK3,sK2)
      & v3_waybel_0(sK3,sK2)
      & v4_yellow_0(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3784,plain,
    ( ? [X2] :
        ( ( k2_yellow_0(sK2,X2) != k2_yellow_0(sK3,X2)
          | ~ r2_yellow_0(sK3,X2) )
        & k1_xboole_0 != X2
        & r2_yellow_0(sK2,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        & v2_waybel_0(X2,sK3) )
   => ( ( k2_yellow_0(sK2,sK4) != k2_yellow_0(sK3,sK4)
        | ~ r2_yellow_0(sK3,sK4) )
      & k1_xboole_0 != sK4
      & r2_yellow_0(sK2,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      & v2_waybel_0(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3184,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r2_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v2_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v3_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3183])).

fof(f3183,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r2_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v2_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v3_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3167])).

fof(f3167,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v3_waybel_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_0(X2,X1) )
               => ( r2_yellow_0(X0,X2)
                 => ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                      & r2_yellow_0(X1,X2) )
                    | k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3166])).

fof(f3166,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v3_waybel_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_0(X2,X1) )
             => ( r2_yellow_0(X0,X2)
               => ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                    & r2_yellow_0(X1,X2) )
                  | k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_waybel_0)).

fof(f6095,plain,(
    spl366_11 ),
    inference(avatar_split_clause,[],[f4256,f6092])).

fof(f4256,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f3785])).

fof(f6090,plain,(
    ~ spl366_10 ),
    inference(avatar_split_clause,[],[f4258,f6087])).

fof(f4258,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f3785])).

fof(f6085,plain,(
    spl366_9 ),
    inference(avatar_split_clause,[],[f4257,f6082])).

fof(f4257,plain,(
    r2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f3785])).

fof(f6080,plain,(
    spl366_8 ),
    inference(avatar_split_clause,[],[f4255,f6077])).

fof(f4255,plain,(
    v2_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f3785])).

fof(f6075,plain,(
    spl366_7 ),
    inference(avatar_split_clause,[],[f4254,f6072])).

fof(f4254,plain,(
    m1_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f3785])).

fof(f6070,plain,(
    spl366_6 ),
    inference(avatar_split_clause,[],[f4253,f6067])).

fof(f4253,plain,(
    v3_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f3785])).

fof(f6065,plain,(
    spl366_5 ),
    inference(avatar_split_clause,[],[f4252,f6062])).

fof(f4252,plain,(
    v4_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f3785])).

fof(f6060,plain,(
    ~ spl366_4 ),
    inference(avatar_split_clause,[],[f4251,f6057])).

fof(f4251,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3785])).

fof(f6055,plain,(
    spl366_3 ),
    inference(avatar_split_clause,[],[f4250,f6052])).

fof(f4250,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3785])).

fof(f6050,plain,(
    spl366_2 ),
    inference(avatar_split_clause,[],[f4249,f6047])).

fof(f4249,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3785])).

fof(f6045,plain,(
    ~ spl366_1 ),
    inference(avatar_split_clause,[],[f4248,f6042])).

fof(f4248,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3785])).
%------------------------------------------------------------------------------
