%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1627+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:27 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
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
fof(f7355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f7046,f7051,f7056,f7061,f7066,f7071,f7076,f7081,f7086,f7091,f7096,f7110,f7336,f7354])).

fof(f7354,plain,
    ( spl546_1
    | ~ spl546_2
    | ~ spl546_3
    | spl546_4
    | ~ spl546_5
    | ~ spl546_6
    | ~ spl546_7
    | ~ spl546_8
    | ~ spl546_9
    | spl546_10
    | ~ spl546_11
    | spl546_14 ),
    inference(avatar_contradiction_clause,[],[f7353])).

fof(f7353,plain,
    ( $false
    | spl546_1
    | ~ spl546_2
    | ~ spl546_3
    | spl546_4
    | ~ spl546_5
    | ~ spl546_6
    | ~ spl546_7
    | ~ spl546_8
    | ~ spl546_9
    | spl546_10
    | ~ spl546_11
    | spl546_14 ),
    inference(subsumption_resolution,[],[f7352,f7331])).

fof(f7331,plain,
    ( r2_hidden(k1_yellow_0(sK2,sK4),u1_struct_0(sK3))
    | spl546_1
    | ~ spl546_3
    | ~ spl546_6
    | ~ spl546_7
    | ~ spl546_8
    | ~ spl546_9
    | spl546_10
    | ~ spl546_11 ),
    inference(unit_resulting_resolution,[],[f7045,f7055,f7075,f7070,f7085,f7080,f7090,f7095,f4735])).

fof(f4735,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_yellow_0(X0,X3),u1_struct_0(X1))
      | k1_xboole_0 = X3
      | ~ r1_yellow_0(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_waybel_0(X3,X1)
      | ~ v4_waybel_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3976])).

fof(f3976,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_0(X1,X0)
              | ( ~ r2_hidden(k1_yellow_0(X0,sK23(X0,X1)),u1_struct_0(X1))
                & k1_xboole_0 != sK23(X0,X1)
                & r1_yellow_0(X0,sK23(X0,X1))
                & m1_subset_1(sK23(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
                & v1_waybel_0(sK23(X0,X1),X1) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),u1_struct_0(X1))
                  | k1_xboole_0 = X3
                  | ~ r1_yellow_0(X0,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v1_waybel_0(X3,X1) )
              | ~ v4_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f3974,f3975])).

fof(f3975,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
          & k1_xboole_0 != X2
          & r1_yellow_0(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v1_waybel_0(X2,X1) )
     => ( ~ r2_hidden(k1_yellow_0(X0,sK23(X0,X1)),u1_struct_0(X1))
        & k1_xboole_0 != sK23(X0,X1)
        & r1_yellow_0(X0,sK23(X0,X1))
        & m1_subset_1(sK23(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
        & v1_waybel_0(sK23(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f3974,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & k1_xboole_0 != X2
                  & r1_yellow_0(X0,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_0(X2,X1) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),u1_struct_0(X1))
                  | k1_xboole_0 = X3
                  | ~ r1_yellow_0(X0,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v1_waybel_0(X3,X1) )
              | ~ v4_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3973])).

fof(f3973,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & k1_xboole_0 != X2
                  & r1_yellow_0(X0,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_0(X2,X1) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  | k1_xboole_0 = X2
                  | ~ r1_yellow_0(X0,X2)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v1_waybel_0(X2,X1) )
              | ~ v4_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3252])).

fof(f3252,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                | k1_xboole_0 = X2
                | ~ r1_yellow_0(X0,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_0(X2,X1) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3251])).

fof(f3251,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                | k1_xboole_0 = X2
                | ~ r1_yellow_0(X0,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_0(X2,X1) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3157])).

fof(f3157,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_0(X2,X1) )
               => ( r1_yellow_0(X0,X2)
                 => ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                    | k1_xboole_0 = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_waybel_0)).

fof(f7095,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl546_11 ),
    inference(avatar_component_clause,[],[f7093])).

fof(f7093,plain,
    ( spl546_11
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_11])])).

fof(f7090,plain,
    ( k1_xboole_0 != sK4
    | spl546_10 ),
    inference(avatar_component_clause,[],[f7088])).

fof(f7088,plain,
    ( spl546_10
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_10])])).

fof(f7080,plain,
    ( v1_waybel_0(sK4,sK3)
    | ~ spl546_8 ),
    inference(avatar_component_clause,[],[f7078])).

fof(f7078,plain,
    ( spl546_8
  <=> v1_waybel_0(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_8])])).

fof(f7085,plain,
    ( r1_yellow_0(sK2,sK4)
    | ~ spl546_9 ),
    inference(avatar_component_clause,[],[f7083])).

fof(f7083,plain,
    ( spl546_9
  <=> r1_yellow_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_9])])).

fof(f7070,plain,
    ( v4_waybel_0(sK3,sK2)
    | ~ spl546_6 ),
    inference(avatar_component_clause,[],[f7068])).

fof(f7068,plain,
    ( spl546_6
  <=> v4_waybel_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_6])])).

fof(f7075,plain,
    ( m1_yellow_0(sK3,sK2)
    | ~ spl546_7 ),
    inference(avatar_component_clause,[],[f7073])).

fof(f7073,plain,
    ( spl546_7
  <=> m1_yellow_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_7])])).

fof(f7055,plain,
    ( l1_orders_2(sK2)
    | ~ spl546_3 ),
    inference(avatar_component_clause,[],[f7053])).

fof(f7053,plain,
    ( spl546_3
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_3])])).

fof(f7045,plain,
    ( ~ v2_struct_0(sK2)
    | spl546_1 ),
    inference(avatar_component_clause,[],[f7043])).

fof(f7043,plain,
    ( spl546_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_1])])).

fof(f7352,plain,
    ( ~ r2_hidden(k1_yellow_0(sK2,sK4),u1_struct_0(sK3))
    | spl546_1
    | ~ spl546_2
    | ~ spl546_3
    | spl546_4
    | ~ spl546_5
    | ~ spl546_7
    | ~ spl546_9
    | ~ spl546_11
    | spl546_14 ),
    inference(unit_resulting_resolution,[],[f7045,f7050,f7055,f7060,f7065,f7075,f7085,f7095,f7109,f4650])).

fof(f4650,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3203])).

fof(f3203,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3202])).

fof(f3202,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3063])).

fof(f3063,axiom,(
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
             => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & r1_yellow_0(X0,X2) )
               => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                  & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_yellow_0)).

fof(f7109,plain,
    ( k1_yellow_0(sK2,sK4) != k1_yellow_0(sK3,sK4)
    | spl546_14 ),
    inference(avatar_component_clause,[],[f7107])).

fof(f7107,plain,
    ( spl546_14
  <=> k1_yellow_0(sK2,sK4) = k1_yellow_0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_14])])).

fof(f7065,plain,
    ( v4_yellow_0(sK3,sK2)
    | ~ spl546_5 ),
    inference(avatar_component_clause,[],[f7063])).

fof(f7063,plain,
    ( spl546_5
  <=> v4_yellow_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_5])])).

fof(f7060,plain,
    ( ~ v2_struct_0(sK3)
    | spl546_4 ),
    inference(avatar_component_clause,[],[f7058])).

fof(f7058,plain,
    ( spl546_4
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_4])])).

fof(f7050,plain,
    ( v4_orders_2(sK2)
    | ~ spl546_2 ),
    inference(avatar_component_clause,[],[f7048])).

fof(f7048,plain,
    ( spl546_2
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_2])])).

fof(f7336,plain,
    ( spl546_1
    | ~ spl546_2
    | ~ spl546_3
    | spl546_4
    | ~ spl546_5
    | ~ spl546_6
    | ~ spl546_7
    | ~ spl546_8
    | ~ spl546_9
    | spl546_10
    | ~ spl546_11
    | spl546_13 ),
    inference(avatar_contradiction_clause,[],[f7335])).

fof(f7335,plain,
    ( $false
    | spl546_1
    | ~ spl546_2
    | ~ spl546_3
    | spl546_4
    | ~ spl546_5
    | ~ spl546_6
    | ~ spl546_7
    | ~ spl546_8
    | ~ spl546_9
    | spl546_10
    | ~ spl546_11
    | spl546_13 ),
    inference(subsumption_resolution,[],[f7334,f7331])).

fof(f7334,plain,
    ( ~ r2_hidden(k1_yellow_0(sK2,sK4),u1_struct_0(sK3))
    | spl546_1
    | ~ spl546_2
    | ~ spl546_3
    | spl546_4
    | ~ spl546_5
    | ~ spl546_7
    | ~ spl546_9
    | ~ spl546_11
    | spl546_13 ),
    inference(unit_resulting_resolution,[],[f7045,f7050,f7055,f7060,f7065,f7075,f7085,f7105,f7095,f4649])).

fof(f4649,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | r1_yellow_0(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3203])).

fof(f7105,plain,
    ( ~ r1_yellow_0(sK3,sK4)
    | spl546_13 ),
    inference(avatar_component_clause,[],[f7103])).

fof(f7103,plain,
    ( spl546_13
  <=> r1_yellow_0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl546_13])])).

fof(f7110,plain,
    ( ~ spl546_13
    | ~ spl546_14 ),
    inference(avatar_split_clause,[],[f4634,f7107,f7103])).

fof(f4634,plain,
    ( k1_yellow_0(sK2,sK4) != k1_yellow_0(sK3,sK4)
    | ~ r1_yellow_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f3924])).

fof(f3924,plain,
    ( ( k1_yellow_0(sK2,sK4) != k1_yellow_0(sK3,sK4)
      | ~ r1_yellow_0(sK3,sK4) )
    & k1_xboole_0 != sK4
    & r1_yellow_0(sK2,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_waybel_0(sK4,sK3)
    & m1_yellow_0(sK3,sK2)
    & v4_waybel_0(sK3,sK2)
    & v4_yellow_0(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_orders_2(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f3194,f3923,f3922,f3921])).

fof(f3921,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                  | ~ r1_yellow_0(X1,X2) )
                & k1_xboole_0 != X2
                & r1_yellow_0(X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v1_waybel_0(X2,X1) )
            & m1_yellow_0(X1,X0)
            & v4_waybel_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X1,X2) != k1_yellow_0(sK2,X2)
                | ~ r1_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r1_yellow_0(sK2,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v1_waybel_0(X2,X1) )
          & m1_yellow_0(X1,sK2)
          & v4_waybel_0(X1,sK2)
          & v4_yellow_0(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3922,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k1_yellow_0(X1,X2) != k1_yellow_0(sK2,X2)
              | ~ r1_yellow_0(X1,X2) )
            & k1_xboole_0 != X2
            & r1_yellow_0(sK2,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
            & v1_waybel_0(X2,X1) )
        & m1_yellow_0(X1,sK2)
        & v4_waybel_0(X1,sK2)
        & v4_yellow_0(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k1_yellow_0(sK2,X2) != k1_yellow_0(sK3,X2)
            | ~ r1_yellow_0(sK3,X2) )
          & k1_xboole_0 != X2
          & r1_yellow_0(sK2,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
          & v1_waybel_0(X2,sK3) )
      & m1_yellow_0(sK3,sK2)
      & v4_waybel_0(sK3,sK2)
      & v4_yellow_0(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3923,plain,
    ( ? [X2] :
        ( ( k1_yellow_0(sK2,X2) != k1_yellow_0(sK3,X2)
          | ~ r1_yellow_0(sK3,X2) )
        & k1_xboole_0 != X2
        & r1_yellow_0(sK2,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
        & v1_waybel_0(X2,sK3) )
   => ( ( k1_yellow_0(sK2,sK4) != k1_yellow_0(sK3,sK4)
        | ~ r1_yellow_0(sK3,sK4) )
      & k1_xboole_0 != sK4
      & r1_yellow_0(sK2,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      & v1_waybel_0(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3194,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v1_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v4_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3193])).

fof(f3193,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v1_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v4_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3169])).

fof(f3169,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_waybel_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_0(X2,X1) )
               => ( r1_yellow_0(X0,X2)
                 => ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                      & r1_yellow_0(X1,X2) )
                    | k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3168])).

fof(f3168,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_waybel_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v1_waybel_0(X2,X1) )
             => ( r1_yellow_0(X0,X2)
               => ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                    & r1_yellow_0(X1,X2) )
                  | k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_waybel_0)).

fof(f7096,plain,(
    spl546_11 ),
    inference(avatar_split_clause,[],[f4631,f7093])).

fof(f4631,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f3924])).

fof(f7091,plain,(
    ~ spl546_10 ),
    inference(avatar_split_clause,[],[f4633,f7088])).

fof(f4633,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f3924])).

fof(f7086,plain,(
    spl546_9 ),
    inference(avatar_split_clause,[],[f4632,f7083])).

fof(f4632,plain,(
    r1_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f3924])).

fof(f7081,plain,(
    spl546_8 ),
    inference(avatar_split_clause,[],[f4630,f7078])).

fof(f4630,plain,(
    v1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f3924])).

fof(f7076,plain,(
    spl546_7 ),
    inference(avatar_split_clause,[],[f4629,f7073])).

fof(f4629,plain,(
    m1_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f3924])).

fof(f7071,plain,(
    spl546_6 ),
    inference(avatar_split_clause,[],[f4628,f7068])).

fof(f4628,plain,(
    v4_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f3924])).

fof(f7066,plain,(
    spl546_5 ),
    inference(avatar_split_clause,[],[f4627,f7063])).

fof(f4627,plain,(
    v4_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f3924])).

fof(f7061,plain,(
    ~ spl546_4 ),
    inference(avatar_split_clause,[],[f4626,f7058])).

fof(f4626,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3924])).

fof(f7056,plain,(
    spl546_3 ),
    inference(avatar_split_clause,[],[f4625,f7053])).

fof(f4625,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3924])).

fof(f7051,plain,(
    spl546_2 ),
    inference(avatar_split_clause,[],[f4624,f7048])).

fof(f4624,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3924])).

fof(f7046,plain,(
    ~ spl546_1 ),
    inference(avatar_split_clause,[],[f4623,f7043])).

fof(f4623,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3924])).
%------------------------------------------------------------------------------
