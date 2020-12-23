%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:29 EST 2020

% Result     : Theorem 0.10s
% Output     : Refutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 231 expanded)
%              Number of leaves         :   30 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  707 (1130 expanded)
%              Number of equality atoms :   55 (  96 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f72,f76,f80,f84,f88,f100,f114,f120,f127,f134,f138,f151,f155,f164,f181,f189,f214,f252,f261])).

fof(f261,plain,
    ( ~ spl6_6
    | ~ spl6_20
    | ~ spl6_34 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_20
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f258,f137])).

fof(f137,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_20
  <=> r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f258,plain,
    ( ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_34 ),
    inference(resolution,[],[f251,f75])).

fof(f75,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_6
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl6_34
  <=> ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f252,plain,
    ( spl6_34
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f225,f212,f153,f70,f66,f62,f58,f54,f250])).

fof(f54,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f58,plain,
    ( spl6_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f62,plain,
    ( spl6_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f66,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f70,plain,
    ( spl6_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f153,plain,
    ( spl6_23
  <=> ! [X1,X3,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | m2_orders_2(X3,X0,X1)
        | ~ r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f212,plain,
    ( spl6_29
  <=> ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f224,f55])).

fof(f55,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f223,f71])).

fof(f71,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f222,f67])).

fof(f67,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f221,f63])).

fof(f63,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f220,f59])).

fof(f59,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(resolution,[],[f213,f154])).

fof(f154,plain,
    ( ! [X0,X3,X1] :
        ( m2_orders_2(X3,X0,X1)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | ~ r2_hidden(X3,k4_orders_2(X0,X1)) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f153])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f212])).

fof(f214,plain,
    ( spl6_29
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f204,f187,f70,f66,f62,f58,f54,f212])).

fof(f187,plain,
    ( spl6_27
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f203,f55])).

fof(f203,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f202,f67])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f201,f63])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f200,f59])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(resolution,[],[f188,f71])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f187])).

fof(f189,plain,
    ( spl6_27
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f183,f179,f149,f132,f187])).

fof(f132,plain,
    ( spl6_19
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X2,X0,X1)
        | v6_orders_2(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f149,plain,
    ( spl6_22
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X2,X0,X1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f179,plain,
    ( spl6_26
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ v6_orders_2(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl6_19
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f182,f150])).

fof(f150,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X2,X0,X1)
        | v2_struct_0(X0) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f149])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl6_19
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f180,f133])).

fof(f133,plain,
    ( ! [X2,X0,X1] :
        ( v6_orders_2(X2,X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X2,X0,X1)
        | v2_struct_0(X0) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f132])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ v6_orders_2(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f179])).

fof(f181,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f50,f179])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v6_orders_2(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(k1_xboole_0,X0,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X2,X0) )
             => ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 ) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

fof(f164,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f162,f55])).

fof(f162,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f161,f75])).

fof(f161,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f160,f71])).

fof(f160,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f159,f67])).

fof(f159,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f158,f63])).

fof(f158,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f157,f59])).

fof(f157,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f156,f83])).

fof(f83,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f156,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(superposition,[],[f119,f123])).

fof(f123,plain,
    ( k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_17
  <=> k1_xboole_0 = k4_orders_2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k4_orders_2(X0,X1))
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_16
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f155,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f51,f153])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X3,X0,X1)
      | ~ r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X3,X0,X1)
      | ~ r2_hidden(X3,X2)
      | k4_orders_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(f151,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f49,f149])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f138,plain,
    ( spl6_17
    | spl6_20
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f130,f125,f86,f136,f122])).

fof(f86,plain,
    ( spl6_9
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK5(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f125,plain,
    ( spl6_18
  <=> k1_xboole_0 = sK5(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f130,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(superposition,[],[f87,f126])).

fof(f126,plain,
    ( k1_xboole_0 = sK5(k4_orders_2(sK0,sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f125])).

fof(f87,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f134,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f48,f132])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | v6_orders_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f127,plain,
    ( spl6_17
    | spl6_18
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f115,f112,f86,f125,f122])).

fof(f112,plain,
    ( spl6_15
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f115,plain,
    ( k1_xboole_0 = sK5(k4_orders_2(sK0,sK1))
    | k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(resolution,[],[f113,f87])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | k1_xboole_0 = X0 )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f112])).

fof(f120,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f47,f118])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f114,plain,
    ( spl6_15
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f102,f98,f78,f112])).

fof(f78,plain,
    ( spl6_7
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f98,plain,
    ( spl6_12
  <=> ! [X0,X2] :
        ( k1_xboole_0 = X2
        | ~ r2_hidden(X2,X0)
        | k1_xboole_0 != k3_tarski(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | k1_xboole_0 = X0 )
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | k1_xboole_0 = X0 )
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(superposition,[],[f99,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f99,plain,
    ( ! [X2,X0] :
        ( k1_xboole_0 != k3_tarski(X0)
        | ~ r2_hidden(X2,X0)
        | k1_xboole_0 = X2 )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f33,f98])).

fof(f33,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 != k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

fof(f88,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f46,f86])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f84,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f30,f82])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f80,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f24,f78])).

fof(f24,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(f76,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f23,f74])).

fof(f23,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.06/0.25  % Computer   : n008.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 18:44:30 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.10/0.34  % (31232)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.10/0.34  % (31228)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.10/0.35  % (31224)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.10/0.35  % (31232)Refutation not found, incomplete strategy% (31232)------------------------------
% 0.10/0.35  % (31232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.35  % (31232)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.35  
% 0.10/0.35  % (31232)Memory used [KB]: 1663
% 0.10/0.35  % (31220)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.10/0.35  % (31232)Time elapsed: 0.044 s
% 0.10/0.35  % (31232)------------------------------
% 0.10/0.35  % (31232)------------------------------
% 0.10/0.35  % (31220)Refutation not found, incomplete strategy% (31220)------------------------------
% 0.10/0.35  % (31220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.35  % (31220)Termination reason: Refutation not found, incomplete strategy
% 0.10/0.35  
% 0.10/0.35  % (31220)Memory used [KB]: 10618
% 0.10/0.35  % (31220)Time elapsed: 0.045 s
% 0.10/0.35  % (31220)------------------------------
% 0.10/0.35  % (31220)------------------------------
% 0.10/0.36  % (31228)Refutation found. Thanks to Tanya!
% 0.10/0.36  % SZS status Theorem for theBenchmark
% 0.10/0.36  % (31230)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.10/0.36  % SZS output start Proof for theBenchmark
% 0.10/0.36  fof(f262,plain,(
% 0.10/0.36    $false),
% 0.10/0.36    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f72,f76,f80,f84,f88,f100,f114,f120,f127,f134,f138,f151,f155,f164,f181,f189,f214,f252,f261])).
% 0.10/0.36  fof(f261,plain,(
% 0.10/0.36    ~spl6_6 | ~spl6_20 | ~spl6_34),
% 0.10/0.36    inference(avatar_contradiction_clause,[],[f260])).
% 0.10/0.36  fof(f260,plain,(
% 0.10/0.36    $false | (~spl6_6 | ~spl6_20 | ~spl6_34)),
% 0.10/0.36    inference(subsumption_resolution,[],[f258,f137])).
% 0.10/0.36  fof(f137,plain,(
% 0.10/0.36    r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | ~spl6_20),
% 0.10/0.36    inference(avatar_component_clause,[],[f136])).
% 0.10/0.36  fof(f136,plain,(
% 0.10/0.36    spl6_20 <=> r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.10/0.36  fof(f258,plain,(
% 0.10/0.36    ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (~spl6_6 | ~spl6_34)),
% 0.10/0.36    inference(resolution,[],[f251,f75])).
% 0.10/0.36  fof(f75,plain,(
% 0.10/0.36    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl6_6),
% 0.10/0.36    inference(avatar_component_clause,[],[f74])).
% 0.10/0.36  fof(f74,plain,(
% 0.10/0.36    spl6_6 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.10/0.36  fof(f251,plain,(
% 0.10/0.36    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | ~spl6_34),
% 0.10/0.36    inference(avatar_component_clause,[],[f250])).
% 0.10/0.36  fof(f250,plain,(
% 0.10/0.36    spl6_34 <=> ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.10/0.36  fof(f252,plain,(
% 0.10/0.36    spl6_34 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_23 | ~spl6_29),
% 0.10/0.36    inference(avatar_split_clause,[],[f225,f212,f153,f70,f66,f62,f58,f54,f250])).
% 0.10/0.36  fof(f54,plain,(
% 0.10/0.36    spl6_1 <=> v2_struct_0(sK0)),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.10/0.36  fof(f58,plain,(
% 0.10/0.36    spl6_2 <=> v3_orders_2(sK0)),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.10/0.36  fof(f62,plain,(
% 0.10/0.36    spl6_3 <=> v4_orders_2(sK0)),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.10/0.36  fof(f66,plain,(
% 0.10/0.36    spl6_4 <=> v5_orders_2(sK0)),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.10/0.36  fof(f70,plain,(
% 0.10/0.36    spl6_5 <=> l1_orders_2(sK0)),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.10/0.36  fof(f153,plain,(
% 0.10/0.36    spl6_23 <=> ! [X1,X3,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1)))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.10/0.36  fof(f212,plain,(
% 0.10/0.36    spl6_29 <=> ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.10/0.36  fof(f225,plain,(
% 0.10/0.36    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_23 | ~spl6_29)),
% 0.10/0.36    inference(subsumption_resolution,[],[f224,f55])).
% 0.10/0.36  fof(f55,plain,(
% 0.10/0.36    ~v2_struct_0(sK0) | spl6_1),
% 0.10/0.36    inference(avatar_component_clause,[],[f54])).
% 0.10/0.36  fof(f224,plain,(
% 0.10/0.36    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_23 | ~spl6_29)),
% 0.10/0.36    inference(subsumption_resolution,[],[f223,f71])).
% 0.10/0.36  fof(f71,plain,(
% 0.10/0.36    l1_orders_2(sK0) | ~spl6_5),
% 0.10/0.36    inference(avatar_component_clause,[],[f70])).
% 0.10/0.36  fof(f223,plain,(
% 0.10/0.36    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_23 | ~spl6_29)),
% 0.10/0.36    inference(subsumption_resolution,[],[f222,f67])).
% 0.10/0.36  fof(f67,plain,(
% 0.10/0.36    v5_orders_2(sK0) | ~spl6_4),
% 0.10/0.36    inference(avatar_component_clause,[],[f66])).
% 0.10/0.36  fof(f222,plain,(
% 0.10/0.36    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (~spl6_2 | ~spl6_3 | ~spl6_23 | ~spl6_29)),
% 0.10/0.36    inference(subsumption_resolution,[],[f221,f63])).
% 0.10/0.36  fof(f63,plain,(
% 0.10/0.36    v4_orders_2(sK0) | ~spl6_3),
% 0.10/0.36    inference(avatar_component_clause,[],[f62])).
% 0.10/0.36  fof(f221,plain,(
% 0.10/0.36    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (~spl6_2 | ~spl6_23 | ~spl6_29)),
% 0.10/0.36    inference(subsumption_resolution,[],[f220,f59])).
% 0.10/0.36  fof(f59,plain,(
% 0.10/0.36    v3_orders_2(sK0) | ~spl6_2),
% 0.10/0.36    inference(avatar_component_clause,[],[f58])).
% 0.10/0.36  fof(f220,plain,(
% 0.10/0.36    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (~spl6_23 | ~spl6_29)),
% 0.10/0.36    inference(duplicate_literal_removal,[],[f219])).
% 0.10/0.36  fof(f219,plain,(
% 0.10/0.36    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (~spl6_23 | ~spl6_29)),
% 0.10/0.36    inference(resolution,[],[f213,f154])).
% 0.10/0.36  fof(f154,plain,(
% 0.10/0.36    ( ! [X0,X3,X1] : (m2_orders_2(X3,X0,X1) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~r2_hidden(X3,k4_orders_2(X0,X1))) ) | ~spl6_23),
% 0.10/0.36    inference(avatar_component_clause,[],[f153])).
% 0.10/0.36  fof(f213,plain,(
% 0.10/0.36    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))) ) | ~spl6_29),
% 0.10/0.36    inference(avatar_component_clause,[],[f212])).
% 0.10/0.36  fof(f214,plain,(
% 0.10/0.36    spl6_29 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_27),
% 0.10/0.36    inference(avatar_split_clause,[],[f204,f187,f70,f66,f62,f58,f54,f212])).
% 0.10/0.36  fof(f187,plain,(
% 0.10/0.36    spl6_27 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.10/0.36  fof(f204,plain,(
% 0.10/0.36    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_27)),
% 0.10/0.36    inference(subsumption_resolution,[],[f203,f55])).
% 0.10/0.36  fof(f203,plain,(
% 0.10/0.36    ( ! [X0] : (v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_27)),
% 0.10/0.36    inference(subsumption_resolution,[],[f202,f67])).
% 0.10/0.36  fof(f202,plain,(
% 0.10/0.36    ( ! [X0] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_27)),
% 0.10/0.36    inference(subsumption_resolution,[],[f201,f63])).
% 0.10/0.36  fof(f201,plain,(
% 0.10/0.36    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl6_2 | ~spl6_5 | ~spl6_27)),
% 0.10/0.36    inference(subsumption_resolution,[],[f200,f59])).
% 0.10/0.36  fof(f200,plain,(
% 0.10/0.36    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl6_5 | ~spl6_27)),
% 0.10/0.36    inference(resolution,[],[f188,f71])).
% 0.10/0.36  fof(f188,plain,(
% 0.10/0.36    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | ~spl6_27),
% 0.10/0.36    inference(avatar_component_clause,[],[f187])).
% 0.10/0.36  fof(f189,plain,(
% 0.10/0.36    spl6_27 | ~spl6_19 | ~spl6_22 | ~spl6_26),
% 0.10/0.36    inference(avatar_split_clause,[],[f183,f179,f149,f132,f187])).
% 0.10/0.36  fof(f132,plain,(
% 0.10/0.36    spl6_19 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v6_orders_2(X2,X0))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.10/0.36  fof(f149,plain,(
% 0.10/0.36    spl6_22 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.10/0.36  fof(f179,plain,(
% 0.10/0.36    spl6_26 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.10/0.36  fof(f183,plain,(
% 0.10/0.36    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | (~spl6_19 | ~spl6_22 | ~spl6_26)),
% 0.10/0.36    inference(subsumption_resolution,[],[f182,f150])).
% 0.10/0.36  fof(f150,plain,(
% 0.10/0.36    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v2_struct_0(X0)) ) | ~spl6_22),
% 0.10/0.36    inference(avatar_component_clause,[],[f149])).
% 0.10/0.36  fof(f182,plain,(
% 0.10/0.36    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | (~spl6_19 | ~spl6_26)),
% 0.10/0.36    inference(subsumption_resolution,[],[f180,f133])).
% 0.10/0.36  fof(f133,plain,(
% 0.10/0.36    ( ! [X2,X0,X1] : (v6_orders_2(X2,X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v2_struct_0(X0)) ) | ~spl6_19),
% 0.10/0.36    inference(avatar_component_clause,[],[f132])).
% 0.10/0.36  fof(f180,plain,(
% 0.10/0.36    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | ~spl6_26),
% 0.10/0.36    inference(avatar_component_clause,[],[f179])).
% 0.10/0.36  fof(f181,plain,(
% 0.10/0.36    spl6_26),
% 0.10/0.36    inference(avatar_split_clause,[],[f50,f179])).
% 0.10/0.36  fof(f50,plain,(
% 0.10/0.36    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) )),
% 0.10/0.36    inference(equality_resolution,[],[f38])).
% 0.10/0.36  fof(f38,plain,(
% 0.10/0.36    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1)) )),
% 0.10/0.36    inference(cnf_transformation,[],[f15])).
% 0.10/0.36  fof(f15,plain,(
% 0.10/0.36    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.10/0.36    inference(flattening,[],[f14])).
% 0.10/0.36  fof(f14,plain,(
% 0.10/0.36    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.10/0.36    inference(ennf_transformation,[],[f3])).
% 0.10/0.36  fof(f3,axiom,(
% 0.10/0.36    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 0.10/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).
% 0.10/0.36  fof(f164,plain,(
% 0.10/0.36    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_16 | ~spl6_17),
% 0.10/0.36    inference(avatar_contradiction_clause,[],[f163])).
% 0.10/0.36  fof(f163,plain,(
% 0.10/0.36    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_16 | ~spl6_17)),
% 0.10/0.36    inference(subsumption_resolution,[],[f162,f55])).
% 0.10/0.36  fof(f162,plain,(
% 0.10/0.36    v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_16 | ~spl6_17)),
% 0.10/0.36    inference(subsumption_resolution,[],[f161,f75])).
% 0.10/0.36  fof(f161,plain,(
% 0.10/0.36    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_16 | ~spl6_17)),
% 0.10/0.36    inference(subsumption_resolution,[],[f160,f71])).
% 0.10/0.36  fof(f160,plain,(
% 0.10/0.36    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_16 | ~spl6_17)),
% 0.10/0.36    inference(subsumption_resolution,[],[f159,f67])).
% 0.10/0.36  fof(f159,plain,(
% 0.10/0.36    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_8 | ~spl6_16 | ~spl6_17)),
% 0.10/0.36    inference(subsumption_resolution,[],[f158,f63])).
% 0.10/0.36  fof(f158,plain,(
% 0.10/0.36    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_8 | ~spl6_16 | ~spl6_17)),
% 0.10/0.36    inference(subsumption_resolution,[],[f157,f59])).
% 0.10/0.36  fof(f157,plain,(
% 0.10/0.36    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_8 | ~spl6_16 | ~spl6_17)),
% 0.10/0.36    inference(subsumption_resolution,[],[f156,f83])).
% 0.10/0.36  fof(f83,plain,(
% 0.10/0.36    v1_xboole_0(k1_xboole_0) | ~spl6_8),
% 0.10/0.36    inference(avatar_component_clause,[],[f82])).
% 0.10/0.36  fof(f82,plain,(
% 0.10/0.36    spl6_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.10/0.36  fof(f156,plain,(
% 0.10/0.36    ~v1_xboole_0(k1_xboole_0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_16 | ~spl6_17)),
% 0.10/0.36    inference(superposition,[],[f119,f123])).
% 0.10/0.36  fof(f123,plain,(
% 0.10/0.36    k1_xboole_0 = k4_orders_2(sK0,sK1) | ~spl6_17),
% 0.10/0.36    inference(avatar_component_clause,[],[f122])).
% 0.10/0.36  fof(f122,plain,(
% 0.10/0.36    spl6_17 <=> k1_xboole_0 = k4_orders_2(sK0,sK1)),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.10/0.36  fof(f119,plain,(
% 0.10/0.36    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl6_16),
% 0.10/0.36    inference(avatar_component_clause,[],[f118])).
% 0.10/0.36  fof(f118,plain,(
% 0.10/0.36    spl6_16 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.10/0.36  fof(f155,plain,(
% 0.10/0.36    spl6_23),
% 0.10/0.36    inference(avatar_split_clause,[],[f51,f153])).
% 0.10/0.36  fof(f51,plain,(
% 0.10/0.36    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.10/0.36    inference(equality_resolution,[],[f41])).
% 0.10/0.36  fof(f41,plain,(
% 0.10/0.36    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.10/0.36    inference(cnf_transformation,[],[f17])).
% 0.10/0.36  fof(f17,plain,(
% 0.10/0.36    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.10/0.36    inference(flattening,[],[f16])).
% 0.10/0.36  fof(f16,plain,(
% 0.10/0.36    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.10/0.36    inference(ennf_transformation,[],[f4])).
% 0.10/0.36  fof(f4,axiom,(
% 0.10/0.36    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.10/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 0.10/0.36  fof(f151,plain,(
% 0.10/0.36    spl6_22),
% 0.10/0.36    inference(avatar_split_clause,[],[f49,f149])).
% 0.10/0.36  fof(f49,plain,(
% 0.10/0.36    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.10/0.36    inference(cnf_transformation,[],[f22])).
% 0.10/0.36  fof(f22,plain,(
% 0.10/0.36    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.10/0.36    inference(flattening,[],[f21])).
% 0.10/0.36  fof(f21,plain,(
% 0.10/0.36    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.10/0.36    inference(ennf_transformation,[],[f5])).
% 0.10/0.36  fof(f5,axiom,(
% 0.10/0.36    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.10/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.10/0.36  fof(f138,plain,(
% 0.10/0.36    spl6_17 | spl6_20 | ~spl6_9 | ~spl6_18),
% 0.10/0.36    inference(avatar_split_clause,[],[f130,f125,f86,f136,f122])).
% 0.10/0.36  fof(f86,plain,(
% 0.10/0.36    spl6_9 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0),X0))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.10/0.36  fof(f125,plain,(
% 0.10/0.36    spl6_18 <=> k1_xboole_0 = sK5(k4_orders_2(sK0,sK1))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.10/0.36  fof(f130,plain,(
% 0.10/0.36    r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = k4_orders_2(sK0,sK1) | (~spl6_9 | ~spl6_18)),
% 0.10/0.36    inference(superposition,[],[f87,f126])).
% 0.10/0.36  fof(f126,plain,(
% 0.10/0.36    k1_xboole_0 = sK5(k4_orders_2(sK0,sK1)) | ~spl6_18),
% 0.10/0.36    inference(avatar_component_clause,[],[f125])).
% 0.10/0.36  fof(f87,plain,(
% 0.10/0.36    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) ) | ~spl6_9),
% 0.10/0.36    inference(avatar_component_clause,[],[f86])).
% 0.10/0.36  fof(f134,plain,(
% 0.10/0.36    spl6_19),
% 0.10/0.36    inference(avatar_split_clause,[],[f48,f132])).
% 0.10/0.36  fof(f48,plain,(
% 0.10/0.36    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v6_orders_2(X2,X0)) )),
% 0.10/0.36    inference(cnf_transformation,[],[f22])).
% 0.10/0.36  fof(f127,plain,(
% 0.10/0.36    spl6_17 | spl6_18 | ~spl6_9 | ~spl6_15),
% 0.10/0.36    inference(avatar_split_clause,[],[f115,f112,f86,f125,f122])).
% 0.10/0.36  fof(f112,plain,(
% 0.10/0.36    spl6_15 <=> ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = X0)),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.10/0.36  fof(f115,plain,(
% 0.10/0.36    k1_xboole_0 = sK5(k4_orders_2(sK0,sK1)) | k1_xboole_0 = k4_orders_2(sK0,sK1) | (~spl6_9 | ~spl6_15)),
% 0.10/0.36    inference(resolution,[],[f113,f87])).
% 0.10/0.36  fof(f113,plain,(
% 0.10/0.36    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = X0) ) | ~spl6_15),
% 0.10/0.36    inference(avatar_component_clause,[],[f112])).
% 0.10/0.36  fof(f120,plain,(
% 0.10/0.36    spl6_16),
% 0.10/0.36    inference(avatar_split_clause,[],[f47,f118])).
% 0.10/0.36  fof(f47,plain,(
% 0.10/0.36    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v1_xboole_0(k4_orders_2(X0,X1))) )),
% 0.10/0.36    inference(cnf_transformation,[],[f20])).
% 0.10/0.36  fof(f20,plain,(
% 0.10/0.36    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.10/0.36    inference(flattening,[],[f19])).
% 0.10/0.36  fof(f19,plain,(
% 0.10/0.36    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.10/0.36    inference(ennf_transformation,[],[f6])).
% 0.10/0.36  fof(f6,axiom,(
% 0.10/0.36    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.10/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).
% 0.10/0.36  fof(f114,plain,(
% 0.10/0.36    spl6_15 | ~spl6_7 | ~spl6_12),
% 0.10/0.36    inference(avatar_split_clause,[],[f102,f98,f78,f112])).
% 0.10/0.36  fof(f78,plain,(
% 0.10/0.36    spl6_7 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.10/0.36  fof(f98,plain,(
% 0.10/0.36    spl6_12 <=> ! [X0,X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,X0) | k1_xboole_0 != k3_tarski(X0))),
% 0.10/0.36    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.10/0.36  fof(f102,plain,(
% 0.10/0.36    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = X0) ) | (~spl6_7 | ~spl6_12)),
% 0.10/0.36    inference(trivial_inequality_removal,[],[f101])).
% 0.10/0.36  fof(f101,plain,(
% 0.10/0.36    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = X0) ) | (~spl6_7 | ~spl6_12)),
% 0.10/0.36    inference(superposition,[],[f99,f79])).
% 0.10/0.36  fof(f79,plain,(
% 0.10/0.36    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl6_7),
% 0.10/0.36    inference(avatar_component_clause,[],[f78])).
% 0.10/0.36  fof(f99,plain,(
% 0.10/0.36    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) ) | ~spl6_12),
% 0.10/0.36    inference(avatar_component_clause,[],[f98])).
% 0.10/0.36  fof(f100,plain,(
% 0.10/0.36    spl6_12),
% 0.10/0.36    inference(avatar_split_clause,[],[f33,f98])).
% 0.10/0.36  fof(f33,plain,(
% 0.10/0.36    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~r2_hidden(X2,X0) | k1_xboole_0 != k3_tarski(X0)) )),
% 0.10/0.36    inference(cnf_transformation,[],[f13])).
% 0.10/0.36  fof(f13,plain,(
% 0.10/0.36    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.10/0.36    inference(ennf_transformation,[],[f10])).
% 0.10/0.36  fof(f10,plain,(
% 0.10/0.36    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.10/0.36    inference(rectify,[],[f7])).
% 0.10/0.36  fof(f7,axiom,(
% 0.10/0.36    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.10/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).
% 0.10/0.36  fof(f88,plain,(
% 0.10/0.36    spl6_9),
% 0.10/0.36    inference(avatar_split_clause,[],[f46,f86])).
% 0.10/0.36  fof(f46,plain,(
% 0.10/0.36    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0),X0)) )),
% 0.10/0.36    inference(cnf_transformation,[],[f18])).
% 0.10/0.36  fof(f18,plain,(
% 0.10/0.36    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.10/0.36    inference(ennf_transformation,[],[f2])).
% 0.10/0.36  fof(f2,axiom,(
% 0.10/0.36    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.10/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.10/0.36  fof(f84,plain,(
% 0.10/0.36    spl6_8),
% 0.10/0.36    inference(avatar_split_clause,[],[f30,f82])).
% 0.10/0.36  fof(f30,plain,(
% 0.10/0.36    v1_xboole_0(k1_xboole_0)),
% 0.10/0.36    inference(cnf_transformation,[],[f1])).
% 0.10/0.36  fof(f1,axiom,(
% 0.10/0.36    v1_xboole_0(k1_xboole_0)),
% 0.10/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.10/0.36  fof(f80,plain,(
% 0.10/0.36    spl6_7),
% 0.10/0.36    inference(avatar_split_clause,[],[f24,f78])).
% 0.10/0.36  fof(f24,plain,(
% 0.10/0.36    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.10/0.36    inference(cnf_transformation,[],[f12])).
% 0.10/0.36  fof(f12,plain,(
% 0.10/0.36    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.10/0.36    inference(flattening,[],[f11])).
% 0.10/0.36  fof(f11,plain,(
% 0.10/0.36    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.10/0.36    inference(ennf_transformation,[],[f9])).
% 0.10/0.36  fof(f9,negated_conjecture,(
% 0.10/0.36    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.10/0.36    inference(negated_conjecture,[],[f8])).
% 0.10/0.36  fof(f8,conjecture,(
% 0.10/0.36    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.10/0.36    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 0.10/0.36  fof(f76,plain,(
% 0.10/0.36    spl6_6),
% 0.10/0.36    inference(avatar_split_clause,[],[f23,f74])).
% 0.10/0.36  fof(f23,plain,(
% 0.10/0.36    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.10/0.36    inference(cnf_transformation,[],[f12])).
% 0.10/0.37  fof(f72,plain,(
% 0.10/0.37    spl6_5),
% 0.10/0.37    inference(avatar_split_clause,[],[f29,f70])).
% 0.10/0.37  fof(f29,plain,(
% 0.10/0.37    l1_orders_2(sK0)),
% 0.10/0.37    inference(cnf_transformation,[],[f12])).
% 0.10/0.37  fof(f68,plain,(
% 0.10/0.37    spl6_4),
% 0.10/0.37    inference(avatar_split_clause,[],[f28,f66])).
% 0.10/0.37  fof(f28,plain,(
% 0.10/0.37    v5_orders_2(sK0)),
% 0.10/0.37    inference(cnf_transformation,[],[f12])).
% 0.10/0.37  fof(f64,plain,(
% 0.10/0.37    spl6_3),
% 0.10/0.37    inference(avatar_split_clause,[],[f27,f62])).
% 0.10/0.37  fof(f27,plain,(
% 0.10/0.37    v4_orders_2(sK0)),
% 0.10/0.37    inference(cnf_transformation,[],[f12])).
% 0.10/0.37  fof(f60,plain,(
% 0.10/0.37    spl6_2),
% 0.10/0.37    inference(avatar_split_clause,[],[f26,f58])).
% 0.10/0.37  fof(f26,plain,(
% 0.10/0.37    v3_orders_2(sK0)),
% 0.10/0.37    inference(cnf_transformation,[],[f12])).
% 0.10/0.37  fof(f56,plain,(
% 0.10/0.37    ~spl6_1),
% 0.10/0.37    inference(avatar_split_clause,[],[f25,f54])).
% 0.10/0.37  fof(f25,plain,(
% 0.10/0.37    ~v2_struct_0(sK0)),
% 0.10/0.37    inference(cnf_transformation,[],[f12])).
% 0.10/0.37  % SZS output end Proof for theBenchmark
% 0.10/0.37  % (31228)------------------------------
% 0.10/0.37  % (31228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.37  % (31228)Termination reason: Refutation
% 0.10/0.37  
% 0.10/0.37  % (31228)Memory used [KB]: 10746
% 0.10/0.37  % (31228)Time elapsed: 0.060 s
% 0.10/0.37  % (31228)------------------------------
% 0.10/0.37  % (31228)------------------------------
% 0.10/0.37  % (31227)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.10/0.37  % (31218)Success in time 0.11 s
%------------------------------------------------------------------------------
