%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 231 expanded)
%              Number of leaves         :   30 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  701 (1124 expanded)
%              Number of equality atoms :   53 (  94 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f272,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f82,f86,f98,f104,f108,f112,f118,f125,f129,f138,f163,f169,f175,f219,f260,f271])).

fof(f271,plain,
    ( ~ spl6_6
    | ~ spl6_21
    | ~ spl6_34 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_21
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f268,f137])).

fof(f137,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_21
  <=> r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f268,plain,
    ( ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_34 ),
    inference(resolution,[],[f259,f73])).

fof(f73,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_6
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl6_34
  <=> ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f260,plain,
    ( spl6_34
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f226,f217,f127,f68,f64,f60,f56,f52,f258])).

fof(f52,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f56,plain,
    ( spl6_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f60,plain,
    ( spl6_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f64,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f68,plain,
    ( spl6_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f127,plain,
    ( spl6_19
  <=> ! [X1,X3,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | m2_orders_2(X3,X0,X1)
        | ~ r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f217,plain,
    ( spl6_30
  <=> ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f225,f53])).

fof(f53,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f224,f69])).

fof(f69,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f223,f65])).

fof(f65,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f222,f61])).

fof(f61,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f221,f57])).

fof(f57,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)) )
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(resolution,[],[f218,f128])).

fof(f128,plain,
    ( ! [X0,X3,X1] :
        ( m2_orders_2(X3,X0,X1)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | ~ r2_hidden(X3,k4_orders_2(X0,X1)) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl6_30
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f181,f173,f68,f64,f60,f56,f52,f217])).

fof(f173,plain,
    ( spl6_24
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f180,f53])).

fof(f180,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f179,f65])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f178,f61])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f177,f57])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl6_5
    | ~ spl6_24 ),
    inference(resolution,[],[f174,f69])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f173])).

fof(f175,plain,
    ( spl6_24
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f171,f167,f116,f110,f173])).

fof(f110,plain,
    ( spl6_15
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X2,X0,X1)
        | v6_orders_2(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f116,plain,
    ( spl6_16
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X2,X0,X1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f167,plain,
    ( spl6_23
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
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f170,f117])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X2,X0,X1)
        | v2_struct_0(X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f116])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m2_orders_2(k1_xboole_0,X0,X1) )
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f168,f111])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( v6_orders_2(X2,X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ m2_orders_2(X2,X0,X1)
        | v2_struct_0(X0) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f110])).

fof(f168,plain,
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
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f167])).

fof(f169,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f48,f167])).

fof(f48,plain,(
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

fof(f163,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f161,f53])).

fof(f161,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f160,f73])).

fof(f160,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f159,f69])).

fof(f159,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f158,f65])).

fof(f158,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f157,f61])).

fof(f157,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f156,f57])).

fof(f156,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f149,f81])).

fof(f81,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f149,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(superposition,[],[f103,f121])).

fof(f121,plain,
    ( k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_17
  <=> k1_xboole_0 = k4_orders_2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k4_orders_2(X0,X1))
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_13
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f138,plain,
    ( spl6_17
    | spl6_21
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f130,f123,f84,f136,f120])).

fof(f84,plain,
    ( spl6_9
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK5(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f123,plain,
    ( spl6_18
  <=> k1_xboole_0 = sK5(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f130,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(superposition,[],[f85,f124])).

fof(f124,plain,
    ( k1_xboole_0 = sK5(k4_orders_2(sK0,sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f123])).

fof(f85,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f129,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f49,f127])).

fof(f49,plain,(
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

fof(f125,plain,
    ( spl6_17
    | spl6_18
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f113,f106,f84,f123,f120])).

fof(f106,plain,
    ( spl6_14
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f113,plain,
    ( k1_xboole_0 = sK5(k4_orders_2(sK0,sK1))
    | k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(resolution,[],[f107,f85])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | k1_xboole_0 = X0 )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f118,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f47,f116])).

fof(f47,plain,(
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

fof(f112,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f46,f110])).

fof(f46,plain,(
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

fof(f108,plain,
    ( spl6_14
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f100,f96,f76,f106])).

fof(f76,plain,
    ( spl6_7
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f96,plain,
    ( spl6_12
  <=> ! [X0,X2] :
        ( k1_xboole_0 = X2
        | ~ r2_hidden(X2,X0)
        | k1_xboole_0 != k3_tarski(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | k1_xboole_0 = X0 )
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
        | k1_xboole_0 = X0 )
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(superposition,[],[f97,f77])).

fof(f77,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f97,plain,
    ( ! [X2,X0] :
        ( k1_xboole_0 != k3_tarski(X0)
        | ~ r2_hidden(X2,X0)
        | k1_xboole_0 = X2 )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f104,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f45,f102])).

fof(f45,plain,(
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

fof(f98,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f33,f96])).

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

fof(f86,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f44,f84])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f82,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f30,f80])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f78,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f24,f76])).

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

fof(f74,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f23,f72])).

fof(f23,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f66,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:44:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.44  % (15029)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.44  % (15022)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.44  % (15037)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.45  % (15030)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.45  % (15029)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f272,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f82,f86,f98,f104,f108,f112,f118,f125,f129,f138,f163,f169,f175,f219,f260,f271])).
% 0.22/0.45  fof(f271,plain,(
% 0.22/0.45    ~spl6_6 | ~spl6_21 | ~spl6_34),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f270])).
% 0.22/0.45  fof(f270,plain,(
% 0.22/0.45    $false | (~spl6_6 | ~spl6_21 | ~spl6_34)),
% 0.22/0.45    inference(subsumption_resolution,[],[f268,f137])).
% 0.22/0.45  fof(f137,plain,(
% 0.22/0.45    r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | ~spl6_21),
% 0.22/0.45    inference(avatar_component_clause,[],[f136])).
% 0.22/0.45  fof(f136,plain,(
% 0.22/0.45    spl6_21 <=> r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.45  fof(f268,plain,(
% 0.22/0.45    ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (~spl6_6 | ~spl6_34)),
% 0.22/0.45    inference(resolution,[],[f259,f73])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl6_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f72])).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    spl6_6 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.45  fof(f259,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | ~spl6_34),
% 0.22/0.45    inference(avatar_component_clause,[],[f258])).
% 0.22/0.45  fof(f258,plain,(
% 0.22/0.45    spl6_34 <=> ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.22/0.45  fof(f260,plain,(
% 0.22/0.45    spl6_34 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_19 | ~spl6_30),
% 0.22/0.45    inference(avatar_split_clause,[],[f226,f217,f127,f68,f64,f60,f56,f52,f258])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    spl6_1 <=> v2_struct_0(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    spl6_2 <=> v3_orders_2(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    spl6_3 <=> v4_orders_2(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    spl6_4 <=> v5_orders_2(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    spl6_5 <=> l1_orders_2(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.45  fof(f127,plain,(
% 0.22/0.45    spl6_19 <=> ! [X1,X3,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.45  fof(f217,plain,(
% 0.22/0.45    spl6_30 <=> ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.45  fof(f226,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_19 | ~spl6_30)),
% 0.22/0.45    inference(subsumption_resolution,[],[f225,f53])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    ~v2_struct_0(sK0) | spl6_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f52])).
% 0.22/0.45  fof(f225,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_19 | ~spl6_30)),
% 0.22/0.45    inference(subsumption_resolution,[],[f224,f69])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    l1_orders_2(sK0) | ~spl6_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f68])).
% 0.22/0.45  fof(f224,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_19 | ~spl6_30)),
% 0.22/0.45    inference(subsumption_resolution,[],[f223,f65])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    v5_orders_2(sK0) | ~spl6_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f64])).
% 0.22/0.45  fof(f223,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (~spl6_2 | ~spl6_3 | ~spl6_19 | ~spl6_30)),
% 0.22/0.45    inference(subsumption_resolution,[],[f222,f61])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    v4_orders_2(sK0) | ~spl6_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f60])).
% 0.22/0.45  fof(f222,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (~spl6_2 | ~spl6_19 | ~spl6_30)),
% 0.22/0.45    inference(subsumption_resolution,[],[f221,f57])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    v3_orders_2(sK0) | ~spl6_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f56])).
% 0.22/0.45  fof(f221,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (~spl6_19 | ~spl6_30)),
% 0.22/0.45    inference(duplicate_literal_removal,[],[f220])).
% 0.22/0.45  fof(f220,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,X0))) ) | (~spl6_19 | ~spl6_30)),
% 0.22/0.45    inference(resolution,[],[f218,f128])).
% 0.22/0.45  fof(f128,plain,(
% 0.22/0.45    ( ! [X0,X3,X1] : (m2_orders_2(X3,X0,X1) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~r2_hidden(X3,k4_orders_2(X0,X1))) ) | ~spl6_19),
% 0.22/0.45    inference(avatar_component_clause,[],[f127])).
% 0.22/0.45  fof(f218,plain,(
% 0.22/0.45    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))) ) | ~spl6_30),
% 0.22/0.45    inference(avatar_component_clause,[],[f217])).
% 0.22/0.45  fof(f219,plain,(
% 0.22/0.45    spl6_30 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_24),
% 0.22/0.45    inference(avatar_split_clause,[],[f181,f173,f68,f64,f60,f56,f52,f217])).
% 0.22/0.45  fof(f173,plain,(
% 0.22/0.45    spl6_24 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.45  fof(f181,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_24)),
% 0.22/0.45    inference(subsumption_resolution,[],[f180,f53])).
% 0.22/0.45  fof(f180,plain,(
% 0.22/0.45    ( ! [X0] : (v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_24)),
% 0.22/0.45    inference(subsumption_resolution,[],[f179,f65])).
% 0.22/0.45  fof(f179,plain,(
% 0.22/0.45    ( ! [X0] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_24)),
% 0.22/0.45    inference(subsumption_resolution,[],[f178,f61])).
% 0.22/0.45  fof(f178,plain,(
% 0.22/0.45    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl6_2 | ~spl6_5 | ~spl6_24)),
% 0.22/0.45    inference(subsumption_resolution,[],[f177,f57])).
% 0.22/0.45  fof(f177,plain,(
% 0.22/0.45    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | (~spl6_5 | ~spl6_24)),
% 0.22/0.45    inference(resolution,[],[f174,f69])).
% 0.22/0.45  fof(f174,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | ~spl6_24),
% 0.22/0.45    inference(avatar_component_clause,[],[f173])).
% 0.22/0.45  fof(f175,plain,(
% 0.22/0.45    spl6_24 | ~spl6_15 | ~spl6_16 | ~spl6_23),
% 0.22/0.45    inference(avatar_split_clause,[],[f171,f167,f116,f110,f173])).
% 0.22/0.45  fof(f110,plain,(
% 0.22/0.45    spl6_15 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v6_orders_2(X2,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.45  fof(f116,plain,(
% 0.22/0.45    spl6_16 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.45  fof(f167,plain,(
% 0.22/0.45    spl6_23 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.45  fof(f171,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | (~spl6_15 | ~spl6_16 | ~spl6_23)),
% 0.22/0.45    inference(subsumption_resolution,[],[f170,f117])).
% 0.22/0.45  fof(f117,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v2_struct_0(X0)) ) | ~spl6_16),
% 0.22/0.45    inference(avatar_component_clause,[],[f116])).
% 0.22/0.45  fof(f170,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | (~spl6_15 | ~spl6_23)),
% 0.22/0.45    inference(subsumption_resolution,[],[f168,f111])).
% 0.22/0.45  fof(f111,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (v6_orders_2(X2,X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v2_struct_0(X0)) ) | ~spl6_15),
% 0.22/0.45    inference(avatar_component_clause,[],[f110])).
% 0.22/0.45  fof(f168,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) ) | ~spl6_23),
% 0.22/0.45    inference(avatar_component_clause,[],[f167])).
% 0.22/0.45  fof(f169,plain,(
% 0.22/0.45    spl6_23),
% 0.22/0.45    inference(avatar_split_clause,[],[f48,f167])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) )),
% 0.22/0.45    inference(equality_resolution,[],[f38])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).
% 0.22/0.45  fof(f163,plain,(
% 0.22/0.45    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_13 | ~spl6_17),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.45  fof(f162,plain,(
% 0.22/0.45    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_13 | ~spl6_17)),
% 0.22/0.45    inference(subsumption_resolution,[],[f161,f53])).
% 0.22/0.45  fof(f161,plain,(
% 0.22/0.45    v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_13 | ~spl6_17)),
% 0.22/0.45    inference(subsumption_resolution,[],[f160,f73])).
% 0.22/0.45  fof(f160,plain,(
% 0.22/0.45    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_13 | ~spl6_17)),
% 0.22/0.45    inference(subsumption_resolution,[],[f159,f69])).
% 0.22/0.45  fof(f159,plain,(
% 0.22/0.45    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_13 | ~spl6_17)),
% 0.22/0.45    inference(subsumption_resolution,[],[f158,f65])).
% 0.22/0.45  fof(f158,plain,(
% 0.22/0.45    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_8 | ~spl6_13 | ~spl6_17)),
% 0.22/0.45    inference(subsumption_resolution,[],[f157,f61])).
% 0.22/0.45  fof(f157,plain,(
% 0.22/0.45    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_8 | ~spl6_13 | ~spl6_17)),
% 0.22/0.45    inference(subsumption_resolution,[],[f156,f57])).
% 0.22/0.45  fof(f156,plain,(
% 0.22/0.45    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_8 | ~spl6_13 | ~spl6_17)),
% 0.22/0.45    inference(subsumption_resolution,[],[f149,f81])).
% 0.22/0.45  fof(f81,plain,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0) | ~spl6_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f80])).
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    spl6_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.45  fof(f149,plain,(
% 0.22/0.45    ~v1_xboole_0(k1_xboole_0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_13 | ~spl6_17)),
% 0.22/0.45    inference(superposition,[],[f103,f121])).
% 0.22/0.45  fof(f121,plain,(
% 0.22/0.45    k1_xboole_0 = k4_orders_2(sK0,sK1) | ~spl6_17),
% 0.22/0.45    inference(avatar_component_clause,[],[f120])).
% 0.22/0.45  fof(f120,plain,(
% 0.22/0.45    spl6_17 <=> k1_xboole_0 = k4_orders_2(sK0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.45  fof(f103,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl6_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f102])).
% 0.22/0.45  fof(f102,plain,(
% 0.22/0.45    spl6_13 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.45  fof(f138,plain,(
% 0.22/0.45    spl6_17 | spl6_21 | ~spl6_9 | ~spl6_18),
% 0.22/0.45    inference(avatar_split_clause,[],[f130,f123,f84,f136,f120])).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    spl6_9 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0),X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.45  fof(f123,plain,(
% 0.22/0.45    spl6_18 <=> k1_xboole_0 = sK5(k4_orders_2(sK0,sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.45  fof(f130,plain,(
% 0.22/0.45    r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = k4_orders_2(sK0,sK1) | (~spl6_9 | ~spl6_18)),
% 0.22/0.45    inference(superposition,[],[f85,f124])).
% 0.22/0.45  fof(f124,plain,(
% 0.22/0.45    k1_xboole_0 = sK5(k4_orders_2(sK0,sK1)) | ~spl6_18),
% 0.22/0.45    inference(avatar_component_clause,[],[f123])).
% 0.22/0.45  fof(f85,plain,(
% 0.22/0.45    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) ) | ~spl6_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f84])).
% 0.22/0.45  fof(f129,plain,(
% 0.22/0.45    spl6_19),
% 0.22/0.45    inference(avatar_split_clause,[],[f49,f127])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.22/0.45    inference(equality_resolution,[],[f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 0.22/0.45  fof(f125,plain,(
% 0.22/0.45    spl6_17 | spl6_18 | ~spl6_9 | ~spl6_14),
% 0.22/0.45    inference(avatar_split_clause,[],[f113,f106,f84,f123,f120])).
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    spl6_14 <=> ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = X0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.45  fof(f113,plain,(
% 0.22/0.45    k1_xboole_0 = sK5(k4_orders_2(sK0,sK1)) | k1_xboole_0 = k4_orders_2(sK0,sK1) | (~spl6_9 | ~spl6_14)),
% 0.22/0.45    inference(resolution,[],[f107,f85])).
% 0.22/0.45  fof(f107,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = X0) ) | ~spl6_14),
% 0.22/0.45    inference(avatar_component_clause,[],[f106])).
% 0.22/0.45  fof(f118,plain,(
% 0.22/0.45    spl6_16),
% 0.22/0.45    inference(avatar_split_clause,[],[f47,f116])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.22/0.45  fof(f112,plain,(
% 0.22/0.45    spl6_15),
% 0.22/0.45    inference(avatar_split_clause,[],[f46,f110])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v6_orders_2(X2,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f108,plain,(
% 0.22/0.45    spl6_14 | ~spl6_7 | ~spl6_12),
% 0.22/0.45    inference(avatar_split_clause,[],[f100,f96,f76,f106])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    spl6_7 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.45  fof(f96,plain,(
% 0.22/0.45    spl6_12 <=> ! [X0,X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,X0) | k1_xboole_0 != k3_tarski(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.45  fof(f100,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = X0) ) | (~spl6_7 | ~spl6_12)),
% 0.22/0.45    inference(trivial_inequality_removal,[],[f99])).
% 0.22/0.45  fof(f99,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = X0) ) | (~spl6_7 | ~spl6_12)),
% 0.22/0.45    inference(superposition,[],[f97,f77])).
% 0.22/0.45  fof(f77,plain,(
% 0.22/0.45    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl6_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f76])).
% 0.22/0.45  fof(f97,plain,(
% 0.22/0.45    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) ) | ~spl6_12),
% 0.22/0.45    inference(avatar_component_clause,[],[f96])).
% 0.22/0.45  fof(f104,plain,(
% 0.22/0.45    spl6_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f45,f102])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v1_xboole_0(k4_orders_2(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    spl6_12),
% 0.22/0.45    inference(avatar_split_clause,[],[f33,f96])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~r2_hidden(X2,X0) | k1_xboole_0 != k3_tarski(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.22/0.45    inference(rectify,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).
% 0.22/0.45  fof(f86,plain,(
% 0.22/0.45    spl6_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f44,f84])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0),X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    spl6_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f30,f80])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    spl6_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f24,f76])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.45    inference(negated_conjecture,[],[f8])).
% 0.22/0.45  fof(f8,conjecture,(
% 0.22/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    spl6_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f72])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    spl6_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f29,f68])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    l1_orders_2(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    spl6_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f28,f64])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    v5_orders_2(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    spl6_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f27,f60])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    v4_orders_2(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    spl6_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f26,f56])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    v3_orders_2(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    ~spl6_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f25,f52])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ~v2_struct_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (15029)------------------------------
% 0.22/0.45  % (15029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (15029)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (15029)Memory used [KB]: 10746
% 0.22/0.45  % (15029)Time elapsed: 0.046 s
% 0.22/0.45  % (15029)------------------------------
% 0.22/0.45  % (15029)------------------------------
% 0.22/0.46  % (15019)Success in time 0.086 s
%------------------------------------------------------------------------------
