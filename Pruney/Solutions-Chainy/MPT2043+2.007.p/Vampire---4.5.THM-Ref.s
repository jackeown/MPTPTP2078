%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 244 expanded)
%              Number of leaves         :   44 ( 115 expanded)
%              Depth                    :    8
%              Number of atoms          :  534 (1123 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f109,f114,f120,f124,f132,f140,f144,f148,f152,f156,f160,f164,f168,f180,f188,f192,f207,f223,f248,f271,f277,f281])).

fof(f281,plain,
    ( spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_21
    | ~ spl3_30
    | ~ spl3_41 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_21
    | ~ spl3_30
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f236,f278])).

fof(f278,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_21
    | ~ spl3_41 ),
    inference(unit_resulting_resolution,[],[f77,f131,f139,f143,f147,f163,f92,f97,f108,f119,f276])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0)))
        | ~ r2_hidden(k1_xboole_0,X1)
        | ~ v1_subset_1(X1,k9_setfam_1(X0))
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | v1_xboole_0(X1)
        | ~ l1_orders_2(k3_yellow_1(X0))
        | ~ v5_orders_2(k3_yellow_1(X0))
        | ~ v4_orders_2(k3_yellow_1(X0))
        | ~ v3_orders_2(k3_yellow_1(X0))
        | v2_struct_0(k3_yellow_1(X0)) )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl3_41
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k1_xboole_0,X1)
        | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0)))
        | ~ v1_subset_1(X1,k9_setfam_1(X0))
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | v1_xboole_0(X1)
        | ~ l1_orders_2(k3_yellow_1(X0))
        | ~ v5_orders_2(k3_yellow_1(X0))
        | ~ v4_orders_2(k3_yellow_1(X0))
        | ~ v3_orders_2(k3_yellow_1(X0))
        | v2_struct_0(k3_yellow_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f119,plain,
    ( m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_10
  <=> m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f108,plain,
    ( v1_subset_1(sK1,k9_setfam_1(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_8
  <=> v1_subset_1(sK1,k9_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f97,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_6
  <=> v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f92,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_5
  <=> v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f163,plain,
    ( ! [X0] : l1_orders_2(k3_yellow_1(X0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl3_21
  <=> ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f147,plain,
    ( ! [X0] : v5_orders_2(k3_yellow_1(X0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_17
  <=> ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f143,plain,
    ( ! [X0] : v4_orders_2(k3_yellow_1(X0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_16
  <=> ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f139,plain,
    ( ! [X0] : v3_orders_2(k3_yellow_1(X0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl3_15
  <=> ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f131,plain,
    ( ! [X0] : ~ v2_struct_0(k3_yellow_1(X0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_13
  <=> ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f77,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f236,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ spl3_4
    | ~ spl3_30 ),
    inference(superposition,[],[f87,f206])).

fof(f206,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl3_30
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f87,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f277,plain,
    ( spl3_41
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_36
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f272,f269,f246,f186,f166,f275])).

fof(f166,plain,
    ( spl3_22
  <=> ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f186,plain,
    ( spl3_27
  <=> ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f246,plain,
    ( spl3_36
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
        | ~ r2_hidden(k3_yellow_0(X0),X1)
        | ~ v1_subset_1(X1,u1_struct_0(X0))
        | ~ v13_waybel_0(X1,X0)
        | ~ v2_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v1_yellow_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f269,plain,
    ( spl3_40
  <=> ! [X0] : v1_yellow_0(k3_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_xboole_0,X1)
        | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0)))
        | ~ v1_subset_1(X1,k9_setfam_1(X0))
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | v1_xboole_0(X1)
        | ~ l1_orders_2(k3_yellow_1(X0))
        | ~ v5_orders_2(k3_yellow_1(X0))
        | ~ v4_orders_2(k3_yellow_1(X0))
        | ~ v3_orders_2(k3_yellow_1(X0))
        | v2_struct_0(k3_yellow_1(X0)) )
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_36
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f252,f270])).

fof(f270,plain,
    ( ! [X0] : v1_yellow_0(k3_yellow_1(X0))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f269])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_xboole_0,X1)
        | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0)))
        | ~ v1_subset_1(X1,k9_setfam_1(X0))
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | v1_xboole_0(X1)
        | ~ l1_orders_2(k3_yellow_1(X0))
        | ~ v1_yellow_0(k3_yellow_1(X0))
        | ~ v5_orders_2(k3_yellow_1(X0))
        | ~ v4_orders_2(k3_yellow_1(X0))
        | ~ v3_orders_2(k3_yellow_1(X0))
        | v2_struct_0(k3_yellow_1(X0)) )
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f251,f167])).

fof(f167,plain,
    ( ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f166])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0)))
        | ~ r2_hidden(k3_yellow_0(k3_yellow_1(X0)),X1)
        | ~ v1_subset_1(X1,k9_setfam_1(X0))
        | ~ v13_waybel_0(X1,k3_yellow_1(X0))
        | ~ v2_waybel_0(X1,k3_yellow_1(X0))
        | v1_xboole_0(X1)
        | ~ l1_orders_2(k3_yellow_1(X0))
        | ~ v1_yellow_0(k3_yellow_1(X0))
        | ~ v5_orders_2(k3_yellow_1(X0))
        | ~ v4_orders_2(k3_yellow_1(X0))
        | ~ v3_orders_2(k3_yellow_1(X0))
        | v2_struct_0(k3_yellow_1(X0)) )
    | ~ spl3_27
    | ~ spl3_36 ),
    inference(superposition,[],[f247,f187])).

fof(f187,plain,
    ( ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f186])).

fof(f247,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
        | ~ r2_hidden(k3_yellow_0(X0),X1)
        | ~ v1_subset_1(X1,u1_struct_0(X0))
        | ~ v13_waybel_0(X1,X0)
        | ~ v2_waybel_0(X1,X0)
        | v1_xboole_0(X1)
        | ~ l1_orders_2(X0)
        | ~ v1_yellow_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f246])).

fof(f271,plain,
    ( spl3_40
    | ~ spl3_11
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_28
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f240,f221,f190,f158,f154,f150,f122,f269])).

fof(f122,plain,
    ( spl3_11
  <=> ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f150,plain,
    ( spl3_18
  <=> ! [X0] : v13_lattices(k1_lattice3(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f154,plain,
    ( spl3_19
  <=> ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f158,plain,
    ( spl3_20
  <=> ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f190,plain,
    ( spl3_28
  <=> ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f221,plain,
    ( spl3_34
  <=> ! [X0] :
        ( v1_yellow_0(k3_lattice3(X0))
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f240,plain,
    ( ! [X0] : v1_yellow_0(k3_yellow_1(X0))
    | ~ spl3_11
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_28
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f238,f191])).

fof(f191,plain,
    ( ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f190])).

fof(f238,plain,
    ( ! [X0] : v1_yellow_0(k3_lattice3(k1_lattice3(X0)))
    | ~ spl3_11
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_34 ),
    inference(unit_resulting_resolution,[],[f123,f155,f151,f159,f222])).

fof(f222,plain,
    ( ! [X0] :
        ( v1_yellow_0(k3_lattice3(X0))
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f221])).

fof(f159,plain,
    ( ! [X0] : l3_lattices(k1_lattice3(X0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f158])).

fof(f151,plain,
    ( ! [X0] : v13_lattices(k1_lattice3(X0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f150])).

fof(f155,plain,
    ( ! [X0] : v10_lattices(k1_lattice3(X0))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f123,plain,
    ( ! [X0] : ~ v2_struct_0(k1_lattice3(X0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f248,plain,(
    spl3_36 ),
    inference(avatar_split_clause,[],[f68,f246])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ r2_hidden(k3_yellow_0(X0),X1)
      | ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f63,f39])).

fof(f39,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k3_yellow_0(X0),X1)
      | ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_subset_1(X1,u1_struct_0(X0))
              | r2_hidden(k3_yellow_0(X0),X1) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f223,plain,(
    spl3_34 ),
    inference(avatar_split_clause,[],[f62,f221])).

fof(f62,plain,(
    ! [X0] :
      ( v1_yellow_0(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_yellow_0(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_yellow_0(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_yellow_0(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_yellow_1)).

fof(f207,plain,
    ( spl3_30
    | ~ spl3_3
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f193,f178,f80,f204])).

fof(f80,plain,
    ( spl3_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f178,plain,
    ( spl3_25
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f193,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_3
    | ~ spl3_25 ),
    inference(unit_resulting_resolution,[],[f82,f179])).

fof(f179,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f178])).

fof(f82,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f192,plain,(
    spl3_28 ),
    inference(avatar_split_clause,[],[f41,f190])).

fof(f41,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f188,plain,(
    spl3_27 ),
    inference(avatar_split_clause,[],[f40,f186])).

fof(f40,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

fof(f180,plain,(
    spl3_25 ),
    inference(avatar_split_clause,[],[f57,f178])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f168,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f38,f166])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

fof(f164,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f56,f162])).

fof(f56,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(f160,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f54,f158])).

fof(f54,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(f156,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f52,f154])).

fof(f52,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v10_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_lattice3)).

fof(f152,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f49,f150])).

fof(f49,plain,(
    ! [X0] : v13_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k1_xboole_0 = k5_lattices(k1_lattice3(X0))
      & v13_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_lattice3)).

fof(f148,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f48,f146])).

fof(f48,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f144,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f47,f142])).

fof(f47,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f140,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f46,f138])).

fof(f46,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f132,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f44,f130])).

fof(f44,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f124,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f42,f122])).

fof(f42,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).

fof(f120,plain,
    ( spl3_10
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f115,f111,f117])).

fof(f111,plain,
    ( spl3_9
  <=> m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f115,plain,
    ( m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f113,f40])).

fof(f113,plain,
    ( m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f114,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f66,f111])).

fof(f66,plain,(
    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(forward_demodulation,[],[f35,f39])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( v1_xboole_0(sK2)
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    & v13_waybel_0(sK1,k3_yellow_1(sK0))
    & v2_waybel_0(sK1,k3_yellow_1(sK0))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
          & v13_waybel_0(X1,k3_yellow_1(sK0))
          & v2_waybel_0(X1,k3_yellow_1(sK0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( v1_xboole_0(X2)
            & r2_hidden(X2,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
        & v13_waybel_0(X1,k3_yellow_1(sK0))
        & v2_waybel_0(X1,k3_yellow_1(sK0))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( v1_xboole_0(X2)
          & r2_hidden(X2,sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      & v13_waybel_0(sK1,k3_yellow_1(sK0))
      & v2_waybel_0(sK1,k3_yellow_1(sK0))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( v1_xboole_0(X2)
        & r2_hidden(X2,sK1) )
   => ( v1_xboole_0(sK2)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
              & v13_waybel_0(X1,k3_yellow_1(X0))
              & v2_waybel_0(X1,k3_yellow_1(X0))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ~ ( v1_xboole_0(X2)
                  & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(f109,plain,
    ( spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f104,f100,f106])).

fof(f100,plain,
    ( spl3_7
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f104,plain,
    ( v1_subset_1(sK1,k9_setfam_1(sK0))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f102,f40])).

fof(f102,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f103,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f100])).

fof(f32,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f98,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f34,f95])).

fof(f34,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f33,f90])).

fof(f33,plain,(
    v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f36,f85])).

fof(f36,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f80])).

fof(f37,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (9700)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.45  % (9700)Refutation not found, incomplete strategy% (9700)------------------------------
% 0.20/0.45  % (9700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (9700)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (9700)Memory used [KB]: 10618
% 0.20/0.45  % (9700)Time elapsed: 0.042 s
% 0.20/0.45  % (9700)------------------------------
% 0.20/0.45  % (9700)------------------------------
% 0.20/0.46  % (9695)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (9705)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (9693)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (9693)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f282,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f109,f114,f120,f124,f132,f140,f144,f148,f152,f156,f160,f164,f168,f180,f188,f192,f207,f223,f248,f271,f277,f281])).
% 0.20/0.47  fof(f281,plain,(
% 0.20/0.47    spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_8 | ~spl3_10 | ~spl3_13 | ~spl3_15 | ~spl3_16 | ~spl3_17 | ~spl3_21 | ~spl3_30 | ~spl3_41),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f280])).
% 0.20/0.47  fof(f280,plain,(
% 0.20/0.47    $false | (spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_8 | ~spl3_10 | ~spl3_13 | ~spl3_15 | ~spl3_16 | ~spl3_17 | ~spl3_21 | ~spl3_30 | ~spl3_41)),
% 0.20/0.47    inference(subsumption_resolution,[],[f236,f278])).
% 0.20/0.47  fof(f278,plain,(
% 0.20/0.47    ~r2_hidden(k1_xboole_0,sK1) | (spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_8 | ~spl3_10 | ~spl3_13 | ~spl3_15 | ~spl3_16 | ~spl3_17 | ~spl3_21 | ~spl3_41)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f77,f131,f139,f143,f147,f163,f92,f97,f108,f119,f276])).
% 0.20/0.47  fof(f276,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0))) | ~r2_hidden(k1_xboole_0,X1) | ~v1_subset_1(X1,k9_setfam_1(X0)) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | v1_xboole_0(X1) | ~l1_orders_2(k3_yellow_1(X0)) | ~v5_orders_2(k3_yellow_1(X0)) | ~v4_orders_2(k3_yellow_1(X0)) | ~v3_orders_2(k3_yellow_1(X0)) | v2_struct_0(k3_yellow_1(X0))) ) | ~spl3_41),
% 0.20/0.47    inference(avatar_component_clause,[],[f275])).
% 0.20/0.47  fof(f275,plain,(
% 0.20/0.47    spl3_41 <=> ! [X1,X0] : (~r2_hidden(k1_xboole_0,X1) | ~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0))) | ~v1_subset_1(X1,k9_setfam_1(X0)) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | v1_xboole_0(X1) | ~l1_orders_2(k3_yellow_1(X0)) | ~v5_orders_2(k3_yellow_1(X0)) | ~v4_orders_2(k3_yellow_1(X0)) | ~v3_orders_2(k3_yellow_1(X0)) | v2_struct_0(k3_yellow_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) | ~spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f117])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    spl3_10 <=> m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    v1_subset_1(sK1,k9_setfam_1(sK0)) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f106])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl3_8 <=> v1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    v13_waybel_0(sK1,k3_yellow_1(sK0)) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f95])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    spl3_6 <=> v13_waybel_0(sK1,k3_yellow_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    v2_waybel_0(sK1,k3_yellow_1(sK0)) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl3_5 <=> v2_waybel_0(sK1,k3_yellow_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    ( ! [X0] : (l1_orders_2(k3_yellow_1(X0))) ) | ~spl3_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f162])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    spl3_21 <=> ! [X0] : l1_orders_2(k3_yellow_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    ( ! [X0] : (v5_orders_2(k3_yellow_1(X0))) ) | ~spl3_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f146])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    spl3_17 <=> ! [X0] : v5_orders_2(k3_yellow_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    ( ! [X0] : (v4_orders_2(k3_yellow_1(X0))) ) | ~spl3_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f142])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    spl3_16 <=> ! [X0] : v4_orders_2(k3_yellow_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ( ! [X0] : (v3_orders_2(k3_yellow_1(X0))) ) | ~spl3_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f138])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    spl3_15 <=> ! [X0] : v3_orders_2(k3_yellow_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_struct_0(k3_yellow_1(X0))) ) | ~spl3_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f130])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    spl3_13 <=> ! [X0] : ~v2_struct_0(k3_yellow_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ~v1_xboole_0(sK1) | spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    spl3_2 <=> v1_xboole_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f236,plain,(
% 0.20/0.47    r2_hidden(k1_xboole_0,sK1) | (~spl3_4 | ~spl3_30)),
% 0.20/0.47    inference(superposition,[],[f87,f206])).
% 0.20/0.47  fof(f206,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | ~spl3_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f204])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    spl3_30 <=> k1_xboole_0 = sK2),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    r2_hidden(sK2,sK1) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    spl3_4 <=> r2_hidden(sK2,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f277,plain,(
% 0.20/0.47    spl3_41 | ~spl3_22 | ~spl3_27 | ~spl3_36 | ~spl3_40),
% 0.20/0.47    inference(avatar_split_clause,[],[f272,f269,f246,f186,f166,f275])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    spl3_22 <=> ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    spl3_27 <=> ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.47  fof(f246,plain,(
% 0.20/0.47    spl3_36 <=> ! [X1,X0] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.47  fof(f269,plain,(
% 0.20/0.47    spl3_40 <=> ! [X0] : v1_yellow_0(k3_yellow_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.20/0.47  fof(f272,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(k1_xboole_0,X1) | ~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0))) | ~v1_subset_1(X1,k9_setfam_1(X0)) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | v1_xboole_0(X1) | ~l1_orders_2(k3_yellow_1(X0)) | ~v5_orders_2(k3_yellow_1(X0)) | ~v4_orders_2(k3_yellow_1(X0)) | ~v3_orders_2(k3_yellow_1(X0)) | v2_struct_0(k3_yellow_1(X0))) ) | (~spl3_22 | ~spl3_27 | ~spl3_36 | ~spl3_40)),
% 0.20/0.47    inference(subsumption_resolution,[],[f252,f270])).
% 0.20/0.47  fof(f270,plain,(
% 0.20/0.47    ( ! [X0] : (v1_yellow_0(k3_yellow_1(X0))) ) | ~spl3_40),
% 0.20/0.47    inference(avatar_component_clause,[],[f269])).
% 0.20/0.47  fof(f252,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(k1_xboole_0,X1) | ~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0))) | ~v1_subset_1(X1,k9_setfam_1(X0)) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | v1_xboole_0(X1) | ~l1_orders_2(k3_yellow_1(X0)) | ~v1_yellow_0(k3_yellow_1(X0)) | ~v5_orders_2(k3_yellow_1(X0)) | ~v4_orders_2(k3_yellow_1(X0)) | ~v3_orders_2(k3_yellow_1(X0)) | v2_struct_0(k3_yellow_1(X0))) ) | (~spl3_22 | ~spl3_27 | ~spl3_36)),
% 0.20/0.47    inference(forward_demodulation,[],[f251,f167])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))) ) | ~spl3_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f166])).
% 0.20/0.47  fof(f251,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0))) | ~r2_hidden(k3_yellow_0(k3_yellow_1(X0)),X1) | ~v1_subset_1(X1,k9_setfam_1(X0)) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | v1_xboole_0(X1) | ~l1_orders_2(k3_yellow_1(X0)) | ~v1_yellow_0(k3_yellow_1(X0)) | ~v5_orders_2(k3_yellow_1(X0)) | ~v4_orders_2(k3_yellow_1(X0)) | ~v3_orders_2(k3_yellow_1(X0)) | v2_struct_0(k3_yellow_1(X0))) ) | (~spl3_27 | ~spl3_36)),
% 0.20/0.47    inference(superposition,[],[f247,f187])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))) ) | ~spl3_27),
% 0.20/0.47    inference(avatar_component_clause,[],[f186])).
% 0.20/0.47  fof(f247,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) ) | ~spl3_36),
% 0.20/0.47    inference(avatar_component_clause,[],[f246])).
% 0.20/0.47  fof(f271,plain,(
% 0.20/0.47    spl3_40 | ~spl3_11 | ~spl3_18 | ~spl3_19 | ~spl3_20 | ~spl3_28 | ~spl3_34),
% 0.20/0.47    inference(avatar_split_clause,[],[f240,f221,f190,f158,f154,f150,f122,f269])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    spl3_11 <=> ! [X0] : ~v2_struct_0(k1_lattice3(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    spl3_18 <=> ! [X0] : v13_lattices(k1_lattice3(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    spl3_19 <=> ! [X0] : v10_lattices(k1_lattice3(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    spl3_20 <=> ! [X0] : l3_lattices(k1_lattice3(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    spl3_28 <=> ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    spl3_34 <=> ! [X0] : (v1_yellow_0(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.47  fof(f240,plain,(
% 0.20/0.47    ( ! [X0] : (v1_yellow_0(k3_yellow_1(X0))) ) | (~spl3_11 | ~spl3_18 | ~spl3_19 | ~spl3_20 | ~spl3_28 | ~spl3_34)),
% 0.20/0.47    inference(forward_demodulation,[],[f238,f191])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) ) | ~spl3_28),
% 0.20/0.47    inference(avatar_component_clause,[],[f190])).
% 0.20/0.47  fof(f238,plain,(
% 0.20/0.47    ( ! [X0] : (v1_yellow_0(k3_lattice3(k1_lattice3(X0)))) ) | (~spl3_11 | ~spl3_18 | ~spl3_19 | ~spl3_20 | ~spl3_34)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f123,f155,f151,f159,f222])).
% 0.20/0.47  fof(f222,plain,(
% 0.20/0.47    ( ! [X0] : (v1_yellow_0(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl3_34),
% 0.20/0.47    inference(avatar_component_clause,[],[f221])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) ) | ~spl3_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f158])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    ( ! [X0] : (v13_lattices(k1_lattice3(X0))) ) | ~spl3_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f150])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    ( ! [X0] : (v10_lattices(k1_lattice3(X0))) ) | ~spl3_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f154])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) ) | ~spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f122])).
% 0.20/0.47  fof(f248,plain,(
% 0.20/0.47    spl3_36),
% 0.20/0.47    inference(avatar_split_clause,[],[f68,f246])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f63,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0] : (k9_setfam_1(X0) = k1_zfmisc_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(k3_yellow_0(X0),X1)) & (~r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.20/0.47  fof(f223,plain,(
% 0.20/0.47    spl3_34),
% 0.20/0.47    inference(avatar_split_clause,[],[f62,f221])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X0] : (v1_yellow_0(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : ((v1_yellow_0(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : ((v1_yellow_0(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v1_yellow_0(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_yellow_1)).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    spl3_30 | ~spl3_3 | ~spl3_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f193,f178,f80,f204])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl3_3 <=> v1_xboole_0(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    spl3_25 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.47  fof(f193,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | (~spl3_3 | ~spl3_25)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f82,f179])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | ~spl3_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f178])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    v1_xboole_0(sK2) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f80])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    spl3_28),
% 0.20/0.47    inference(avatar_split_clause,[],[f41,f190])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    spl3_27),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f186])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    spl3_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f57,f178])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    spl3_22),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f166])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    spl3_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f56,f162])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (l1_orders_2(k3_yellow_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : (l1_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    spl3_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f54,f158])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    spl3_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f52,f154])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0] : (v10_lattices(k1_lattice3(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : (v10_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_lattice3)).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    spl3_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f49,f150])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0] : (v13_lattices(k1_lattice3(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : (k1_xboole_0 = k5_lattices(k1_lattice3(X0)) & v13_lattices(k1_lattice3(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_lattice3)).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    spl3_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f48,f146])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0] : (v5_orders_2(k3_yellow_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0] : (v5_orders_2(k3_yellow_1(X0)) & v4_orders_2(k3_yellow_1(X0)) & v3_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)) & ~v2_struct_0(k3_yellow_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    spl3_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f47,f142])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0] : (v4_orders_2(k3_yellow_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    spl3_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f46,f138])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0] : (v3_orders_2(k3_yellow_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f44,f130])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_struct_0(k3_yellow_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f42,f122])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    spl3_10 | ~spl3_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f115,f111,f117])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    spl3_9 <=> m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k3_yellow_1(sK0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) | ~spl3_9),
% 0.20/0.47    inference(forward_demodulation,[],[f113,f40])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k3_yellow_1(sK0)))) | ~spl3_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f111])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    spl3_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f66,f111])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k3_yellow_1(sK0))))),
% 0.20/0.47    inference(forward_demodulation,[],[f35,f39])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ((v1_xboole_0(sK2) & r2_hidden(sK2,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) & v13_waybel_0(sK1,k3_yellow_1(sK0)) & v2_waybel_0(sK1,k3_yellow_1(sK0)) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f27,f26,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) & v13_waybel_0(X1,k3_yellow_1(sK0)) & v2_waybel_0(X1,k3_yellow_1(sK0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) & v13_waybel_0(X1,k3_yellow_1(sK0)) & v2_waybel_0(X1,k3_yellow_1(sK0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK0))) & ~v1_xboole_0(X1)) => (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) & v13_waybel_0(sK1,k3_yellow_1(sK0)) & v2_waybel_0(sK1,k3_yellow_1(sK0)) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) & ~v1_xboole_0(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,sK1)) => (v1_xboole_0(sK2) & r2_hidden(sK2,sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f15])).
% 0.20/0.47  fof(f15,conjecture,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    spl3_8 | ~spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f104,f100,f106])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    spl3_7 <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    v1_subset_1(sK1,k9_setfam_1(sK0)) | ~spl3_7),
% 0.20/0.47    inference(forward_demodulation,[],[f102,f40])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f100])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f100])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f95])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    v13_waybel_0(sK1,k3_yellow_1(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f90])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    v2_waybel_0(sK1,k3_yellow_1(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f85])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    r2_hidden(sK2,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f80])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    v1_xboole_0(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f75])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~v1_xboole_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (9693)------------------------------
% 0.20/0.47  % (9693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (9693)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (9693)Memory used [KB]: 6268
% 0.20/0.47  % (9693)Time elapsed: 0.055 s
% 0.20/0.47  % (9693)------------------------------
% 0.20/0.47  % (9693)------------------------------
% 0.20/0.47  % (9702)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (9683)Success in time 0.115 s
%------------------------------------------------------------------------------
