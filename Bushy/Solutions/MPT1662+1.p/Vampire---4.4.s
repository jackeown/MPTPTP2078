%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t42_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:50 EDT 2019

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  313 ( 655 expanded)
%              Number of leaves         :   57 ( 224 expanded)
%              Depth                    :   26
%              Number of atoms          : 1543 (3299 expanded)
%              Number of equality atoms :   35 (  97 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1447,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f184,f191,f198,f205,f212,f219,f226,f277,f292,f352,f450,f468,f473,f498,f509,f517,f611,f618,f626,f647,f866,f888,f931,f938,f1145,f1229,f1233,f1243,f1265,f1284,f1289,f1433,f1446])).

fof(f1446,plain,
    ( spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_20
    | spl17_41
    | spl17_151 ),
    inference(avatar_contradiction_clause,[],[f1445])).

fof(f1445,plain,
    ( $false
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_20
    | ~ spl17_41
    | ~ spl17_151 ),
    inference(subsumption_resolution,[],[f1444,f225])).

fof(f225,plain,
    ( v12_waybel_0(sK1,sK0)
    | ~ spl17_12 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl17_12
  <=> v12_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_12])])).

fof(f1444,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_20
    | ~ spl17_41
    | ~ spl17_151 ),
    inference(subsumption_resolution,[],[f1443,f183])).

fof(f183,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl17_1 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl17_1
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f1443,plain,
    ( v1_xboole_0(sK1)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_20
    | ~ spl17_41
    | ~ spl17_151 ),
    inference(subsumption_resolution,[],[f1442,f291])).

fof(f291,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_20 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl17_20
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_20])])).

fof(f1442,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_41
    | ~ spl17_151 ),
    inference(resolution,[],[f1432,f474])).

fof(f474,plain,
    ( ! [X1] :
        ( m1_subset_1(o_2_7_waybel_0(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | ~ v12_waybel_0(X1,sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_41 ),
    inference(subsumption_resolution,[],[f404,f443])).

fof(f443,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl17_41 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl17_41
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_41])])).

fof(f404,plain,
    ( ! [X1] :
        ( ~ v12_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | v1_xboole_0(u1_struct_0(sK0))
        | m1_subset_1(o_2_7_waybel_0(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(duplicate_literal_removal,[],[f403])).

fof(f403,plain,
    ( ! [X1] :
        ( ~ v12_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0))
        | m1_subset_1(o_2_7_waybel_0(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(resolution,[],[f261,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | m1_subset_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
         => m1_subset_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',dt_m2_subset_1)).

fof(f261,plain,
    ( ! [X21] :
        ( m2_subset_1(o_2_7_waybel_0(sK0,X21),u1_struct_0(sK0),X21)
        | ~ v12_waybel_0(X21,sK0)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X21) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f260,f190])).

fof(f190,plain,
    ( v3_orders_2(sK0)
    | ~ spl17_2 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl17_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f260,plain,
    ( ! [X21] :
        ( ~ v3_orders_2(sK0)
        | v1_xboole_0(X21)
        | ~ v12_waybel_0(X21,sK0)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_subset_1(o_2_7_waybel_0(sK0,X21),u1_struct_0(sK0),X21) )
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f259,f211])).

fof(f211,plain,
    ( v1_lattice3(sK0)
    | ~ spl17_8 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl17_8
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_8])])).

fof(f259,plain,
    ( ! [X21] :
        ( ~ v1_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X21)
        | ~ v12_waybel_0(X21,sK0)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_subset_1(o_2_7_waybel_0(sK0,X21),u1_struct_0(sK0),X21) )
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f258,f204])).

fof(f204,plain,
    ( v5_orders_2(sK0)
    | ~ spl17_6 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl17_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).

fof(f258,plain,
    ( ! [X21] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X21)
        | ~ v12_waybel_0(X21,sK0)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_subset_1(o_2_7_waybel_0(sK0,X21),u1_struct_0(sK0),X21) )
    | ~ spl17_4
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f242,f197])).

fof(f197,plain,
    ( v4_orders_2(sK0)
    | ~ spl17_4 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl17_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f242,plain,
    ( ! [X21] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v3_orders_2(sK0)
        | v1_xboole_0(X21)
        | ~ v12_waybel_0(X21,sK0)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_subset_1(o_2_7_waybel_0(sK0,X21),u1_struct_0(sK0),X21) )
    | ~ spl17_10 ),
    inference(resolution,[],[f218,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(X1,X0)
        & ~ v1_xboole_0(X1)
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',dt_o_2_7_waybel_0)).

fof(f218,plain,
    ( l1_orders_2(sK0)
    | ~ spl17_10 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl17_10
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).

fof(f1432,plain,
    ( ~ m1_subset_1(o_2_7_waybel_0(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_151 ),
    inference(avatar_component_clause,[],[f1431])).

fof(f1431,plain,
    ( spl17_151
  <=> ~ m1_subset_1(o_2_7_waybel_0(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_151])])).

fof(f1433,plain,
    ( ~ spl17_151
    | spl17_1
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_20
    | ~ spl17_42
    | ~ spl17_48
    | spl17_59 ),
    inference(avatar_split_clause,[],[f1405,f536,f490,f448,f290,f224,f217,f182,f1431])).

fof(f448,plain,
    ( spl17_42
  <=> ! [X0] :
        ( ~ v12_waybel_0(X0,sK0)
        | m1_subset_1(o_2_7_waybel_0(sK0,X0),X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_42])])).

fof(f490,plain,
    ( spl17_48
  <=> k1_xboole_0 = sK7(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_48])])).

fof(f536,plain,
    ( spl17_59
  <=> ~ sP6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_59])])).

fof(f1405,plain,
    ( ~ m1_subset_1(o_2_7_waybel_0(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_1
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_20
    | ~ spl17_42
    | ~ spl17_48
    | ~ spl17_59 ),
    inference(subsumption_resolution,[],[f1404,f291])).

fof(f1404,plain,
    ( ~ m1_subset_1(o_2_7_waybel_0(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_42
    | ~ spl17_48
    | ~ spl17_59 ),
    inference(subsumption_resolution,[],[f1403,f183])).

fof(f1403,plain,
    ( ~ m1_subset_1(o_2_7_waybel_0(sK0,sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_42
    | ~ spl17_48
    | ~ spl17_59 ),
    inference(subsumption_resolution,[],[f1402,f225])).

fof(f1402,plain,
    ( ~ m1_subset_1(o_2_7_waybel_0(sK0,sK1),u1_struct_0(sK0))
    | ~ v12_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_10
    | ~ spl17_42
    | ~ spl17_48
    | ~ spl17_59 ),
    inference(resolution,[],[f1397,f449])).

fof(f449,plain,
    ( ! [X0] :
        ( m1_subset_1(o_2_7_waybel_0(sK0,X0),X0)
        | ~ v12_waybel_0(X0,sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_42 ),
    inference(avatar_component_clause,[],[f448])).

fof(f1397,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl17_1
    | ~ spl17_10
    | ~ spl17_48
    | ~ spl17_59 ),
    inference(subsumption_resolution,[],[f1396,f183])).

fof(f1396,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X2,sK1) )
    | ~ spl17_10
    | ~ spl17_48
    | ~ spl17_59 ),
    inference(resolution,[],[f1315,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t2_subset)).

fof(f1315,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl17_10
    | ~ spl17_48
    | ~ spl17_59 ),
    inference(subsumption_resolution,[],[f1295,f227])).

fof(f227,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl17_10 ),
    inference(resolution,[],[f218,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_lattice3(X0,k1_xboole_0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t6_yellow_0)).

fof(f1295,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK0,k1_xboole_0,X1)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl17_48
    | ~ spl17_59 ),
    inference(superposition,[],[f955,f491])).

fof(f491,plain,
    ( k1_xboole_0 = sK7(sK0,sK1)
    | ~ spl17_48 ),
    inference(avatar_component_clause,[],[f490])).

fof(f955,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK0,sK7(sK0,sK1),X1)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl17_59 ),
    inference(resolution,[],[f537,f125])).

fof(f125,plain,(
    ! [X0,X3,X1] :
      ( sP6(X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_lattice3(X0,sK7(X0,X1),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r2_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r2_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ? [X3] :
                    ( r2_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t1_waybel_0)).

fof(f537,plain,
    ( ~ sP6(sK1,sK0)
    | ~ spl17_59 ),
    inference(avatar_component_clause,[],[f536])).

fof(f1289,plain,
    ( spl17_49
    | ~ spl17_128 ),
    inference(avatar_contradiction_clause,[],[f1288])).

fof(f1288,plain,
    ( $false
    | ~ spl17_49
    | ~ spl17_128 ),
    inference(subsumption_resolution,[],[f1287,f488])).

fof(f488,plain,
    ( k1_xboole_0 != sK7(sK0,sK1)
    | ~ spl17_49 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl17_49
  <=> k1_xboole_0 != sK7(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_49])])).

fof(f1287,plain,
    ( k1_xboole_0 = sK7(sK0,sK1)
    | ~ spl17_128 ),
    inference(resolution,[],[f1222,f120])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t6_boole)).

fof(f1222,plain,
    ( v1_xboole_0(sK7(sK0,sK1))
    | ~ spl17_128 ),
    inference(avatar_component_clause,[],[f1221])).

fof(f1221,plain,
    ( spl17_128
  <=> v1_xboole_0(sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_128])])).

fof(f1284,plain,
    ( ~ spl17_20
    | spl17_135 ),
    inference(avatar_contradiction_clause,[],[f1283])).

fof(f1283,plain,
    ( $false
    | ~ spl17_20
    | ~ spl17_135 ),
    inference(subsumption_resolution,[],[f1282,f291])).

fof(f1282,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_135 ),
    inference(resolution,[],[f1264,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t3_subset)).

fof(f1264,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl17_135 ),
    inference(avatar_component_clause,[],[f1263])).

fof(f1263,plain,
    ( spl17_135
  <=> ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_135])])).

fof(f1265,plain,
    ( ~ spl17_135
    | spl17_59
    | spl17_133 ),
    inference(avatar_split_clause,[],[f1254,f1241,f536,f1263])).

fof(f1241,plain,
    ( spl17_133
  <=> ~ r1_tarski(sK7(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_133])])).

fof(f1254,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl17_59
    | ~ spl17_133 ),
    inference(subsumption_resolution,[],[f1252,f537])).

fof(f1252,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sP6(sK1,sK0)
    | ~ spl17_133 ),
    inference(resolution,[],[f1248,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),k1_zfmisc_1(X1))
      | sP6(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1248,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(X2))
        | ~ r1_tarski(X2,u1_struct_0(sK0)) )
    | ~ spl17_133 ),
    inference(resolution,[],[f1245,f157])).

fof(f1245,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK7(sK0,sK1),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl17_133 ),
    inference(resolution,[],[f1242,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t1_xboole_1)).

fof(f1242,plain,
    ( ~ r1_tarski(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_133 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f1243,plain,
    ( ~ spl17_133
    | spl17_131 ),
    inference(avatar_split_clause,[],[f1236,f1227,f1241])).

fof(f1227,plain,
    ( spl17_131
  <=> ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_131])])).

fof(f1236,plain,
    ( ~ r1_tarski(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_131 ),
    inference(resolution,[],[f1228,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1228,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_131 ),
    inference(avatar_component_clause,[],[f1227])).

fof(f1233,plain,
    ( spl17_59
    | spl17_127 ),
    inference(avatar_contradiction_clause,[],[f1232])).

fof(f1232,plain,
    ( $false
    | ~ spl17_59
    | ~ spl17_127 ),
    inference(subsumption_resolution,[],[f1230,f537])).

fof(f1230,plain,
    ( sP6(sK1,sK0)
    | ~ spl17_127 ),
    inference(resolution,[],[f1216,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( v1_finset_1(sK7(X0,X1))
      | sP6(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1216,plain,
    ( ~ v1_finset_1(sK7(sK0,sK1))
    | ~ spl17_127 ),
    inference(avatar_component_clause,[],[f1215])).

fof(f1215,plain,
    ( spl17_127
  <=> ~ v1_finset_1(sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_127])])).

fof(f1229,plain,
    ( ~ spl17_127
    | spl17_128
    | ~ spl17_131
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | spl17_25
    | spl17_117 ),
    inference(avatar_split_clause,[],[f1149,f1143,f307,f217,f210,f203,f196,f189,f1227,f1221,f1215])).

fof(f307,plain,
    ( spl17_25
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_25])])).

fof(f1143,plain,
    ( spl17_117
  <=> ~ r2_lattice3(sK0,sK7(sK0,sK1),k1_yellow_0(sK0,sK7(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_117])])).

fof(f1149,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK7(sK0,sK1))
    | ~ v1_finset_1(sK7(sK0,sK1))
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25
    | ~ spl17_117 ),
    inference(resolution,[],[f1144,f372])).

fof(f372,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,X0,k1_yellow_0(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_finset_1(X0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f371,f298])).

fof(f298,plain,
    ( ! [X2] :
        ( ~ r1_yellow_0(sK0,X2)
        | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) )
    | ~ spl17_6
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f297,f204])).

fof(f297,plain,
    ( ! [X2] :
        ( ~ v5_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X2)
        | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) )
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f294,f218])).

fof(f294,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X2)
        | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) )
    | ~ spl17_10 ),
    inference(resolution,[],[f241,f175])).

fof(f175,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,k1_yellow_0(X0,X2)) ) ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow_0(X0,X2) != X1
      | ~ r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t30_yellow_0)).

fof(f241,plain,
    ( ! [X20] : m1_subset_1(k1_yellow_0(sK0,X20),u1_struct_0(sK0))
    | ~ spl17_10 ),
    inference(resolution,[],[f218,f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',dt_k1_yellow_0)).

fof(f371,plain,
    ( ! [X11] :
        ( r1_yellow_0(sK0,X11)
        | ~ v1_finset_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X11) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f253,f308])).

fof(f308,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl17_25 ),
    inference(avatar_component_clause,[],[f307])).

fof(f253,plain,
    ( ! [X11] :
        ( v2_struct_0(sK0)
        | v1_xboole_0(X11)
        | ~ v1_finset_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X11) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f252,f211])).

fof(f252,plain,
    ( ! [X11] :
        ( v2_struct_0(sK0)
        | v1_xboole_0(X11)
        | ~ v1_finset_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X11)
        | ~ v1_lattice3(sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f251,f204])).

fof(f251,plain,
    ( ! [X11] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(X11)
        | ~ v1_finset_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X11)
        | ~ v1_lattice3(sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f250,f197])).

fof(f250,plain,
    ( ! [X11] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(X11)
        | ~ v1_finset_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X11)
        | ~ v1_lattice3(sK0) )
    | ~ spl17_2
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f236,f190])).

fof(f236,plain,
    ( ! [X11] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(X11)
        | ~ v1_finset_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X11)
        | ~ v1_lattice3(sK0) )
    | ~ spl17_10 ),
    inference(resolution,[],[f218,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_yellow_0(X0,X1)
      | ~ v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) )
           => r1_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t54_yellow_0)).

fof(f1144,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0,sK1),k1_yellow_0(sK0,sK7(sK0,sK1)))
    | ~ spl17_117 ),
    inference(avatar_component_clause,[],[f1143])).

fof(f1145,plain,
    ( ~ spl17_117
    | ~ spl17_4
    | ~ spl17_10
    | spl17_15
    | ~ spl17_20
    | spl17_25
    | ~ spl17_50 ),
    inference(avatar_split_clause,[],[f1060,f496,f307,f290,f269,f217,f196,f1143])).

fof(f269,plain,
    ( spl17_15
  <=> ~ v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_15])])).

fof(f496,plain,
    ( spl17_50
  <=> r2_hidden(k1_yellow_0(sK0,sK7(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_50])])).

fof(f1060,plain,
    ( ~ r2_lattice3(sK0,sK7(sK0,sK1),k1_yellow_0(sK0,sK7(sK0,sK1)))
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_50 ),
    inference(subsumption_resolution,[],[f1059,f291])).

fof(f1059,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_lattice3(sK0,sK7(sK0,sK1),k1_yellow_0(sK0,sK7(sK0,sK1)))
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_25
    | ~ spl17_50 ),
    inference(subsumption_resolution,[],[f1055,f270])).

fof(f270,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | ~ spl17_15 ),
    inference(avatar_component_clause,[],[f269])).

fof(f1055,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_lattice3(sK0,sK7(sK0,sK1),k1_yellow_0(sK0,sK7(sK0,sK1)))
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25
    | ~ spl17_50 ),
    inference(resolution,[],[f497,f366])).

fof(f366,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | v1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_lattice3(sK0,sK7(sK0,X0),X1) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f365,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t4_subset)).

fof(f365,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_waybel_0(X0,sK0)
        | ~ r2_hidden(X1,X0)
        | ~ r2_lattice3(sK0,sK7(sK0,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f357,f125])).

fof(f357,plain,
    ( ! [X10] :
        ( ~ sP6(X10,sK0)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_waybel_0(X10,sK0) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f249,f308])).

fof(f249,plain,
    ( ! [X10] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sP6(X10,sK0)
        | v1_waybel_0(X10,sK0) )
    | ~ spl17_4
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f235,f197])).

fof(f235,plain,
    ( ! [X10] :
        ( ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ sP6(X10,sK0)
        | v1_waybel_0(X10,sK0) )
    | ~ spl17_10 ),
    inference(resolution,[],[f218,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP6(X1,X0)
      | v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f497,plain,
    ( r2_hidden(k1_yellow_0(sK0,sK7(sK0,sK1)),sK1)
    | ~ spl17_50 ),
    inference(avatar_component_clause,[],[f496])).

fof(f938,plain,
    ( ~ spl17_18
    | spl17_53 ),
    inference(avatar_contradiction_clause,[],[f937])).

fof(f937,plain,
    ( $false
    | ~ spl17_18
    | ~ spl17_53 ),
    inference(subsumption_resolution,[],[f936,f508])).

fof(f508,plain,
    ( k1_xboole_0 != sK2
    | ~ spl17_53 ),
    inference(avatar_component_clause,[],[f507])).

fof(f507,plain,
    ( spl17_53
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_53])])).

fof(f936,plain,
    ( k1_xboole_0 = sK2
    | ~ spl17_18 ),
    inference(resolution,[],[f281,f120])).

fof(f281,plain,
    ( v1_xboole_0(sK2)
    | ~ spl17_18 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl17_18
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_18])])).

fof(f931,plain,
    ( ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_16
    | spl17_19
    | ~ spl17_20
    | spl17_25
    | ~ spl17_54
    | ~ spl17_58
    | spl17_69
    | ~ spl17_86 ),
    inference(avatar_contradiction_clause,[],[f930])).

fof(f930,plain,
    ( $false
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_16
    | ~ spl17_19
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_54
    | ~ spl17_58
    | ~ spl17_69
    | ~ spl17_86 ),
    inference(subsumption_resolution,[],[f819,f846])).

fof(f846,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_86 ),
    inference(avatar_component_clause,[],[f845])).

fof(f845,plain,
    ( spl17_86
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_86])])).

fof(f819,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_16
    | ~ spl17_19
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_54
    | ~ spl17_58
    | ~ spl17_69 ),
    inference(subsumption_resolution,[],[f818,f516])).

fof(f516,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl17_54 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl17_54
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_54])])).

fof(f818,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_16
    | ~ spl17_19
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58
    | ~ spl17_69 ),
    inference(subsumption_resolution,[],[f817,f625])).

fof(f625,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,sK2),sK1)
    | ~ spl17_69 ),
    inference(avatar_component_clause,[],[f624])).

fof(f624,plain,
    ( spl17_69
  <=> ~ r2_hidden(k1_yellow_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_69])])).

fof(f817,plain,
    ( r2_hidden(k1_yellow_0(sK0,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_16
    | ~ spl17_19
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(subsumption_resolution,[],[f814,f284])).

fof(f284,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl17_19 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl17_19
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_19])])).

fof(f814,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(k1_yellow_0(sK0,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_16
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(resolution,[],[f780,f276])).

fof(f276,plain,
    ( v1_finset_1(sK2)
    | ~ spl17_16 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl17_16
  <=> v1_finset_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_16])])).

fof(f780,plain,
    ( ! [X7] :
        ( ~ v1_finset_1(X7)
        | v1_xboole_0(X7)
        | r2_hidden(k1_yellow_0(sK0,X7),sK1)
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(subsumption_resolution,[],[f779,f225])).

fof(f779,plain,
    ( ! [X7] :
        ( v1_xboole_0(X7)
        | ~ v1_finset_1(X7)
        | r2_hidden(k1_yellow_0(sK0,X7),sK1)
        | ~ v12_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(subsumption_resolution,[],[f775,f291])).

fof(f775,plain,
    ( ! [X7] :
        ( v1_xboole_0(X7)
        | ~ v1_finset_1(X7)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k1_yellow_0(sK0,X7),sK1)
        | ~ v12_waybel_0(sK1,sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(resolution,[],[f736,f540])).

fof(f540,plain,
    ( sP6(sK1,sK0)
    | ~ spl17_58 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl17_58
  <=> sP6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_58])])).

fof(f736,plain,
    ( ! [X4,X3] :
        ( ~ sP6(X4,sK0)
        | v1_xboole_0(X3)
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k1_yellow_0(sK0,X3),X4)
        | ~ v12_waybel_0(X4,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(duplicate_literal_removal,[],[f735])).

fof(f735,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X3)
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k1_yellow_0(sK0,X3),X4)
        | ~ v12_waybel_0(X4,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
        | ~ v1_finset_1(X3)
        | ~ sP6(X4,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
        | ~ v1_finset_1(X3)
        | ~ sP6(X4,sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f680,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,sK8(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X2)
      | ~ sP6(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f680,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_lattice3(sK0,X0,sK8(X1,X2,X3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_finset_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k1_yellow_0(sK0,X0),X2)
        | ~ v12_waybel_0(X2,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
        | ~ v1_finset_1(X3)
        | ~ sP6(X2,X1) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f669,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X2)
      | ~ sP6(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f669,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_hidden(X5,X6)
        | ~ v1_finset_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X4)
        | ~ r2_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k1_yellow_0(sK0,X4),X6)
        | ~ v12_waybel_0(X6,sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f668,f164])).

fof(f668,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ v1_finset_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X4)
        | ~ r2_hidden(X5,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k1_yellow_0(sK0,X4),X6)
        | ~ v12_waybel_0(X6,sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f665,f241])).

fof(f665,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ v1_finset_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(k1_yellow_0(sK0,X4),u1_struct_0(sK0))
        | ~ r2_hidden(X5,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k1_yellow_0(sK0,X4),X6)
        | ~ v12_waybel_0(X6,sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f432,f246])).

fof(f246,plain,
    ( ! [X6,X7,X5] :
        ( ~ r1_orders_2(sK0,X7,X6)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X7,X5)
        | ~ v12_waybel_0(X5,sK0) )
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f232,f164])).

fof(f232,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ r1_orders_2(sK0,X7,X6)
        | r2_hidden(X7,X5)
        | ~ v12_waybel_0(X5,sK0) )
    | ~ spl17_10 ),
    inference(resolution,[],[f218,f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r2_hidden(X3,X1)
      | ~ v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',d19_waybel_0)).

fof(f432,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,k1_yellow_0(sK0,X1),X0)
        | ~ r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_finset_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(resolution,[],[f296,f371])).

fof(f296,plain,
    ( ! [X0,X1] :
        ( ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl17_6
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f295,f204])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f293,f218])).

fof(f293,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl17_10 ),
    inference(resolution,[],[f241,f176])).

fof(f176,plain,(
    ! [X4,X2,X0] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X4)
      | r1_orders_2(X0,k1_yellow_0(X0,X2),X4) ) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow_0(X0,X2) != X1
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X4)
      | r1_orders_2(X0,X1,X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f888,plain,
    ( ~ spl17_20
    | ~ spl17_56
    | spl17_91 ),
    inference(avatar_contradiction_clause,[],[f887])).

fof(f887,plain,
    ( $false
    | ~ spl17_20
    | ~ spl17_56
    | ~ spl17_91 ),
    inference(subsumption_resolution,[],[f884,f291])).

fof(f884,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_56
    | ~ spl17_91 ),
    inference(resolution,[],[f883,f521])).

fof(f521,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl17_56 ),
    inference(avatar_component_clause,[],[f520])).

fof(f520,plain,
    ( spl17_56
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_56])])).

fof(f883,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK2,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_91 ),
    inference(resolution,[],[f877,f157])).

fof(f877,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(sK2,X0) )
    | ~ spl17_91 ),
    inference(resolution,[],[f865,f163])).

fof(f865,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl17_91 ),
    inference(avatar_component_clause,[],[f864])).

fof(f864,plain,
    ( spl17_91
  <=> ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_91])])).

fof(f866,plain,
    ( ~ spl17_91
    | spl17_87 ),
    inference(avatar_split_clause,[],[f854,f848,f864])).

fof(f848,plain,
    ( spl17_87
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_87])])).

fof(f854,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl17_87 ),
    inference(resolution,[],[f849,f156])).

fof(f849,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_87 ),
    inference(avatar_component_clause,[],[f848])).

fof(f647,plain,
    ( spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_20
    | spl17_25
    | spl17_59 ),
    inference(avatar_contradiction_clause,[],[f646])).

fof(f646,plain,
    ( $false
    | ~ spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_59 ),
    inference(subsumption_resolution,[],[f614,f537])).

fof(f614,plain,
    ( sP6(sK1,sK0)
    | ~ spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_20
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f613,f291])).

fof(f613,plain,
    ( sP6(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f612,f183])).

fof(f612,plain,
    ( sP6(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_25 ),
    inference(resolution,[],[f267,f367])).

fof(f367,plain,
    ( ! [X8] :
        ( ~ v1_waybel_0(X8,sK0)
        | sP6(X8,sK0)
        | v1_xboole_0(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f247,f308])).

fof(f247,plain,
    ( ! [X8] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | sP6(X8,sK0)
        | v1_xboole_0(X8)
        | ~ v1_waybel_0(X8,sK0) )
    | ~ spl17_4
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f233,f197])).

fof(f233,plain,
    ( ! [X8] :
        ( ~ v4_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | sP6(X8,sK0)
        | v1_xboole_0(X8)
        | ~ v1_waybel_0(X8,sK0) )
    | ~ spl17_10 ),
    inference(resolution,[],[f218,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP6(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f267,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl17_14 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl17_14
  <=> v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_14])])).

fof(f626,plain,
    ( ~ spl17_69
    | ~ spl17_14 ),
    inference(avatar_split_clause,[],[f619,f266,f624])).

fof(f619,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,sK2),sK1)
    | ~ spl17_14 ),
    inference(subsumption_resolution,[],[f92,f267])).

fof(f92,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,sK2),sK1)
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                    & v1_finset_1(X2) )
                 => ( k1_xboole_0 != X2
                   => r2_hidden(k1_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ( k1_xboole_0 != X2
                 => r2_hidden(k1_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t42_waybel_0)).

fof(f618,plain,
    ( ~ spl17_54
    | spl17_57 ),
    inference(avatar_contradiction_clause,[],[f617])).

fof(f617,plain,
    ( $false
    | ~ spl17_54
    | ~ spl17_57 ),
    inference(subsumption_resolution,[],[f527,f516])).

fof(f527,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl17_57 ),
    inference(resolution,[],[f524,f157])).

fof(f524,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl17_57 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl17_57
  <=> ~ r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_57])])).

fof(f611,plain,
    ( ~ spl17_4
    | ~ spl17_10
    | spl17_15
    | ~ spl17_20
    | spl17_25
    | ~ spl17_58 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(subsumption_resolution,[],[f609,f270])).

fof(f609,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_20
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(subsumption_resolution,[],[f607,f291])).

fof(f607,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_0(sK1,sK0)
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_25
    | ~ spl17_58 ),
    inference(resolution,[],[f540,f357])).

fof(f517,plain,
    ( spl17_54
    | ~ spl17_14 ),
    inference(avatar_split_clause,[],[f510,f266,f515])).

fof(f510,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl17_14 ),
    inference(subsumption_resolution,[],[f90,f267])).

fof(f90,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f509,plain,
    ( ~ spl17_53
    | ~ spl17_14 ),
    inference(avatar_split_clause,[],[f502,f266,f507])).

fof(f502,plain,
    ( k1_xboole_0 != sK2
    | ~ spl17_14 ),
    inference(subsumption_resolution,[],[f91,f267])).

fof(f91,plain,
    ( k1_xboole_0 != sK2
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f498,plain,
    ( spl17_48
    | spl17_50
    | ~ spl17_4
    | ~ spl17_10
    | spl17_15
    | ~ spl17_20
    | spl17_25 ),
    inference(avatar_split_clause,[],[f424,f307,f290,f269,f217,f196,f496,f490])).

fof(f424,plain,
    ( r2_hidden(k1_yellow_0(sK0,sK7(sK0,sK1)),sK1)
    | k1_xboole_0 = sK7(sK0,sK1)
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f423,f270])).

fof(f423,plain,
    ( r2_hidden(k1_yellow_0(sK0,sK7(sK0,sK1)),sK1)
    | k1_xboole_0 = sK7(sK0,sK1)
    | v1_waybel_0(sK1,sK0)
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_20
    | ~ spl17_25 ),
    inference(subsumption_resolution,[],[f421,f291])).

fof(f421,plain,
    ( r2_hidden(k1_yellow_0(sK0,sK7(sK0,sK1)),sK1)
    | k1_xboole_0 = sK7(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_waybel_0(sK1,sK0)
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_15
    | ~ spl17_25 ),
    inference(resolution,[],[f409,f357])).

fof(f409,plain,
    ( ! [X0] :
        ( sP6(sK1,X0)
        | r2_hidden(k1_yellow_0(sK0,sK7(X0,sK1)),sK1)
        | k1_xboole_0 = sK7(X0,sK1) )
    | ~ spl17_15 ),
    inference(duplicate_literal_removal,[],[f407])).

fof(f407,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK7(X0,sK1)
        | r2_hidden(k1_yellow_0(sK0,sK7(X0,sK1)),sK1)
        | sP6(sK1,X0)
        | sP6(sK1,X0) )
    | ~ spl17_15 ),
    inference(resolution,[],[f301,f127])).

fof(f301,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK7(X1,X2),k1_zfmisc_1(sK1))
        | k1_xboole_0 = sK7(X1,X2)
        | r2_hidden(k1_yellow_0(sK0,sK7(X1,X2)),sK1)
        | sP6(X2,X1) )
    | ~ spl17_15 ),
    inference(resolution,[],[f299,f126])).

fof(f299,plain,
    ( ! [X2] :
        ( ~ v1_finset_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
        | k1_xboole_0 = X2
        | r2_hidden(k1_yellow_0(sK0,X2),sK1) )
    | ~ spl17_15 ),
    inference(subsumption_resolution,[],[f93,f270])).

fof(f93,plain,(
    ! [X2] :
      ( ~ v1_finset_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | k1_xboole_0 = X2
      | r2_hidden(k1_yellow_0(sK0,X2),sK1)
      | v1_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f473,plain,
    ( ~ spl17_10
    | spl17_45 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | ~ spl17_10
    | ~ spl17_45 ),
    inference(subsumption_resolution,[],[f471,f218])).

fof(f471,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl17_45 ),
    inference(resolution,[],[f467,f104])).

fof(f104,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',dt_l1_orders_2)).

fof(f467,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl17_45 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl17_45
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_45])])).

fof(f468,plain,
    ( ~ spl17_45
    | spl17_25
    | ~ spl17_40 ),
    inference(avatar_split_clause,[],[f454,f445,f307,f466])).

fof(f445,plain,
    ( spl17_40
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_40])])).

fof(f454,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl17_25
    | ~ spl17_40 ),
    inference(subsumption_resolution,[],[f451,f308])).

fof(f451,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_40 ),
    inference(resolution,[],[f446,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',fc2_struct_0)).

fof(f446,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl17_40 ),
    inference(avatar_component_clause,[],[f445])).

fof(f450,plain,
    ( spl17_40
    | spl17_42
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(avatar_split_clause,[],[f405,f217,f210,f203,f196,f189,f448,f445])).

fof(f405,plain,
    ( ! [X0] :
        ( ~ v12_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | m1_subset_1(o_2_7_waybel_0(sK0,X0),X0)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(duplicate_literal_removal,[],[f402])).

fof(f402,plain,
    ( ! [X0] :
        ( ~ v12_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(o_2_7_waybel_0(sK0,X0),X0)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10 ),
    inference(resolution,[],[f261,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',redefinition_m2_subset_1)).

fof(f352,plain,
    ( ~ spl17_8
    | ~ spl17_10
    | ~ spl17_24 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_24 ),
    inference(subsumption_resolution,[],[f350,f218])).

fof(f350,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl17_8
    | ~ spl17_24 ),
    inference(subsumption_resolution,[],[f349,f211])).

fof(f349,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl17_24 ),
    inference(resolution,[],[f311,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',cc1_lattice3)).

fof(f311,plain,
    ( v2_struct_0(sK0)
    | ~ spl17_24 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl17_24
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_24])])).

fof(f292,plain,(
    spl17_20 ),
    inference(avatar_split_clause,[],[f96,f290])).

fof(f96,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f277,plain,
    ( ~ spl17_15
    | spl17_16 ),
    inference(avatar_split_clause,[],[f89,f275,f269])).

fof(f89,plain,
    ( v1_finset_1(sK2)
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f226,plain,(
    spl17_12 ),
    inference(avatar_split_clause,[],[f95,f224])).

fof(f95,plain,(
    v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f219,plain,(
    spl17_10 ),
    inference(avatar_split_clause,[],[f101,f217])).

fof(f101,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f212,plain,(
    spl17_8 ),
    inference(avatar_split_clause,[],[f100,f210])).

fof(f100,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f205,plain,(
    spl17_6 ),
    inference(avatar_split_clause,[],[f99,f203])).

fof(f99,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f198,plain,(
    spl17_4 ),
    inference(avatar_split_clause,[],[f98,f196])).

fof(f98,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f191,plain,(
    spl17_2 ),
    inference(avatar_split_clause,[],[f97,f189])).

fof(f97,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f184,plain,(
    ~ spl17_1 ),
    inference(avatar_split_clause,[],[f94,f182])).

fof(f94,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
