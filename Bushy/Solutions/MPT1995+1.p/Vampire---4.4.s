%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t44_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:07 EDT 2019

% Result     : Theorem 17.40s
% Output     : Refutation 17.40s
% Verified   : 
% Statistics : Number of formulae       :  292 (1317 expanded)
%              Number of leaves         :   44 ( 456 expanded)
%              Depth                    :   34
%              Number of atoms          : 2347 (9184 expanded)
%              Number of equality atoms :    8 (  32 expanded)
%              Maximal formula depth    :   22 (   9 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5840,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f215,f222,f226,f233,f240,f247,f254,f261,f268,f275,f282,f289,f417,f437,f457,f458,f1495,f1512,f3542,f3551,f3561,f3724,f3753,f5839])).

fof(f5839,plain,
    ( spl15_6
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | spl15_45
    | ~ spl15_72 ),
    inference(avatar_split_clause,[],[f5838,f1493,f404,f287,f280,f273,f266,f259,f252,f245,f238,f231,f224])).

fof(f224,plain,
    ( spl15_6
  <=> ! [X3] :
        ( v2_waybel_0(k6_waybel_4(sK0,X3,sK1),sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f231,plain,
    ( spl15_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f238,plain,
    ( spl15_10
  <=> v5_waybel_4(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_10])])).

fof(f245,plain,
    ( spl15_12
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).

fof(f252,plain,
    ( spl15_14
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f259,plain,
    ( spl15_16
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f266,plain,
    ( spl15_18
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f273,plain,
    ( spl15_20
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).

fof(f280,plain,
    ( spl15_22
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).

fof(f287,plain,
    ( spl15_24
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_24])])).

fof(f404,plain,
    ( spl15_45
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_45])])).

fof(f1493,plain,
    ( spl15_72
  <=> ! [X22,X21,X23] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X21,X22),sK1)
        | r2_hidden(k4_tarski(X21,k11_lattice3(sK0,X23,X22)),sK1)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | ~ m1_subset_1(X22,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X21,X23),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_72])])).

fof(f5838,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5837,f1109])).

fof(f1109,plain,
    ( ! [X1] :
        ( m1_subset_1(sK3(sK0,k6_waybel_4(sK0,X1,sK1)),u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(duplicate_literal_removal,[],[f1105])).

fof(f1105,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | m1_subset_1(sK3(sK0,k6_waybel_4(sK0,X1,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(resolution,[],[f1093,f511])).

fof(f511,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k6_waybel_4(sK0,X4,sK1))
        | m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_45 ),
    inference(resolution,[],[f506,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t44_waybel_7.p',t4_subset)).

fof(f506,plain,
    ( ! [X2] :
        ( m1_subset_1(k6_waybel_4(sK0,X2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f505,f405])).

fof(f405,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl15_45 ),
    inference(avatar_component_clause,[],[f404])).

fof(f505,plain,
    ( ! [X2] :
        ( m1_subset_1(k6_waybel_4(sK0,X2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl15_8
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f500,f246])).

fof(f246,plain,
    ( l1_orders_2(sK0)
    | ~ spl15_12 ),
    inference(avatar_component_clause,[],[f245])).

fof(f500,plain,
    ( ! [X2] :
        ( m1_subset_1(k6_waybel_4(sK0,X2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_8 ),
    inference(resolution,[],[f157,f232])).

fof(f232,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl15_8 ),
    inference(avatar_component_clause,[],[f231])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(k6_waybel_4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k6_waybel_4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k6_waybel_4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_waybel_4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t44_waybel_7.p',dt_k6_waybel_4)).

fof(f1093,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK0,k6_waybel_4(sK0,X1,sK1)),k6_waybel_4(sK0,X1,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f519,f635])).

fof(f635,plain,
    ( ! [X2] :
        ( v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24 ),
    inference(subsumption_resolution,[],[f634,f288])).

fof(f288,plain,
    ( v3_orders_2(sK0)
    | ~ spl15_24 ),
    inference(avatar_component_clause,[],[f287])).

fof(f634,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22 ),
    inference(subsumption_resolution,[],[f633,f281])).

fof(f281,plain,
    ( v4_orders_2(sK0)
    | ~ spl15_22 ),
    inference(avatar_component_clause,[],[f280])).

fof(f633,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f632,f274])).

fof(f274,plain,
    ( v5_orders_2(sK0)
    | ~ spl15_20 ),
    inference(avatar_component_clause,[],[f273])).

fof(f632,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_18 ),
    inference(subsumption_resolution,[],[f631,f267])).

fof(f267,plain,
    ( v1_yellow_0(sK0)
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f266])).

fof(f631,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_16 ),
    inference(subsumption_resolution,[],[f630,f260])).

fof(f260,plain,
    ( v1_lattice3(sK0)
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f259])).

fof(f630,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ v1_lattice3(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f629,f246])).

fof(f629,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_10 ),
    inference(subsumption_resolution,[],[f624,f239])).

fof(f239,plain,
    ( v5_waybel_4(sK1,sK0)
    | ~ spl15_10 ),
    inference(avatar_component_clause,[],[f238])).

fof(f624,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ v5_waybel_4(sK1,sK0)
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8 ),
    inference(resolution,[],[f156,f232])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v13_waybel_0(k6_waybel_4(X0,X2,X1),X0)
      | ~ v5_waybel_4(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v13_waybel_0(k6_waybel_4(X0,X2,X1),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v5_waybel_4(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v13_waybel_0(k6_waybel_4(X0,X2,X1),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v5_waybel_4(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v5_waybel_4(X1,X0)
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => v13_waybel_0(k6_waybel_4(X0,X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t44_waybel_7.p',fc3_waybel_7)).

fof(f519,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,k6_waybel_4(sK0,X1,sK1)),k6_waybel_4(sK0,X1,sK1))
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_20
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f518,f274])).

fof(f518,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,k6_waybel_4(sK0,X1,sK1)),k6_waybel_4(sK0,X1,sK1))
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f517,f253])).

fof(f253,plain,
    ( v2_lattice3(sK0)
    | ~ spl15_14 ),
    inference(avatar_component_clause,[],[f252])).

fof(f517,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,k6_waybel_4(sK0,X1,sK1)),k6_waybel_4(sK0,X1,sK1))
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f508,f246])).

fof(f508,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,k6_waybel_4(sK0,X1,sK1)),k6_waybel_4(sK0,X1,sK1))
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_45 ),
    inference(resolution,[],[f506,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK3(X0,X1),X1)
      | v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ( ~ r2_hidden(k12_lattice3(X0,sK3(X0,X1),sK4(X0,X1)),X1)
                & r2_hidden(sK4(X0,X1),X1)
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f101,f103,f102])).

fof(f102,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k12_lattice3(X0,sK3(X0,X1),X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(sK3(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k12_lattice3(X0,X2,sK4(X0,X1)),X1)
        & r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      | ~ r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t44_waybel_7.p',t41_waybel_0)).

fof(f5837,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(sK3(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5836,f1110])).

fof(f1110,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(duplicate_literal_removal,[],[f1104])).

fof(f1104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(resolution,[],[f1093,f647])).

fof(f647,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k6_waybel_4(sK0,X4,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X4,X3),sK1) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24 ),
    inference(subsumption_resolution,[],[f646,f288])).

fof(f646,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k6_waybel_4(sK0,X4,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X4,X3),sK1)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22 ),
    inference(subsumption_resolution,[],[f645,f281])).

fof(f645,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k6_waybel_4(sK0,X4,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X4,X3),sK1)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f644,f274])).

fof(f644,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k6_waybel_4(sK0,X4,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X4,X3),sK1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16 ),
    inference(subsumption_resolution,[],[f643,f260])).

fof(f643,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k6_waybel_4(sK0,X4,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X4,X3),sK1)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f638,f246])).

fof(f638,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k6_waybel_4(sK0,X4,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X4,X3),sK1)
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8 ),
    inference(resolution,[],[f158,f232])).

fof(f158,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
      | ~ r2_hidden(X0,k6_waybel_4(X1,X3,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(k4_tarski(X3,X0),X2)
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( ( r2_hidden(X0,k6_waybel_4(X1,X3,X2))
                  | ~ r2_hidden(k4_tarski(X3,X0),X2) )
                & ( r2_hidden(k4_tarski(X3,X0),X2)
                  | ~ r2_hidden(X0,k6_waybel_4(X1,X3,X2)) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) )
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r2_hidden(X0,k6_waybel_4(X1,X3,X2))
              <=> r2_hidden(k4_tarski(X3,X0),X2) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) )
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r2_hidden(X0,k6_waybel_4(X1,X3,X2))
              <=> r2_hidden(k4_tarski(X3,X0),X2) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) )
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( l1_orders_2(X1)
        & v1_lattice3(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X0,k6_waybel_4(X1,X3,X2))
              <=> r2_hidden(k4_tarski(X3,X0),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t44_waybel_7.p',t14_waybel_4)).

fof(f5836,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(sK3(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5835,f405])).

fof(f5835,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(sK3(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5834,f246])).

fof(f5834,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(sK3(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(duplicate_literal_removal,[],[f5833])).

fof(f5833,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(sK3(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(superposition,[],[f5832,f194])).

fof(f194,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_yellow_3(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_yellow_3(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_yellow_3(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X1))
        & m1_subset_1(X2,u1_struct_0(X0))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k7_yellow_3(X0,X1,X2,X3) = k4_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t44_waybel_7.p',redefinition_k7_yellow_3)).

fof(f5832,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5831,f932])).

fof(f932,plain,
    ( ! [X1] :
        ( m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X1,sK1)),u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(duplicate_literal_removal,[],[f928])).

fof(f928,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X1,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(resolution,[],[f924,f511])).

fof(f924,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),k6_waybel_4(sK0,X0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f516,f635])).

fof(f516,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),k6_waybel_4(sK0,X0,sK1))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_20
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f515,f274])).

fof(f515,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),k6_waybel_4(sK0,X0,sK1))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f514,f253])).

fof(f514,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),k6_waybel_4(sK0,X0,sK1))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f507,f246])).

fof(f507,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),k6_waybel_4(sK0,X0,sK1))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_45 ),
    inference(resolution,[],[f506,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1),X1)
      | v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f5831,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5830,f933])).

fof(f933,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(duplicate_literal_removal,[],[f927])).

fof(f927,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(resolution,[],[f924,f647])).

fof(f5830,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5829,f405])).

fof(f5829,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5828,f246])).

fof(f5828,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(duplicate_literal_removal,[],[f5827])).

fof(f5827,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(superposition,[],[f5185,f194])).

fof(f5185,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5184,f635])).

fof(f5184,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5183,f506])).

fof(f5183,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5182,f932])).

fof(f5182,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5181,f1109])).

fof(f5181,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5180,f274])).

fof(f5180,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5179,f253])).

fof(f5179,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f5178,f246])).

fof(f5178,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_72 ),
    inference(duplicate_literal_removal,[],[f5162])).

fof(f5162,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK4(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK3(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_72 ),
    inference(resolution,[],[f3839,f671])).

fof(f671,plain,
    ( ! [X12,X11] :
        ( ~ r2_hidden(k4_tarski(X11,k12_lattice3(X12,sK3(X12,k6_waybel_4(sK0,X11,sK1)),sK4(X12,k6_waybel_4(sK0,X11,sK1)))),sK1)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X11,sK1),X12)
        | ~ m1_subset_1(k6_waybel_4(sK0,X11,sK1),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X11,sK1),X12)
        | ~ l1_orders_2(X12)
        | ~ v2_lattice3(X12)
        | ~ v5_orders_2(X12) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24 ),
    inference(resolution,[],[f658,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k12_lattice3(X0,sK3(X0,X1),sK4(X0,X1)),X1)
      | v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f658,plain,
    ( ! [X4,X3] :
        ( r2_hidden(X4,k6_waybel_4(sK0,X3,sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(k4_tarski(X3,X4),sK1) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24 ),
    inference(subsumption_resolution,[],[f657,f288])).

fof(f657,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X4,k6_waybel_4(sK0,X3,sK1))
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22 ),
    inference(subsumption_resolution,[],[f656,f281])).

fof(f656,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X4,k6_waybel_4(sK0,X3,sK1))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f655,f274])).

fof(f655,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X4,k6_waybel_4(sK0,X3,sK1))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16 ),
    inference(subsumption_resolution,[],[f654,f260])).

fof(f654,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X4,k6_waybel_4(sK0,X3,sK1))
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f649,f246])).

fof(f649,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X4,k6_waybel_4(sK0,X3,sK1))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl15_8 ),
    inference(resolution,[],[f159,f232])).

fof(f159,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(X0,k6_waybel_4(X1,X3,X2))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f3839,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X2,k12_lattice3(sK0,X0,X1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X1),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X0),sK1) )
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_20
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f3838,f274])).

fof(f3838,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X2,k12_lattice3(sK0,X0,X1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X1),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X0),sK1)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f3837,f253])).

fof(f3837,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X2,k12_lattice3(sK0,X0,X1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X1),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X0),sK1)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_12
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f3834,f246])).

fof(f3834,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X2,k12_lattice3(sK0,X0,X1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X1),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X0),sK1)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_72 ),
    inference(duplicate_literal_removal,[],[f3833])).

fof(f3833,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X2,k12_lattice3(sK0,X0,X1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X1),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,X0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl15_72 ),
    inference(superposition,[],[f1494,f183])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t44_waybel_7.p',redefinition_k12_lattice3)).

fof(f1494,plain,
    ( ! [X23,X21,X22] :
        ( r2_hidden(k4_tarski(X21,k11_lattice3(sK0,X23,X22)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X21,X22),sK1)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | ~ m1_subset_1(X22,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X21,X23),sK1) )
    | ~ spl15_72 ),
    inference(avatar_component_clause,[],[f1493])).

fof(f3753,plain,
    ( spl15_1
    | ~ spl15_8
    | ~ spl15_12
    | spl15_45
    | spl15_125 ),
    inference(avatar_contradiction_clause,[],[f3752])).

fof(f3752,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_45
    | ~ spl15_125 ),
    inference(subsumption_resolution,[],[f3751,f405])).

fof(f3751,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_1
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_125 ),
    inference(subsumption_resolution,[],[f3750,f246])).

fof(f3750,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_1
    | ~ spl15_8
    | ~ spl15_125 ),
    inference(subsumption_resolution,[],[f3749,f232])).

fof(f3749,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_1
    | ~ spl15_125 ),
    inference(subsumption_resolution,[],[f3747,f208])).

fof(f208,plain,
    ( ~ v5_waybel_7(sK1,sK0)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl15_1
  <=> ~ v5_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f3747,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_125 ),
    inference(resolution,[],[f3723,f546])).

fof(f546,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK10(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f545,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | v5_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_7(X1,X0)
              | ( ~ r2_hidden(k7_yellow_3(X0,X0,sK8(X0,X1),k11_lattice3(X0,sK9(X0,X1),sK10(X0,X1))),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK8(X0,X1),sK10(X0,X1)),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK8(X0,X1),sK9(X0,X1)),X1)
                & m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ! [X7] :
                          ( r2_hidden(k7_yellow_3(X0,X0,X5,k11_lattice3(X0,X6,X7)),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X7),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X6),X1)
                          | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f113,f116,f115,f114])).

fof(f114,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                  & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                  & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(k7_yellow_3(X0,X0,sK8(X0,X1),k11_lattice3(X0,X3,X4)),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK8(X0,X1),X4),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK8(X0,X1),X3),X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f115,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
              & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
              & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,sK9(X0,X1),X4)),X1)
            & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
            & r2_hidden(k7_yellow_3(X0,X0,X2,sK9(X0,X1)),X1)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f116,plain,(
    ! [X2,X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
          & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
          & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,sK10(X0,X1))),X1)
        & r2_hidden(k7_yellow_3(X0,X0,X2,sK10(X0,X1)),X1)
        & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f113,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ! [X7] :
                          ( r2_hidden(k7_yellow_3(X0,X0,X5,k11_lattice3(X0,X6,X7)),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X7),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X6),X1)
                          | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ! [X4] :
                          ( r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1) )
                         => r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t44_waybel_7.p',d7_waybel_7)).

fof(f545,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK10(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f544,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | v5_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f544,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK10(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f543])).

fof(f543,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK10(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f165,f194])).

fof(f165,plain,(
    ! [X0,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,sK8(X0,X1),sK10(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f3723,plain,
    ( ~ r2_hidden(k4_tarski(sK8(sK0,sK1),sK10(sK0,sK1)),sK1)
    | ~ spl15_125 ),
    inference(avatar_component_clause,[],[f3722])).

fof(f3722,plain,
    ( spl15_125
  <=> ~ r2_hidden(k4_tarski(sK8(sK0,sK1),sK10(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_125])])).

fof(f3724,plain,
    ( ~ spl15_125
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_46
    | spl15_107 ),
    inference(avatar_split_clause,[],[f3717,f3540,f413,f287,f280,f273,f259,f245,f231,f3722])).

fof(f413,plain,
    ( spl15_46
  <=> m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_46])])).

fof(f3540,plain,
    ( spl15_107
  <=> ~ r2_hidden(sK10(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_107])])).

fof(f3717,plain,
    ( ~ r2_hidden(k4_tarski(sK8(sK0,sK1),sK10(sK0,sK1)),sK1)
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_46
    | ~ spl15_107 ),
    inference(subsumption_resolution,[],[f3716,f414])).

fof(f414,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl15_46 ),
    inference(avatar_component_clause,[],[f413])).

fof(f3716,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(sK8(sK0,sK1),sK10(sK0,sK1)),sK1)
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_107 ),
    inference(resolution,[],[f3541,f658])).

fof(f3541,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ spl15_107 ),
    inference(avatar_component_clause,[],[f3540])).

fof(f3561,plain,
    ( spl15_1
    | ~ spl15_8
    | ~ spl15_12
    | spl15_45
    | spl15_109 ),
    inference(avatar_contradiction_clause,[],[f3560])).

fof(f3560,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_45
    | ~ spl15_109 ),
    inference(subsumption_resolution,[],[f3559,f405])).

fof(f3559,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_1
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_109 ),
    inference(subsumption_resolution,[],[f3558,f246])).

fof(f3558,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_1
    | ~ spl15_8
    | ~ spl15_109 ),
    inference(subsumption_resolution,[],[f3557,f232])).

fof(f3557,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_1
    | ~ spl15_109 ),
    inference(subsumption_resolution,[],[f3555,f208])).

fof(f3555,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_109 ),
    inference(resolution,[],[f3550,f539])).

fof(f539,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f538,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | v5_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f538,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f537,f161])).

fof(f537,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f536])).

fof(f536,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f164,f194])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,sK8(X0,X1),sK9(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f3550,plain,
    ( ~ r2_hidden(k4_tarski(sK8(sK0,sK1),sK9(sK0,sK1)),sK1)
    | ~ spl15_109 ),
    inference(avatar_component_clause,[],[f3549])).

fof(f3549,plain,
    ( spl15_109
  <=> ~ r2_hidden(k4_tarski(sK8(sK0,sK1),sK9(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_109])])).

fof(f3551,plain,
    ( ~ spl15_109
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_46
    | spl15_105 ),
    inference(avatar_split_clause,[],[f3544,f3534,f413,f287,f280,f273,f259,f245,f231,f3549])).

fof(f3534,plain,
    ( spl15_105
  <=> ~ r2_hidden(sK9(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_105])])).

fof(f3544,plain,
    ( ~ r2_hidden(k4_tarski(sK8(sK0,sK1),sK9(sK0,sK1)),sK1)
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_46
    | ~ spl15_105 ),
    inference(subsumption_resolution,[],[f3543,f414])).

fof(f3543,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(sK8(sK0,sK1),sK9(sK0,sK1)),sK1)
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_105 ),
    inference(resolution,[],[f3535,f658])).

fof(f3535,plain,
    ( ~ r2_hidden(sK9(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ spl15_105 ),
    inference(avatar_component_clause,[],[f3534])).

fof(f3542,plain,
    ( ~ spl15_105
    | ~ spl15_107
    | spl15_1
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | spl15_45
    | ~ spl15_46
    | ~ spl15_52
    | ~ spl15_74 ),
    inference(avatar_split_clause,[],[f3529,f1503,f452,f413,f404,f287,f280,f273,f266,f259,f252,f245,f238,f231,f224,f207,f3540,f3534])).

fof(f452,plain,
    ( spl15_52
  <=> m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_52])])).

fof(f1503,plain,
    ( spl15_74
  <=> m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_74])])).

fof(f3529,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ r2_hidden(sK9(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ spl15_1
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_46
    | ~ spl15_52
    | ~ spl15_74 ),
    inference(subsumption_resolution,[],[f3528,f414])).

fof(f3528,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK9(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ spl15_1
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_52
    | ~ spl15_74 ),
    inference(subsumption_resolution,[],[f3527,f274])).

fof(f3527,plain,
    ( ~ v5_orders_2(sK0)
    | ~ r2_hidden(sK10(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK9(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ spl15_1
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_52
    | ~ spl15_74 ),
    inference(subsumption_resolution,[],[f3526,f253])).

fof(f3526,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ r2_hidden(sK10(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK9(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ spl15_1
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_52
    | ~ spl15_74 ),
    inference(subsumption_resolution,[],[f3525,f453])).

fof(f453,plain,
    ( m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl15_52 ),
    inference(avatar_component_clause,[],[f452])).

fof(f3525,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ r2_hidden(sK10(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK9(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ spl15_1
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45
    | ~ spl15_74 ),
    inference(subsumption_resolution,[],[f3524,f1504])).

fof(f1504,plain,
    ( m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl15_74 ),
    inference(avatar_component_clause,[],[f1503])).

fof(f3524,plain,
    ( ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ r2_hidden(sK10(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK9(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ spl15_1
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f3523,f246])).

fof(f3523,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ r2_hidden(sK10(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK9(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ spl15_1
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f3522,f232])).

fof(f3522,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ r2_hidden(sK10(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK9(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ spl15_1
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f3510,f208])).

fof(f3510,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ r2_hidden(sK10(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK9(sK0,sK1),k6_waybel_4(sK0,sK8(sK0,sK1),sK1))
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(resolution,[],[f1246,f1732])).

fof(f1732,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X1,k12_lattice3(sK0,X0,X2)),sK1)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1)) )
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_10
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f1731,f635])).

fof(f1731,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,k12_lattice3(sK0,X0,X2)),sK1) )
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f1730,f225])).

fof(f225,plain,
    ( ! [X3] :
        ( v2_waybel_0(k6_waybel_4(sK0,X3,sK1),sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f224])).

fof(f1730,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,k12_lattice3(sK0,X0,X2)),sK1) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f1729,f274])).

fof(f1729,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,k12_lattice3(sK0,X0,X2)),sK1) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f1728,f253])).

fof(f1728,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,k12_lattice3(sK0,X0,X2)),sK1) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f1727,f246])).

fof(f1727,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,k12_lattice3(sK0,X0,X2)),sK1) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(duplicate_literal_removal,[],[f1726])).

fof(f1726,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,k12_lattice3(sK0,X0,X2)),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24
    | ~ spl15_45 ),
    inference(resolution,[],[f679,f506])).

fof(f679,plain,
    ( ! [X14,X17,X15,X16] :
        ( ~ m1_subset_1(k6_waybel_4(sK0,X15,sK1),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ r2_hidden(X16,k6_waybel_4(sK0,X15,sK1))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X15,sK1),X17)
        | ~ r2_hidden(X14,k6_waybel_4(sK0,X15,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X15,sK1),X17)
        | ~ l1_orders_2(X17)
        | ~ v2_lattice3(X17)
        | ~ v5_orders_2(X17)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X15,k12_lattice3(X17,X16,X14)),sK1) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_16
    | ~ spl15_20
    | ~ spl15_22
    | ~ spl15_24 ),
    inference(resolution,[],[f664,f647])).

fof(f664,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f663,f168])).

fof(f663,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f141,f168])).

fof(f141,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f1246,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),k12_lattice3(X0,sK9(X0,X1),sK10(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f1245,f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t44_waybel_7.p',dt_k11_lattice3)).

fof(f1245,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),k12_lattice3(X0,sK9(X0,X1),sK10(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k11_lattice3(X0,sK9(X0,X1),sK10(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f1244,f182])).

fof(f182,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t44_waybel_7.p',cc2_lattice3)).

fof(f1244,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),k12_lattice3(X0,sK9(X0,X1),sK10(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k11_lattice3(X0,sK9(X0,X1),sK10(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f1243])).

fof(f1243,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),k12_lattice3(X0,sK9(X0,X1),sK10(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k11_lattice3(X0,sK9(X0,X1),sK10(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f601,f183])).

fof(f601,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),k11_lattice3(X0,sK9(X0,X1),sK10(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k11_lattice3(X0,sK9(X0,X1),sK10(X0,X1)),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f598,f161])).

fof(f598,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),k11_lattice3(X0,sK9(X0,X1),sK10(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k11_lattice3(X0,sK9(X0,X1),sK10(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f597])).

fof(f597,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),k11_lattice3(X0,sK9(X0,X1),sK10(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k11_lattice3(X0,sK9(X0,X1),sK10(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f166,f194])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_yellow_3(X0,X0,sK8(X0,X1),k11_lattice3(X0,sK9(X0,X1),sK10(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f1512,plain,
    ( spl15_0
    | spl15_74
    | ~ spl15_8
    | ~ spl15_12
    | spl15_45 ),
    inference(avatar_split_clause,[],[f1511,f404,f245,f231,f1503,f204])).

fof(f204,plain,
    ( spl15_0
  <=> v5_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_0])])).

fof(f1511,plain,
    ( m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f1510,f405])).

fof(f1510,plain,
    ( m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl15_8
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f473,f246])).

fof(f473,plain,
    ( m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_8 ),
    inference(resolution,[],[f163,f232])).

fof(f1495,plain,
    ( ~ spl15_1
    | spl15_72
    | ~ spl15_8
    | ~ spl15_12
    | spl15_45 ),
    inference(avatar_split_clause,[],[f1491,f404,f245,f231,f1493,f207])).

fof(f1491,plain,
    ( ! [X23,X21,X22] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X21,X22),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X21,X23),sK1)
        | ~ m1_subset_1(X22,u1_struct_0(sK0))
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | ~ v5_waybel_7(sK1,sK0)
        | r2_hidden(k4_tarski(X21,k11_lattice3(sK0,X23,X22)),sK1) )
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f1490,f405])).

fof(f1490,plain,
    ( ! [X23,X21,X22] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X21,X22),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X21,X23),sK1)
        | ~ m1_subset_1(X22,u1_struct_0(sK0))
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | ~ v5_waybel_7(sK1,sK0)
        | r2_hidden(k4_tarski(X21,k11_lattice3(sK0,X23,X22)),sK1)
        | v2_struct_0(sK0) )
    | ~ spl15_8
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f1278,f246])).

fof(f1278,plain,
    ( ! [X23,X21,X22] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X21,X22),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X21,X23),sK1)
        | ~ m1_subset_1(X22,u1_struct_0(sK0))
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | ~ v5_waybel_7(sK1,sK0)
        | r2_hidden(k4_tarski(X21,k11_lattice3(sK0,X23,X22)),sK1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_8 ),
    inference(resolution,[],[f721,f232])).

fof(f721,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ r2_hidden(k7_yellow_3(X0,X0,X1,X3),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X1,X2),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_7(X4,X0)
      | r2_hidden(k4_tarski(X1,k11_lattice3(X0,X2,X3)),X4)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f717,f195])).

fof(f717,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X1,k11_lattice3(X0,X2,X3)),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X1,X3),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X1,X2),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_7(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k11_lattice3(X0,X2,X3),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f716])).

fof(f716,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X1,k11_lattice3(X0,X2,X3)),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X1,X3),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X1,X2),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_7(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k11_lattice3(X0,X2,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f160,f194])).

fof(f160,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,X5,k11_lattice3(X0,X6,X7)),X1)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X7),X1)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X6),X1)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f458,plain,
    ( ~ spl15_5
    | spl15_3
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f438,f224,f213,f217])).

fof(f217,plain,
    ( spl15_5
  <=> ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f213,plain,
    ( spl15_3
  <=> ~ v2_waybel_0(k6_waybel_4(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f438,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl15_3
    | ~ spl15_6 ),
    inference(resolution,[],[f214,f225])).

fof(f214,plain,
    ( ~ v2_waybel_0(k6_waybel_4(sK0,sK2,sK1),sK0)
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f213])).

fof(f457,plain,
    ( spl15_0
    | spl15_52
    | ~ spl15_8
    | ~ spl15_12
    | spl15_45 ),
    inference(avatar_split_clause,[],[f456,f404,f245,f231,f452,f204])).

fof(f456,plain,
    ( m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ spl15_8
    | ~ spl15_12
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f455,f405])).

fof(f455,plain,
    ( m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl15_8
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f440,f246])).

fof(f440,plain,
    ( m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_8 ),
    inference(resolution,[],[f162,f232])).

fof(f437,plain,
    ( ~ spl15_12
    | ~ spl15_14
    | ~ spl15_44 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | ~ spl15_12
    | ~ spl15_14
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f435,f246])).

fof(f435,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl15_14
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f433,f253])).

fof(f433,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl15_44 ),
    inference(resolution,[],[f408,f182])).

fof(f408,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_44 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl15_44
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_44])])).

fof(f417,plain,
    ( spl15_44
    | spl15_0
    | spl15_46
    | ~ spl15_8
    | ~ spl15_12 ),
    inference(avatar_split_clause,[],[f416,f245,f231,f413,f204,f407])).

fof(f416,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl15_8
    | ~ spl15_12 ),
    inference(subsumption_resolution,[],[f396,f246])).

fof(f396,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_8 ),
    inference(resolution,[],[f161,f232])).

fof(f289,plain,(
    spl15_24 ),
    inference(avatar_split_clause,[],[f129,f287])).

fof(f129,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,
    ( ( ( ~ v2_waybel_0(k6_waybel_4(sK0,sK2,sK1),sK0)
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ v5_waybel_7(sK1,sK0) )
    & ( ! [X3] :
          ( v2_waybel_0(k6_waybel_4(sK0,X3,sK1),sK0)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      | v5_waybel_7(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    & v5_waybel_4(sK1,sK0)
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f95,f98,f97,f96])).

fof(f96,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) )
            & ( ! [X3] :
                  ( v2_waybel_0(k6_waybel_4(X0,X3,X1),X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | v5_waybel_7(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
            & v5_waybel_4(X1,X0) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ v2_waybel_0(k6_waybel_4(sK0,X2,X1),sK0)
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ v5_waybel_7(X1,sK0) )
          & ( ! [X3] :
                ( v2_waybel_0(k6_waybel_4(sK0,X3,X1),sK0)
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            | v5_waybel_7(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
          & v5_waybel_4(X1,sK0) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X3] :
                ( v2_waybel_0(k6_waybel_4(X0,X3,X1),X0)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
     => ( ( ? [X2] :
              ( ~ v2_waybel_0(k6_waybel_4(X0,X2,sK1),X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(sK1,X0) )
        & ( ! [X3] :
              ( v2_waybel_0(k6_waybel_4(X0,X3,sK1),X0)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | v5_waybel_7(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v5_waybel_4(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ v2_waybel_0(k6_waybel_4(X0,sK2,X1),X0)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X3] :
                ( v2_waybel_0(k6_waybel_4(X0,X3,X1),X0)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f94])).

fof(f94,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_waybel_7(X1,X0)
          <~> ! [X2] :
                ( v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_waybel_7(X1,X0)
          <~> ! [X2] :
                ( v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              & v5_waybel_4(X1,X0) )
           => ( v5_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => v2_waybel_0(k6_waybel_4(X0,X2,X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
            & v5_waybel_4(X1,X0) )
         => ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => v2_waybel_0(k6_waybel_4(X0,X2,X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t44_waybel_7.p',t44_waybel_7)).

fof(f282,plain,(
    spl15_22 ),
    inference(avatar_split_clause,[],[f130,f280])).

fof(f130,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f275,plain,(
    spl15_20 ),
    inference(avatar_split_clause,[],[f131,f273])).

fof(f131,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f268,plain,(
    spl15_18 ),
    inference(avatar_split_clause,[],[f132,f266])).

fof(f132,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f261,plain,(
    spl15_16 ),
    inference(avatar_split_clause,[],[f133,f259])).

fof(f133,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f254,plain,(
    spl15_14 ),
    inference(avatar_split_clause,[],[f134,f252])).

fof(f134,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f247,plain,(
    spl15_12 ),
    inference(avatar_split_clause,[],[f135,f245])).

fof(f135,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f240,plain,(
    spl15_10 ),
    inference(avatar_split_clause,[],[f136,f238])).

fof(f136,plain,(
    v5_waybel_4(sK1,sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f233,plain,(
    spl15_8 ),
    inference(avatar_split_clause,[],[f137,f231])).

fof(f137,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f99])).

fof(f226,plain,
    ( spl15_0
    | spl15_6 ),
    inference(avatar_split_clause,[],[f138,f224,f204])).

fof(f138,plain,(
    ! [X3] :
      ( v2_waybel_0(k6_waybel_4(sK0,X3,sK1),sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v5_waybel_7(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f222,plain,
    ( ~ spl15_1
    | spl15_4 ),
    inference(avatar_split_clause,[],[f139,f220,f207])).

fof(f220,plain,
    ( spl15_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f139,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f99])).

fof(f215,plain,
    ( ~ spl15_1
    | ~ spl15_3 ),
    inference(avatar_split_clause,[],[f140,f213,f207])).

fof(f140,plain,
    ( ~ v2_waybel_0(k6_waybel_4(sK0,sK2,sK1),sK0)
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f99])).
%------------------------------------------------------------------------------
