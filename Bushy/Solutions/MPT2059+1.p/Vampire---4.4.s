%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t18_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:50 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  271 ( 565 expanded)
%              Number of leaves         :   61 ( 230 expanded)
%              Depth                    :   15
%              Number of atoms          : 1268 (2341 expanded)
%              Number of equality atoms :   22 (  52 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f776,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f138,f145,f152,f159,f166,f173,f180,f187,f194,f207,f208,f226,f277,f325,f328,f337,f355,f365,f370,f385,f392,f396,f400,f412,f520,f571,f574,f633,f666,f672,f678,f689,f702,f714,f729,f756,f775])).

fof(f775,plain,
    ( ~ spl6_20
    | spl6_29 ),
    inference(avatar_contradiction_clause,[],[f774])).

fof(f774,plain,
    ( $false
    | ~ spl6_20
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f752,f270])).

fof(f270,plain,
    ( ~ m1_subset_1(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl6_29
  <=> ~ m1_subset_1(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f752,plain,
    ( m1_subset_1(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ spl6_20 ),
    inference(resolution,[],[f200,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',t1_subset)).

fof(f200,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl6_20
  <=> r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f756,plain,
    ( ~ spl6_20
    | spl6_23
    | ~ spl6_36
    | ~ spl6_74 ),
    inference(avatar_contradiction_clause,[],[f755])).

fof(f755,plain,
    ( $false
    | ~ spl6_20
    | ~ spl6_23
    | ~ spl6_36
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f754,f203])).

fof(f203,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl6_23
  <=> ~ r2_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f754,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ spl6_20
    | ~ spl6_36
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f746,f336])).

fof(f336,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl6_36
  <=> m1_subset_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f746,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ spl6_20
    | ~ spl6_74 ),
    inference(resolution,[],[f200,f665])).

fof(f665,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r2_waybel_7(sK0,sK1,X0) )
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f664])).

fof(f664,plain,
    ( spl6_74
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | r2_waybel_7(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f729,plain,
    ( spl6_21
    | ~ spl6_22
    | ~ spl6_36
    | ~ spl6_80 ),
    inference(avatar_contradiction_clause,[],[f728])).

fof(f728,plain,
    ( $false
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_36
    | ~ spl6_80 ),
    inference(subsumption_resolution,[],[f727,f206])).

fof(f206,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl6_22
  <=> r2_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f727,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ spl6_21
    | ~ spl6_36
    | ~ spl6_80 ),
    inference(subsumption_resolution,[],[f715,f336])).

fof(f715,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ spl6_21
    | ~ spl6_80 ),
    inference(resolution,[],[f713,f197])).

fof(f197,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl6_21
  <=> ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f713,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK1,X1) )
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f712])).

fof(f712,plain,
    ( spl6_80
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ r2_waybel_7(sK0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f714,plain,
    ( ~ spl6_69
    | ~ spl6_71
    | ~ spl6_73
    | spl6_46
    | spl6_80
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f348,f320,f317,f150,f143,f136,f712,f387,f661,f655,f649])).

fof(f649,plain,
    ( spl6_69
  <=> ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f655,plain,
    ( spl6_71
  <=> ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f661,plain,
    ( spl6_73
  <=> ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f387,plain,
    ( spl6_46
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f136,plain,
    ( spl6_3
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f143,plain,
    ( spl6_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f150,plain,
    ( spl6_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f317,plain,
    ( spl6_32
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f320,plain,
    ( spl6_34
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f348,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK1,X1)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f347,f329])).

fof(f329,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl6_34 ),
    inference(resolution,[],[f321,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',d3_struct_0)).

fof(f321,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f320])).

fof(f347,plain,
    ( ! [X1] :
        ( ~ r2_waybel_7(sK0,sK1,X1)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f346,f137])).

fof(f137,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f136])).

fof(f346,plain,
    ( ! [X1] :
        ( ~ r2_waybel_7(sK0,sK1,X1)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f345,f151])).

fof(f151,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f345,plain,
    ( ! [X1] :
        ( ~ r2_waybel_7(sK0,sK1,X1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    | ~ spl6_4
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f339,f144])).

fof(f144,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f339,plain,
    ( ! [X1] :
        ( ~ r2_waybel_7(sK0,sK1,X1)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    | ~ spl6_32 ),
    inference(superposition,[],[f93,f318])).

fof(f318,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f317])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,k10_yellow_6(X0,X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',t13_yellow19)).

fof(f702,plain,
    ( ~ spl6_77
    | spl6_78
    | spl6_41
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f607,f410,f357,f700,f694])).

fof(f694,plain,
    ( spl6_77
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f700,plain,
    ( spl6_78
  <=> v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f357,plain,
    ( spl6_41
  <=> ~ v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f410,plain,
    ( spl6_52
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f607,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ spl6_41
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f597,f358])).

fof(f358,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f357])).

fof(f597,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ spl6_52 ),
    inference(resolution,[],[f413,f411])).

fof(f411,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f410])).

fof(f413,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f211,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',t2_subset)).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f100,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',antisymmetry_r2_hidden)).

fof(f689,plain,
    ( spl6_1
    | spl6_3
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_34
    | ~ spl6_38
    | spl6_41
    | ~ spl6_52
    | spl6_69 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_41
    | ~ spl6_52
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f687,f411])).

fof(f687,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_41
    | ~ spl6_69 ),
    inference(forward_demodulation,[],[f686,f354])).

fof(f354,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl6_38
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f686,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_34
    | ~ spl6_41
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f685,f137])).

fof(f685,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_34
    | ~ spl6_41
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f684,f186])).

fof(f186,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f684,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_34
    | ~ spl6_41
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f683,f172])).

fof(f172,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_12
  <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f683,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_34
    | ~ spl6_41
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f682,f165])).

fof(f165,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl6_10
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f682,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_34
    | ~ spl6_41
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f681,f130])).

fof(f130,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_1
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f681,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl6_34
    | ~ spl6_41
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f680,f358])).

fof(f680,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl6_34
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f679,f321])).

fof(f679,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl6_69 ),
    inference(resolution,[],[f650,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',dt_k3_yellow19)).

fof(f650,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f649])).

fof(f678,plain,
    ( spl6_3
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_48
    | ~ spl6_52
    | spl6_73 ),
    inference(avatar_contradiction_clause,[],[f677])).

fof(f677,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_48
    | ~ spl6_52
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f676,f411])).

fof(f676,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_3
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_48
    | ~ spl6_73 ),
    inference(forward_demodulation,[],[f675,f354])).

fof(f675,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3
    | ~ spl6_34
    | ~ spl6_48
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f674,f137])).

fof(f674,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_34
    | ~ spl6_48
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f673,f321])).

fof(f673,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_48
    | ~ spl6_73 ),
    inference(resolution,[],[f662,f395])).

fof(f395,plain,
    ( ! [X8] :
        ( v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1))
        | ~ l1_struct_0(X8)
        | v2_struct_0(X8)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8))) )
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl6_48
  <=> ! [X8] :
        ( ~ l1_struct_0(X8)
        | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1))
        | v2_struct_0(X8)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f662,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f661])).

fof(f672,plain,
    ( spl6_3
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_50
    | ~ spl6_52
    | spl6_71 ),
    inference(avatar_contradiction_clause,[],[f671])).

fof(f671,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_50
    | ~ spl6_52
    | ~ spl6_71 ),
    inference(subsumption_resolution,[],[f670,f411])).

fof(f670,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_3
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_50
    | ~ spl6_71 ),
    inference(forward_demodulation,[],[f669,f354])).

fof(f669,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3
    | ~ spl6_34
    | ~ spl6_50
    | ~ spl6_71 ),
    inference(subsumption_resolution,[],[f668,f137])).

fof(f668,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_34
    | ~ spl6_50
    | ~ spl6_71 ),
    inference(subsumption_resolution,[],[f667,f321])).

fof(f667,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_50
    | ~ spl6_71 ),
    inference(resolution,[],[f656,f399])).

fof(f399,plain,
    ( ! [X8] :
        ( v7_waybel_0(k3_yellow19(X8,k2_struct_0(sK0),sK1))
        | ~ l1_struct_0(X8)
        | v2_struct_0(X8)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8))) )
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl6_50
  <=> ! [X8] :
        ( ~ l1_struct_0(X8)
        | v7_waybel_0(k3_yellow19(X8,k2_struct_0(sK0),sK1))
        | v2_struct_0(X8)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f656,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl6_71 ),
    inference(avatar_component_clause,[],[f655])).

fof(f666,plain,
    ( ~ spl6_69
    | ~ spl6_71
    | ~ spl6_73
    | spl6_46
    | spl6_74
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f344,f320,f317,f150,f143,f136,f664,f387,f661,f655,f649])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r2_waybel_7(sK0,sK1,X0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f343,f329])).

fof(f343,plain,
    ( ! [X0] :
        ( r2_waybel_7(sK0,sK1,X0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f342,f137])).

fof(f342,plain,
    ( ! [X0] :
        ( r2_waybel_7(sK0,sK1,X0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f341,f151])).

fof(f341,plain,
    ( ! [X0] :
        ( r2_waybel_7(sK0,sK1,X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    | ~ spl6_4
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f338,f144])).

fof(f338,plain,
    ( ! [X0] :
        ( r2_waybel_7(sK0,sK1,X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    | ~ spl6_32 ),
    inference(superposition,[],[f94,f318])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f633,plain,
    ( ~ spl6_65
    | spl6_66
    | ~ spl6_36
    | spl6_41 ),
    inference(avatar_split_clause,[],[f609,f357,f335,f631,f625])).

fof(f625,plain,
    ( spl6_65
  <=> ~ m1_subset_1(k2_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f631,plain,
    ( spl6_66
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f609,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),sK2)
    | ~ spl6_36
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f602,f358])).

fof(f602,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),sK2)
    | ~ spl6_36 ),
    inference(resolution,[],[f413,f336])).

fof(f574,plain,
    ( ~ spl6_18
    | spl6_57 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | ~ spl6_18
    | ~ spl6_57 ),
    inference(subsumption_resolution,[],[f572,f193])).

fof(f193,plain,
    ( l1_pre_topc(sK5)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl6_18
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f572,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ spl6_57 ),
    inference(resolution,[],[f552,f124])).

fof(f124,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',dt_l1_pre_topc)).

fof(f552,plain,
    ( ~ l1_struct_0(sK5)
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f551])).

fof(f551,plain,
    ( spl6_57
  <=> ~ l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f571,plain,
    ( ~ spl6_57
    | spl6_58
    | ~ spl6_61
    | ~ spl6_63
    | ~ spl6_42
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f543,f518,f363,f569,f563,f557,f551])).

fof(f557,plain,
    ( spl6_58
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f563,plain,
    ( spl6_61
  <=> ~ v2_struct_0(k3_yellow19(sK5,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f569,plain,
    ( spl6_63
  <=> ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f363,plain,
    ( spl6_42
  <=> ! [X8] :
        ( ~ l1_struct_0(X8)
        | ~ v2_struct_0(k3_yellow19(X8,k2_struct_0(sK0),sK1))
        | v2_struct_0(X8)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f518,plain,
    ( spl6_54
  <=> k2_struct_0(sK5) = u1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f543,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK5)))
    | ~ v2_struct_0(k3_yellow19(sK5,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK5)
    | ~ l1_struct_0(sK5)
    | ~ spl6_42
    | ~ spl6_54 ),
    inference(superposition,[],[f364,f519])).

fof(f519,plain,
    ( k2_struct_0(sK5) = u1_struct_0(sK5)
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f518])).

fof(f364,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v2_struct_0(k3_yellow19(X8,k2_struct_0(sK0),sK1))
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f363])).

fof(f520,plain,
    ( spl6_54
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f402,f192,f518])).

fof(f402,plain,
    ( k2_struct_0(sK5) = u1_struct_0(sK5)
    | ~ spl6_18 ),
    inference(resolution,[],[f209,f193])).

fof(f209,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f118,f124])).

fof(f412,plain,
    ( spl6_52
    | ~ spl6_34
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f376,f353,f320,f410])).

fof(f376,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_34
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f372,f321])).

fof(f372,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl6_38 ),
    inference(superposition,[],[f116,f354])).

fof(f116,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',dt_k2_struct_0)).

fof(f400,plain,
    ( spl6_40
    | spl6_50
    | spl6_1
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f301,f185,f178,f171,f164,f129,f398,f360])).

fof(f360,plain,
    ( spl6_40
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f178,plain,
    ( spl6_14
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f301,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | v7_waybel_0(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f300,f172])).

fof(f300,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | v7_waybel_0(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f299,f165])).

fof(f299,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | v7_waybel_0(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f298,f179])).

fof(f179,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f178])).

fof(f298,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | v7_waybel_0(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f295,f130])).

fof(f295,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | v1_xboole_0(sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | v7_waybel_0(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_16 ),
    inference(resolution,[],[f106,f186])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | v2_struct_0(X0)
      | v7_waybel_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',fc5_yellow19)).

fof(f396,plain,
    ( spl6_40
    | spl6_48
    | spl6_1
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f286,f185,f171,f164,f129,f394,f360])).

fof(f286,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f285,f172])).

fof(f285,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f284,f165])).

fof(f284,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f281,f130])).

fof(f281,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | v1_xboole_0(sK1)
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_16 ),
    inference(resolution,[],[f112,f186])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | v2_struct_0(X0)
      | v4_orders_2(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',fc4_yellow19)).

fof(f392,plain,
    ( ~ spl6_47
    | spl6_3
    | ~ spl6_34
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f381,f363,f320,f136,f390])).

fof(f390,plain,
    ( spl6_47
  <=> ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f381,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl6_3
    | ~ spl6_34
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f380,f321])).

fof(f380,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f379,f137])).

fof(f379,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl6_42 ),
    inference(duplicate_literal_removal,[],[f377])).

fof(f377,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl6_42 ),
    inference(resolution,[],[f364,f116])).

fof(f385,plain,
    ( spl6_40
    | spl6_44
    | spl6_1
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f264,f185,f171,f164,f129,f383,f360])).

fof(f383,plain,
    ( spl6_44
  <=> ! [X8] :
        ( ~ l1_struct_0(X8)
        | v3_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1))
        | v2_struct_0(X8)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f264,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | v3_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f263,f172])).

fof(f263,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | v3_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f262,f165])).

fof(f262,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | v3_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f259,f130])).

fof(f259,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | v1_xboole_0(sK1)
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | v3_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_16 ),
    inference(resolution,[],[f111,f186])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | v2_struct_0(X0)
      | v3_orders_2(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f370,plain,
    ( spl6_3
    | ~ spl6_34
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_34
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f368,f137])).

fof(f368,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_34
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f366,f321])).

fof(f366,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_40 ),
    inference(resolution,[],[f361,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',fc5_struct_0)).

fof(f361,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f360])).

fof(f365,plain,
    ( spl6_40
    | spl6_42
    | spl6_1
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f255,f185,f171,f164,f129,f363,f360])).

fof(f255,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v2_struct_0(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f254,f172])).

fof(f254,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | ~ v2_struct_0(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f253,f165])).

fof(f253,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | ~ v2_struct_0(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f250,f130])).

fof(f250,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(X8)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
        | v1_xboole_0(sK1)
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X8)
        | ~ v2_struct_0(k3_yellow19(X8,k2_struct_0(sK0),sK1)) )
    | ~ spl6_16 ),
    inference(resolution,[],[f107,f186])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | v2_struct_0(X0)
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f355,plain,
    ( spl6_38
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f329,f320,f353])).

fof(f337,plain,
    ( spl6_36
    | ~ spl6_8
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f330,f320,f157,f335])).

fof(f157,plain,
    ( spl6_8
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f330,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ spl6_8
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f329,f158])).

fof(f158,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f328,plain,
    ( ~ spl6_6
    | spl6_35 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f326,f151])).

fof(f326,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_35 ),
    inference(resolution,[],[f324,f124])).

fof(f324,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl6_35
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f325,plain,
    ( spl6_32
    | ~ spl6_35
    | spl6_1
    | spl6_3
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f312,f185,f178,f171,f164,f136,f129,f323,f317])).

fof(f312,plain,
    ( ~ l1_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f311,f137])).

fof(f311,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f310,f172])).

fof(f310,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl6_1
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f309,f165])).

fof(f309,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f308,f179])).

fof(f308,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f305,f130])).

fof(f305,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | ~ spl6_16 ),
    inference(resolution,[],[f114,f186])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v2_struct_0(X0)
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',t15_yellow19)).

fof(f277,plain,
    ( ~ spl6_29
    | spl6_30
    | spl6_21 ),
    inference(avatar_split_clause,[],[f210,f196,f275,f269])).

fof(f275,plain,
    ( spl6_30
  <=> v1_xboole_0(k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f210,plain,
    ( v1_xboole_0(k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ spl6_21 ),
    inference(resolution,[],[f100,f197])).

fof(f226,plain,
    ( ~ spl6_25
    | spl6_26
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f215,f185,f224,f221])).

fof(f221,plain,
    ( spl6_25
  <=> ~ v1_xboole_0(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f224,plain,
    ( spl6_26
  <=> ! [X2] : ~ r2_hidden(X2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f215,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ v1_xboole_0(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl6_16 ),
    inference(resolution,[],[f95,f186])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',t5_subset)).

fof(f208,plain,
    ( ~ spl6_21
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f83,f202,f196])).

fof(f83,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
                <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',t18_yellow19)).

fof(f207,plain,
    ( spl6_20
    | spl6_22 ),
    inference(avatar_split_clause,[],[f82,f205,f199])).

fof(f82,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f194,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f123,f192])).

fof(f123,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t18_yellow19.p',existence_l1_pre_topc)).

fof(f187,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f89,f185])).

fof(f89,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f52])).

fof(f180,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f86,f178])).

fof(f86,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f173,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f88,f171])).

fof(f88,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f166,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f87,f164])).

fof(f87,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f159,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f84,f157])).

fof(f84,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f152,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f92,f150])).

fof(f92,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f145,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f91,f143])).

fof(f91,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f138,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f90,f136])).

fof(f90,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f131,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f85,f129])).

fof(f85,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
