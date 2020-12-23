%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t84_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:23 EDT 2019

% Result     : Theorem 35.28s
% Output     : Refutation 35.28s
% Verified   : 
% Statistics : Number of formulae       :  339 ( 888 expanded)
%              Number of leaves         :   60 ( 337 expanded)
%              Depth                    :   24
%              Number of atoms          : 1864 (3998 expanded)
%              Number of equality atoms :  169 ( 326 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f246,f253,f260,f267,f274,f400,f407,f414,f427,f479,f539,f612,f672,f1051,f1059,f1072,f1277,f1747,f1827,f4862,f4886,f4983,f9034,f9565,f9912,f10886,f11252,f11422,f11497,f11745,f12005,f12100,f12102])).

fof(f12102,plain,
    ( ~ spl17_22
    | ~ spl17_62
    | ~ spl17_66
    | ~ spl17_264 ),
    inference(avatar_contradiction_clause,[],[f12101])).

fof(f12101,plain,
    ( $false
    | ~ spl17_22
    | ~ spl17_62
    | ~ spl17_66
    | ~ spl17_264 ),
    inference(subsumption_resolution,[],[f10896,f1112])).

fof(f1112,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl17_22
    | ~ spl17_62 ),
    inference(backward_demodulation,[],[f1077,f478])).

fof(f478,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_22 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl17_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_22])])).

fof(f1077,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ spl17_62 ),
    inference(resolution,[],[f1068,f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t6_boole)).

fof(f1068,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl17_62 ),
    inference(avatar_component_clause,[],[f1067])).

fof(f1067,plain,
    ( spl17_62
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_62])])).

fof(f10896,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl17_66
    | ~ spl17_264 ),
    inference(resolution,[],[f10885,f2756])).

fof(f2756,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl17_66 ),
    inference(resolution,[],[f1276,f222])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f61])).

fof(f61,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t5_subset)).

fof(f1276,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl17_66 ),
    inference(avatar_component_clause,[],[f1275])).

fof(f1275,plain,
    ( spl17_66
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_66])])).

fof(f10885,plain,
    ( r2_hidden(sK6(sK0,sK3,k3_orders_2(sK0,sK3,sK6(sK0,sK3,sK2))),sK3)
    | ~ spl17_264 ),
    inference(avatar_component_clause,[],[f10884])).

fof(f10884,plain,
    ( spl17_264
  <=> r2_hidden(sK6(sK0,sK3,k3_orders_2(sK0,sK3,sK6(sK0,sK3,sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_264])])).

fof(f12100,plain,
    ( ~ spl17_20
    | ~ spl17_62
    | ~ spl17_66
    | ~ spl17_274 ),
    inference(avatar_contradiction_clause,[],[f12099])).

fof(f12099,plain,
    ( $false
    | ~ spl17_20
    | ~ spl17_62
    | ~ spl17_66
    | ~ spl17_274 ),
    inference(subsumption_resolution,[],[f11262,f1107])).

fof(f1107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl17_20
    | ~ spl17_62 ),
    inference(backward_demodulation,[],[f1077,f459])).

fof(f459,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_20 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl17_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_20])])).

fof(f11262,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl17_66
    | ~ spl17_274 ),
    inference(resolution,[],[f11245,f2756])).

fof(f11245,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl17_274 ),
    inference(avatar_component_clause,[],[f11244])).

fof(f11244,plain,
    ( spl17_274
  <=> r2_hidden(sK6(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_274])])).

fof(f12005,plain,
    ( spl17_37
    | ~ spl17_78
    | spl17_83
    | ~ spl17_300 ),
    inference(avatar_contradiction_clause,[],[f12004])).

fof(f12004,plain,
    ( $false
    | ~ spl17_37
    | ~ spl17_78
    | ~ spl17_83
    | ~ spl17_300 ),
    inference(subsumption_resolution,[],[f11778,f1823])).

fof(f1823,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | ~ spl17_83 ),
    inference(avatar_component_clause,[],[f1822])).

fof(f1822,plain,
    ( spl17_83
  <=> ~ m1_orders_2(sK2,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_83])])).

fof(f11778,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl17_37
    | ~ spl17_78
    | ~ spl17_300 ),
    inference(backward_demodulation,[],[f11755,f1740])).

fof(f1740,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl17_78 ),
    inference(avatar_component_clause,[],[f1739])).

fof(f1739,plain,
    ( spl17_78
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_78])])).

fof(f11755,plain,
    ( sK2 = sK3
    | ~ spl17_37
    | ~ spl17_300 ),
    inference(subsumption_resolution,[],[f11754,f628])).

fof(f628,plain,
    ( ~ r2_xboole_0(sK3,sK2)
    | ~ spl17_37 ),
    inference(avatar_component_clause,[],[f627])).

fof(f627,plain,
    ( spl17_37
  <=> ~ r2_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_37])])).

fof(f11754,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK3,sK2)
    | ~ spl17_300 ),
    inference(resolution,[],[f11744,f196])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',d8_xboole_0)).

fof(f11744,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl17_300 ),
    inference(avatar_component_clause,[],[f11743])).

fof(f11743,plain,
    ( spl17_300
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_300])])).

fof(f11745,plain,
    ( spl17_300
    | ~ spl17_20
    | ~ spl17_64
    | ~ spl17_274
    | ~ spl17_290 ),
    inference(avatar_split_clause,[],[f11700,f11495,f11244,f1070,f458,f11743])).

fof(f1070,plain,
    ( spl17_64
  <=> ! [X1,X0] :
        ( k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k1_tarski(X0)),X1) = k3_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_64])])).

fof(f11495,plain,
    ( spl17_290
  <=> k3_orders_2(sK0,sK2,sK6(sK0,sK2,sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_290])])).

fof(f11700,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl17_20
    | ~ spl17_64
    | ~ spl17_274
    | ~ spl17_290 ),
    inference(subsumption_resolution,[],[f11498,f11695])).

fof(f11695,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl17_20
    | ~ spl17_274 ),
    inference(resolution,[],[f11255,f459])).

fof(f11255,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | m1_subset_1(sK6(sK0,sK2,sK3),X0) )
    | ~ spl17_274 ),
    inference(resolution,[],[f11245,f221])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f130])).

fof(f130,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f129])).

fof(f129,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f60,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t4_subset)).

fof(f11498,plain,
    ( r1_tarski(sK3,sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl17_20
    | ~ spl17_64
    | ~ spl17_290 ),
    inference(superposition,[],[f3077,f11496])).

fof(f11496,plain,
    ( k3_orders_2(sK0,sK2,sK6(sK0,sK2,sK3)) = sK3
    | ~ spl17_290 ),
    inference(avatar_component_clause,[],[f11495])).

fof(f3077,plain,
    ( ! [X3] :
        ( r1_tarski(k3_orders_2(sK0,sK2,X3),sK2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl17_20
    | ~ spl17_64 ),
    inference(superposition,[],[f177,f1696])).

fof(f1696,plain,
    ( ! [X2] :
        ( k3_xboole_0(sK2,k2_orders_2(sK0,k1_tarski(X2))) = k3_orders_2(sK0,sK2,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl17_20
    | ~ spl17_64 ),
    inference(forward_demodulation,[],[f1694,f178])).

fof(f178,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',commutativity_k3_xboole_0)).

fof(f1694,plain,
    ( ! [X2] :
        ( k3_xboole_0(k2_orders_2(sK0,k1_tarski(X2)),sK2) = k3_orders_2(sK0,sK2,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl17_20
    | ~ spl17_64 ),
    inference(backward_demodulation,[],[f1691,f1690])).

fof(f1690,plain,
    ( ! [X2] :
        ( k9_subset_1(u1_struct_0(sK0),sK2,k2_orders_2(sK0,k1_tarski(X2))) = k3_orders_2(sK0,sK2,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl17_20
    | ~ spl17_64 ),
    inference(subsumption_resolution,[],[f1676,f459])).

fof(f1676,plain,
    ( ! [X2] :
        ( k9_subset_1(u1_struct_0(sK0),sK2,k2_orders_2(sK0,k1_tarski(X2))) = k3_orders_2(sK0,sK2,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl17_20
    | ~ spl17_64 ),
    inference(superposition,[],[f1060,f1071])).

fof(f1071,plain,
    ( ! [X0,X1] :
        ( k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k1_tarski(X0)),X1) = k3_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl17_64 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f1060,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0)
    | ~ spl17_20 ),
    inference(resolution,[],[f459,f206])).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',commutativity_k9_subset_1)).

fof(f1691,plain,
    ( ! [X3] : k3_xboole_0(X3,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X3)
    | ~ spl17_20 ),
    inference(subsumption_resolution,[],[f1678,f459])).

fof(f1678,plain,
    ( ! [X3] :
        ( k3_xboole_0(X3,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_20 ),
    inference(superposition,[],[f1060,f204])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',redefinition_k9_subset_1)).

fof(f177,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t17_xboole_1)).

fof(f11497,plain,
    ( spl17_290
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_20
    | ~ spl17_78
    | spl17_277 ),
    inference(avatar_split_clause,[],[f11438,f11247,f1739,f458,f272,f265,f258,f251,f244,f11495])).

fof(f244,plain,
    ( spl17_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f251,plain,
    ( spl17_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f258,plain,
    ( spl17_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f265,plain,
    ( spl17_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).

fof(f272,plain,
    ( spl17_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_8])])).

fof(f11247,plain,
    ( spl17_277
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_277])])).

fof(f11438,plain,
    ( k3_orders_2(sK0,sK2,sK6(sK0,sK2,sK3)) = sK3
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_20
    | ~ spl17_78
    | ~ spl17_277 ),
    inference(subsumption_resolution,[],[f10592,f11248])).

fof(f11248,plain,
    ( k1_xboole_0 != sK2
    | ~ spl17_277 ),
    inference(avatar_component_clause,[],[f11247])).

fof(f10592,plain,
    ( k1_xboole_0 = sK2
    | k3_orders_2(sK0,sK2,sK6(sK0,sK2,sK3)) = sK3
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_20
    | ~ spl17_78 ),
    inference(subsumption_resolution,[],[f10585,f459])).

fof(f10585,plain,
    ( k1_xboole_0 = sK2
    | k3_orders_2(sK0,sK2,sK6(sK0,sK2,sK3)) = sK3
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_78 ),
    inference(resolution,[],[f1740,f1278])).

fof(f1278,plain,
    ( ! [X19,X18] :
        ( ~ m1_orders_2(X19,sK0,X18)
        | k1_xboole_0 = X18
        | k3_orders_2(sK0,X18,sK6(sK0,X18,X19)) = X19
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f335,f351])).

fof(f351,plain,
    ( ! [X26,X25] :
        ( ~ m1_orders_2(X26,sK0,X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f350,f245])).

fof(f245,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl17_1 ),
    inference(avatar_component_clause,[],[f244])).

fof(f350,plain,
    ( ! [X26,X25] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X26,sK0,X25)
        | m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f349,f266])).

fof(f266,plain,
    ( v5_orders_2(sK0)
    | ~ spl17_6 ),
    inference(avatar_component_clause,[],[f265])).

fof(f349,plain,
    ( ! [X26,X25] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X26,sK0,X25)
        | m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f348,f259])).

fof(f259,plain,
    ( v4_orders_2(sK0)
    | ~ spl17_4 ),
    inference(avatar_component_clause,[],[f258])).

fof(f348,plain,
    ( ! [X26,X25] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X26,sK0,X25)
        | m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f287,f252])).

fof(f252,plain,
    ( v3_orders_2(sK0)
    | ~ spl17_2 ),
    inference(avatar_component_clause,[],[f251])).

fof(f287,plain,
    ( ! [X26,X25] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X26,sK0,X25)
        | m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_8 ),
    inference(resolution,[],[f273,f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',dt_m1_orders_2)).

fof(f273,plain,
    ( l1_orders_2(sK0)
    | ~ spl17_8 ),
    inference(avatar_component_clause,[],[f272])).

fof(f335,plain,
    ( ! [X19,X18] :
        ( ~ m1_orders_2(X19,sK0,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X18
        | k3_orders_2(sK0,X18,sK6(sK0,X18,X19)) = X19
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f334,f245])).

fof(f334,plain,
    ( ! [X19,X18] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X18
        | k3_orders_2(sK0,X18,sK6(sK0,X18,X19)) = X19
        | ~ m1_orders_2(X19,sK0,X18) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f333,f266])).

fof(f333,plain,
    ( ! [X19,X18] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X18
        | k3_orders_2(sK0,X18,sK6(sK0,X18,X19)) = X19
        | ~ m1_orders_2(X19,sK0,X18) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f332,f259])).

fof(f332,plain,
    ( ! [X19,X18] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X18
        | k3_orders_2(sK0,X18,sK6(sK0,X18,X19)) = X19
        | ~ m1_orders_2(X19,sK0,X18) )
    | ~ spl17_2
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f283,f252])).

fof(f283,plain,
    ( ! [X19,X18] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X18
        | k3_orders_2(sK0,X18,sK6(sK0,X18,X19)) = X19
        | ~ m1_orders_2(X19,sK0,X18) )
    | ~ spl17_8 ),
    inference(resolution,[],[f273,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | k3_orders_2(X0,X1,sK6(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',d15_orders_2)).

fof(f11422,plain,
    ( k1_xboole_0 != sK2
    | m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ m2_orders_2(sK2,sK0,sK1) ),
    introduced(theory_axiom,[])).

fof(f11252,plain,
    ( spl17_274
    | spl17_276
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_20
    | ~ spl17_78 ),
    inference(avatar_split_clause,[],[f10593,f1739,f458,f272,f265,f258,f251,f244,f11250,f11244])).

fof(f11250,plain,
    ( spl17_276
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_276])])).

fof(f10593,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_20
    | ~ spl17_78 ),
    inference(subsumption_resolution,[],[f10586,f459])).

fof(f10586,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_78 ),
    inference(resolution,[],[f1740,f1279])).

fof(f1279,plain,
    ( ! [X17,X16] :
        ( ~ m1_orders_2(X17,sK0,X16)
        | k1_xboole_0 = X16
        | r2_hidden(sK6(sK0,X16,X17),X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f331,f351])).

fof(f331,plain,
    ( ! [X17,X16] :
        ( ~ m1_orders_2(X17,sK0,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X16
        | r2_hidden(sK6(sK0,X16,X17),X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f330,f245])).

fof(f330,plain,
    ( ! [X17,X16] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X16
        | r2_hidden(sK6(sK0,X16,X17),X16)
        | ~ m1_orders_2(X17,sK0,X16) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f329,f266])).

fof(f329,plain,
    ( ! [X17,X16] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X16
        | r2_hidden(sK6(sK0,X16,X17),X16)
        | ~ m1_orders_2(X17,sK0,X16) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f328,f259])).

fof(f328,plain,
    ( ! [X17,X16] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X16
        | r2_hidden(sK6(sK0,X16,X17),X16)
        | ~ m1_orders_2(X17,sK0,X16) )
    | ~ spl17_2
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f282,f252])).

fof(f282,plain,
    ( ! [X17,X16] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X16
        | r2_hidden(sK6(sK0,X16,X17),X16)
        | ~ m1_orders_2(X17,sK0,X16) )
    | ~ spl17_8 ),
    inference(resolution,[],[f273,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f10886,plain,
    ( spl17_264
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_22
    | ~ spl17_30
    | spl17_33 ),
    inference(avatar_split_clause,[],[f7881,f607,f604,f477,f272,f265,f258,f251,f244,f10884])).

fof(f604,plain,
    ( spl17_30
  <=> r2_hidden(sK6(sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_30])])).

fof(f607,plain,
    ( spl17_33
  <=> k1_xboole_0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_33])])).

fof(f7881,plain,
    ( r2_hidden(sK6(sK0,sK3,k3_orders_2(sK0,sK3,sK6(sK0,sK3,sK2))),sK3)
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_22
    | ~ spl17_30
    | ~ spl17_33 ),
    inference(subsumption_resolution,[],[f7880,f478])).

fof(f7880,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK6(sK0,sK3,k3_orders_2(sK0,sK3,sK6(sK0,sK3,sK2))),sK3)
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_30
    | ~ spl17_33 ),
    inference(subsumption_resolution,[],[f7873,f608])).

fof(f608,plain,
    ( k1_xboole_0 != sK3
    | ~ spl17_33 ),
    inference(avatar_component_clause,[],[f607])).

fof(f7873,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK6(sK0,sK3,k3_orders_2(sK0,sK3,sK6(sK0,sK3,sK2))),sK3)
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_30 ),
    inference(resolution,[],[f605,f801])).

fof(f801,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,X2)
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK6(sK0,X2,k3_orders_2(sK0,X2,X3)),X2) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f799,f798])).

fof(f798,plain,
    ( ! [X4,X5] :
        ( m1_subset_1(k3_orders_2(sK0,X4,X5),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X4 )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(duplicate_literal_removal,[],[f796])).

fof(f796,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 = X4
        | ~ r2_hidden(X5,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k3_orders_2(sK0,X4,X5),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(resolution,[],[f469,f351])).

fof(f469,plain,
    ( ! [X0,X1] :
        ( m1_orders_2(k3_orders_2(sK0,X1,X0),sK0,X1)
        | k1_xboole_0 = X1
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f468,f221])).

fof(f468,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1
        | ~ r2_hidden(X0,X1)
        | m1_orders_2(k3_orders_2(sK0,X1,X0),sK0,X1) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f467,f245])).

fof(f467,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | k1_xboole_0 = X1
        | ~ r2_hidden(X0,X1)
        | m1_orders_2(k3_orders_2(sK0,X1,X0),sK0,X1) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f466,f273])).

fof(f466,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | k1_xboole_0 = X1
        | ~ r2_hidden(X0,X1)
        | m1_orders_2(k3_orders_2(sK0,X1,X0),sK0,X1) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f465,f266])).

fof(f465,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | k1_xboole_0 = X1
        | ~ r2_hidden(X0,X1)
        | m1_orders_2(k3_orders_2(sK0,X1,X0),sK0,X1) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f464,f259])).

fof(f464,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | k1_xboole_0 = X1
        | ~ r2_hidden(X0,X1)
        | m1_orders_2(k3_orders_2(sK0,X1,X0),sK0,X1) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f463,f252])).

fof(f463,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | k1_xboole_0 = X1
        | ~ r2_hidden(X0,X1)
        | m1_orders_2(k3_orders_2(sK0,X1,X0),sK0,X1) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(duplicate_literal_removal,[],[f461])).

fof(f461,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | m1_orders_2(k3_orders_2(sK0,X1,X0),sK0,X1) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(resolution,[],[f359,f230])).

fof(f230,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k3_orders_2(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | m1_orders_2(k3_orders_2(X0,X1,X3),X0,X1) ) ),
    inference(equality_resolution,[],[f170])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | k3_orders_2(X0,X1,X3) != X2
      | m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f359,plain,
    ( ! [X28,X29] :
        ( m1_subset_1(k3_orders_2(sK0,X28,X29),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X29,u1_struct_0(sK0))
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f358,f245])).

fof(f358,plain,
    ( ! [X28,X29] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X29,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,X28,X29),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f357,f266])).

fof(f357,plain,
    ( ! [X28,X29] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X29,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,X28,X29),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f356,f259])).

fof(f356,plain,
    ( ! [X28,X29] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X29,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,X28,X29),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f289,f252])).

fof(f289,plain,
    ( ! [X28,X29] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X29,u1_struct_0(sK0))
        | m1_subset_1(k3_orders_2(sK0,X28,X29),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_8 ),
    inference(resolution,[],[f273,f207])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f122,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f121])).

fof(f121,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',dt_k3_orders_2)).

fof(f799,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = X2
        | ~ r2_hidden(X3,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_orders_2(sK0,X2,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK6(sK0,X2,k3_orders_2(sK0,X2,X3)),X2) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(duplicate_literal_removal,[],[f795])).

fof(f795,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = X2
        | ~ r2_hidden(X3,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k3_orders_2(sK0,X2,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | r2_hidden(sK6(sK0,X2,k3_orders_2(sK0,X2,X3)),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(resolution,[],[f469,f331])).

fof(f605,plain,
    ( r2_hidden(sK6(sK0,sK3,sK2),sK3)
    | ~ spl17_30 ),
    inference(avatar_component_clause,[],[f604])).

fof(f9912,plain,
    ( sK2 != sK3
    | r2_xboole_0(sK3,sK2)
    | ~ r2_xboole_0(sK2,sK3) ),
    introduced(theory_axiom,[])).

fof(f9565,plain,
    ( spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_20
    | ~ spl17_82
    | spl17_199 ),
    inference(avatar_contradiction_clause,[],[f9564])).

fof(f9564,plain,
    ( $false
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_20
    | ~ spl17_82
    | ~ spl17_199 ),
    inference(subsumption_resolution,[],[f9304,f4858])).

fof(f4858,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl17_199 ),
    inference(avatar_component_clause,[],[f4857])).

fof(f4857,plain,
    ( spl17_199
  <=> ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_199])])).

fof(f9304,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_20
    | ~ spl17_82 ),
    inference(backward_demodulation,[],[f9303,f406])).

fof(f406,plain,
    ( m2_orders_2(sK2,sK0,sK1)
    | ~ spl17_12 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl17_12
  <=> m2_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_12])])).

fof(f9303,plain,
    ( k1_xboole_0 = sK2
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_20
    | ~ spl17_82 ),
    inference(subsumption_resolution,[],[f9291,f459])).

fof(f9291,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_82 ),
    inference(resolution,[],[f1826,f323])).

fof(f323,plain,
    ( ! [X13] :
        ( ~ m1_orders_2(X13,sK0,X13)
        | k1_xboole_0 = X13
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f322,f245])).

fof(f322,plain,
    ( ! [X13] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X13
        | ~ m1_orders_2(X13,sK0,X13) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f321,f266])).

fof(f321,plain,
    ( ! [X13] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X13
        | ~ m1_orders_2(X13,sK0,X13) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f320,f259])).

fof(f320,plain,
    ( ! [X13] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X13
        | ~ m1_orders_2(X13,sK0,X13) )
    | ~ spl17_2
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f280,f252])).

fof(f280,plain,
    ( ! [X13] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X13
        | ~ m1_orders_2(X13,sK0,X13) )
    | ~ spl17_8 ),
    inference(resolution,[],[f273,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,X0,X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f62])).

fof(f62,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t68_orders_2)).

fof(f1826,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl17_82 ),
    inference(avatar_component_clause,[],[f1825])).

fof(f1825,plain,
    ( spl17_82
  <=> m1_orders_2(sK2,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_82])])).

fof(f9034,plain,
    ( ~ spl17_22
    | spl17_35
    | ~ spl17_44
    | ~ spl17_64
    | ~ spl17_208 ),
    inference(avatar_contradiction_clause,[],[f9033])).

fof(f9033,plain,
    ( $false
    | ~ spl17_22
    | ~ spl17_35
    | ~ spl17_44
    | ~ spl17_64
    | ~ spl17_208 ),
    inference(subsumption_resolution,[],[f9032,f4982])).

fof(f4982,plain,
    ( m1_subset_1(sK6(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl17_208 ),
    inference(avatar_component_clause,[],[f4981])).

fof(f4981,plain,
    ( spl17_208
  <=> m1_subset_1(sK6(sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_208])])).

fof(f9032,plain,
    ( ~ m1_subset_1(sK6(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl17_22
    | ~ spl17_35
    | ~ spl17_44
    | ~ spl17_64 ),
    inference(subsumption_resolution,[],[f9027,f618])).

fof(f618,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ spl17_35 ),
    inference(avatar_component_clause,[],[f617])).

fof(f617,plain,
    ( spl17_35
  <=> ~ r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_35])])).

fof(f9027,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK6(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl17_22
    | ~ spl17_44
    | ~ spl17_64 ),
    inference(superposition,[],[f8656,f671])).

fof(f671,plain,
    ( k3_orders_2(sK0,sK3,sK6(sK0,sK3,sK2)) = sK2
    | ~ spl17_44 ),
    inference(avatar_component_clause,[],[f670])).

fof(f670,plain,
    ( spl17_44
  <=> k3_orders_2(sK0,sK3,sK6(sK0,sK3,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_44])])).

fof(f8656,plain,
    ( ! [X3] :
        ( r1_tarski(k3_orders_2(sK0,sK3,X3),sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl17_22
    | ~ spl17_64 ),
    inference(superposition,[],[f177,f1514])).

fof(f1514,plain,
    ( ! [X3] :
        ( k3_xboole_0(sK3,k2_orders_2(sK0,k1_tarski(X3))) = k3_orders_2(sK0,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl17_22
    | ~ spl17_64 ),
    inference(forward_demodulation,[],[f1513,f178])).

fof(f1513,plain,
    ( ! [X3] :
        ( k3_xboole_0(k2_orders_2(sK0,k1_tarski(X3)),sK3) = k3_orders_2(sK0,sK3,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl17_22
    | ~ spl17_64 ),
    inference(subsumption_resolution,[],[f1500,f478])).

fof(f1500,plain,
    ( ! [X3] :
        ( k3_xboole_0(k2_orders_2(sK0,k1_tarski(X3)),sK3) = k3_orders_2(sK0,sK3,X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl17_22
    | ~ spl17_64 ),
    inference(superposition,[],[f1071,f820])).

fof(f820,plain,
    ( ! [X0] : k3_xboole_0(X0,sK3) = k9_subset_1(u1_struct_0(sK0),X0,sK3)
    | ~ spl17_22 ),
    inference(backward_demodulation,[],[f819,f487])).

fof(f487,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK3) = k9_subset_1(u1_struct_0(sK0),sK3,X0)
    | ~ spl17_22 ),
    inference(resolution,[],[f478,f206])).

fof(f819,plain,
    ( ! [X2] : k3_xboole_0(X2,sK3) = k9_subset_1(u1_struct_0(sK0),sK3,X2)
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f809,f478])).

fof(f809,plain,
    ( ! [X2] :
        ( k3_xboole_0(X2,sK3) = k9_subset_1(u1_struct_0(sK0),sK3,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_22 ),
    inference(superposition,[],[f487,f204])).

fof(f4983,plain,
    ( spl17_208
    | ~ spl17_22
    | ~ spl17_30 ),
    inference(avatar_split_clause,[],[f4971,f604,f477,f4981])).

fof(f4971,plain,
    ( m1_subset_1(sK6(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl17_22
    | ~ spl17_30 ),
    inference(resolution,[],[f4960,f478])).

fof(f4960,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | m1_subset_1(sK6(sK0,sK3,sK2),X0) )
    | ~ spl17_30 ),
    inference(resolution,[],[f605,f221])).

fof(f4886,plain,
    ( spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_14
    | ~ spl17_26
    | ~ spl17_198 ),
    inference(avatar_contradiction_clause,[],[f4885])).

fof(f4885,plain,
    ( $false
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_14
    | ~ spl17_26
    | ~ spl17_198 ),
    inference(subsumption_resolution,[],[f4878,f413])).

fof(f413,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl17_14 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl17_14
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_14])])).

fof(f4878,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_26
    | ~ spl17_198 ),
    inference(resolution,[],[f4861,f572])).

fof(f572,plain,
    ( ! [X1] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_26 ),
    inference(subsumption_resolution,[],[f571,f339])).

fof(f339,plain,
    ( ! [X21,X20] :
        ( v6_orders_2(X21,sK0)
        | ~ m2_orders_2(X21,sK0,X20)
        | ~ m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f338,f245])).

fof(f338,plain,
    ( ! [X21,X20] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X21,sK0,X20)
        | v6_orders_2(X21,sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f337,f266])).

fof(f337,plain,
    ( ! [X21,X20] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X21,sK0,X20)
        | v6_orders_2(X21,sK0) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f336,f259])).

fof(f336,plain,
    ( ! [X21,X20] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X21,sK0,X20)
        | v6_orders_2(X21,sK0) )
    | ~ spl17_2
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f284,f252])).

fof(f284,plain,
    ( ! [X21,X20] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X20,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X21,sK0,X20)
        | v6_orders_2(X21,sK0) )
    | ~ spl17_8 ),
    inference(resolution,[],[f273,f185])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | v6_orders_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
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
    inference(flattening,[],[f100])).

fof(f100,plain,(
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
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',dt_m2_orders_2)).

fof(f571,plain,
    ( ! [X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | ~ m2_orders_2(k1_xboole_0,sK0,X1) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_26 ),
    inference(subsumption_resolution,[],[f570,f245])).

fof(f570,plain,
    ( ! [X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(k1_xboole_0,sK0,X1) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_26 ),
    inference(subsumption_resolution,[],[f569,f273])).

fof(f569,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(k1_xboole_0,sK0,X1) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_26 ),
    inference(subsumption_resolution,[],[f568,f266])).

fof(f568,plain,
    ( ! [X1] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(k1_xboole_0,sK0,X1) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_26 ),
    inference(subsumption_resolution,[],[f567,f259])).

fof(f567,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(k1_xboole_0,sK0,X1) )
    | ~ spl17_2
    | ~ spl17_26 ),
    inference(subsumption_resolution,[],[f555,f252])).

fof(f555,plain,
    ( ! [X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(k1_xboole_0,sK0,X1) )
    | ~ spl17_26 ),
    inference(resolution,[],[f538,f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v6_orders_2(k1_xboole_0,X0)
      | v2_struct_0(X0)
      | ~ m2_orders_2(k1_xboole_0,X0,X1) ) ),
    inference(equality_resolution,[],[f162])).

fof(f162,plain,(
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
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
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
    inference(flattening,[],[f81])).

fof(f81,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',d16_orders_2)).

fof(f538,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_26 ),
    inference(avatar_component_clause,[],[f537])).

fof(f537,plain,
    ( spl17_26
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_26])])).

fof(f4861,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl17_198 ),
    inference(avatar_component_clause,[],[f4860])).

fof(f4860,plain,
    ( spl17_198
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_198])])).

fof(f4862,plain,
    ( spl17_198
    | ~ spl17_10
    | ~ spl17_32 ),
    inference(avatar_split_clause,[],[f4663,f610,f398,f4860])).

fof(f398,plain,
    ( spl17_10
  <=> m2_orders_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).

fof(f610,plain,
    ( spl17_32
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_32])])).

fof(f4663,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl17_10
    | ~ spl17_32 ),
    inference(backward_demodulation,[],[f611,f399])).

fof(f399,plain,
    ( m2_orders_2(sK3,sK0,sK1)
    | ~ spl17_10 ),
    inference(avatar_component_clause,[],[f398])).

fof(f611,plain,
    ( k1_xboole_0 = sK3
    | ~ spl17_32 ),
    inference(avatar_component_clause,[],[f610])).

fof(f1827,plain,
    ( spl17_82
    | ~ spl17_18
    | ~ spl17_34 ),
    inference(avatar_split_clause,[],[f1819,f620,f425,f1825])).

fof(f425,plain,
    ( spl17_18
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_18])])).

fof(f620,plain,
    ( spl17_34
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_34])])).

fof(f1819,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl17_18
    | ~ spl17_34 ),
    inference(forward_demodulation,[],[f426,f1748])).

fof(f1748,plain,
    ( sK2 = sK3
    | ~ spl17_18
    | ~ spl17_34 ),
    inference(subsumption_resolution,[],[f1053,f428])).

fof(f428,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ spl17_18 ),
    inference(subsumption_resolution,[],[f133,f426])).

fof(f133,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t84_orders_2)).

fof(f1053,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl17_34 ),
    inference(resolution,[],[f621,f196])).

fof(f621,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl17_34 ),
    inference(avatar_component_clause,[],[f620])).

fof(f426,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl17_18 ),
    inference(avatar_component_clause,[],[f425])).

fof(f1747,plain,
    ( spl17_78
    | spl17_80
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_14
    | spl17_19 ),
    inference(avatar_split_clause,[],[f1733,f422,f412,f405,f398,f272,f265,f258,f251,f244,f1745,f1739])).

fof(f1745,plain,
    ( spl17_80
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_80])])).

fof(f422,plain,
    ( spl17_19
  <=> ~ m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_19])])).

fof(f1733,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_14
    | ~ spl17_19 ),
    inference(subsumption_resolution,[],[f1729,f423])).

fof(f423,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ spl17_19 ),
    inference(avatar_component_clause,[],[f422])).

fof(f1729,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | m1_orders_2(sK3,sK0,sK2)
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_12
    | ~ spl17_14 ),
    inference(resolution,[],[f804,f406])).

fof(f804,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | sK3 = X0
        | m1_orders_2(X0,sK0,sK3)
        | m1_orders_2(sK3,sK0,X0) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_14 ),
    inference(resolution,[],[f525,f399])).

fof(f525,plain,
    ( ! [X2,X3] :
        ( ~ m2_orders_2(X2,sK0,sK1)
        | ~ m2_orders_2(X3,sK0,sK1)
        | X2 = X3
        | m1_orders_2(X3,sK0,X2)
        | m1_orders_2(X2,sK0,X3) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_14 ),
    inference(resolution,[],[f302,f413])).

fof(f302,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | ~ m2_orders_2(X2,sK0,X0)
        | X1 = X2
        | m1_orders_2(X2,sK0,X1)
        | m1_orders_2(X1,sK0,X2) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f301,f245])).

fof(f301,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | ~ m2_orders_2(X2,sK0,X0)
        | X1 = X2
        | m1_orders_2(X2,sK0,X1)
        | m1_orders_2(X1,sK0,X2) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f300,f266])).

fof(f300,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | ~ m2_orders_2(X2,sK0,X0)
        | X1 = X2
        | m1_orders_2(X2,sK0,X1)
        | m1_orders_2(X1,sK0,X2) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f299,f259])).

fof(f299,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | ~ m2_orders_2(X2,sK0,X0)
        | X1 = X2
        | m1_orders_2(X2,sK0,X1)
        | m1_orders_2(X1,sK0,X2) )
    | ~ spl17_2
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f275,f252])).

fof(f275,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X0)
        | ~ m2_orders_2(X2,sK0,X0)
        | X1 = X2
        | m1_orders_2(X2,sK0,X1)
        | m1_orders_2(X1,sK0,X2) )
    | ~ spl17_8 ),
    inference(resolution,[],[f273,f156])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m2_orders_2(X3,X0,X1)
      | X2 = X3
      | m1_orders_2(X3,X0,X2)
      | m1_orders_2(X2,X0,X3) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f65,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t83_orders_2)).

fof(f1277,plain,
    ( spl17_66
    | ~ spl17_62 ),
    inference(avatar_split_clause,[],[f1185,f1067,f1275])).

fof(f1185,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl17_62 ),
    inference(backward_demodulation,[],[f1077,f1068])).

fof(f1072,plain,
    ( spl17_62
    | spl17_64
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(avatar_split_clause,[],[f551,f272,f265,f258,f251,f244,f1070,f1067])).

fof(f551,plain,
    ( ! [X0,X1] :
        ( k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k1_tarski(X0)),X1) = k3_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(duplicate_literal_removal,[],[f540])).

fof(f540,plain,
    ( ! [X0,X1] :
        ( k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k1_tarski(X0)),X1) = k3_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(superposition,[],[f327,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',redefinition_k6_domain_1)).

fof(f327,plain,
    ( ! [X14,X15] :
        ( k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X15)),X14) = k3_orders_2(sK0,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f326,f245])).

fof(f326,plain,
    ( ! [X14,X15] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X15)),X14) = k3_orders_2(sK0,X14,X15) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f325,f266])).

fof(f325,plain,
    ( ! [X14,X15] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X15)),X14) = k3_orders_2(sK0,X14,X15) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f324,f259])).

fof(f324,plain,
    ( ! [X14,X15] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X15)),X14) = k3_orders_2(sK0,X14,X15) )
    | ~ spl17_2
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f281,f252])).

fof(f281,plain,
    ( ! [X14,X15] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X15)),X14) = k3_orders_2(sK0,X14,X15) )
    | ~ spl17_8 ),
    inference(resolution,[],[f273,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) = k3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) = k3_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) = k3_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) = k3_orders_2(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',d14_orders_2)).

fof(f1059,plain,
    ( spl17_20
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_14 ),
    inference(avatar_split_clause,[],[f443,f412,f405,f272,f265,f258,f251,f244,f458])).

fof(f443,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_14 ),
    inference(resolution,[],[f431,f406])).

fof(f431,plain,
    ( ! [X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_14 ),
    inference(resolution,[],[f343,f413])).

fof(f343,plain,
    ( ! [X23,X22] :
        ( ~ m1_orders_1(X22,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X23,sK0,X22)
        | m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f342,f245])).

fof(f342,plain,
    ( ! [X23,X22] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X22,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X23,sK0,X22)
        | m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f341,f266])).

fof(f341,plain,
    ( ! [X23,X22] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X22,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X23,sK0,X22)
        | m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f340,f259])).

fof(f340,plain,
    ( ! [X23,X22] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X22,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X23,sK0,X22)
        | m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_2
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f285,f252])).

fof(f285,plain,
    ( ! [X23,X22] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X22,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X23,sK0,X22)
        | m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_8 ),
    inference(resolution,[],[f273,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f1051,plain,
    ( ~ spl17_37
    | ~ spl17_16 ),
    inference(avatar_split_clause,[],[f615,f419,f627])).

fof(f419,plain,
    ( spl17_16
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_16])])).

fof(f615,plain,
    ( ~ r2_xboole_0(sK3,sK2)
    | ~ spl17_16 ),
    inference(resolution,[],[f420,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',antisymmetry_r2_xboole_0)).

fof(f420,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl17_16 ),
    inference(avatar_component_clause,[],[f419])).

fof(f672,plain,
    ( spl17_44
    | spl17_32
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_18
    | ~ spl17_20
    | ~ spl17_22 ),
    inference(avatar_split_clause,[],[f646,f477,f458,f425,f272,f265,f258,f251,f244,f610,f670])).

fof(f646,plain,
    ( k1_xboole_0 = sK3
    | k3_orders_2(sK0,sK3,sK6(sK0,sK3,sK2)) = sK2
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_18
    | ~ spl17_20
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f645,f478])).

fof(f645,plain,
    ( k1_xboole_0 = sK3
    | k3_orders_2(sK0,sK3,sK6(sK0,sK3,sK2)) = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_18
    | ~ spl17_20 ),
    inference(subsumption_resolution,[],[f642,f459])).

fof(f642,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3
    | k3_orders_2(sK0,sK3,sK6(sK0,sK3,sK2)) = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_18 ),
    inference(resolution,[],[f426,f335])).

fof(f612,plain,
    ( spl17_30
    | spl17_32
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_18
    | ~ spl17_20
    | ~ spl17_22 ),
    inference(avatar_split_clause,[],[f518,f477,f458,f425,f272,f265,f258,f251,f244,f610,f604])).

fof(f518,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(sK6(sK0,sK3,sK2),sK3)
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_18
    | ~ spl17_20
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f517,f478])).

fof(f517,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(sK6(sK0,sK3,sK2),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_18
    | ~ spl17_20 ),
    inference(subsumption_resolution,[],[f514,f459])).

fof(f514,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK3
    | r2_hidden(sK6(sK0,sK3,sK2),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_18 ),
    inference(resolution,[],[f331,f426])).

fof(f539,plain,
    ( spl17_26
    | ~ spl17_20 ),
    inference(avatar_split_clause,[],[f527,f458,f537])).

fof(f527,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_20 ),
    inference(superposition,[],[f522,f145])).

fof(f145,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',t2_boole)).

fof(f522,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_20 ),
    inference(superposition,[],[f511,f178])).

fof(f511,plain,
    ( ! [X1] : m1_subset_1(k3_xboole_0(X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_20 ),
    inference(forward_demodulation,[],[f510,f507])).

fof(f507,plain,
    ( ! [X1] : k3_xboole_0(X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1)
    | ~ spl17_20 ),
    inference(subsumption_resolution,[],[f501,f459])).

fof(f501,plain,
    ( ! [X1] :
        ( k3_xboole_0(X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_20 ),
    inference(superposition,[],[f470,f204])).

fof(f470,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0)
    | ~ spl17_20 ),
    inference(resolution,[],[f459,f206])).

fof(f510,plain,
    ( ! [X1] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_20 ),
    inference(subsumption_resolution,[],[f504,f459])).

fof(f504,plain,
    ( ! [X1] :
        ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl17_20 ),
    inference(superposition,[],[f203,f470])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t84_orders_2.p',dt_k9_subset_1)).

fof(f479,plain,
    ( spl17_22
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_14 ),
    inference(avatar_split_clause,[],[f442,f412,f398,f272,f265,f258,f251,f244,f477])).

fof(f442,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_8
    | ~ spl17_10
    | ~ spl17_14 ),
    inference(resolution,[],[f431,f399])).

fof(f427,plain,
    ( spl17_16
    | spl17_18 ),
    inference(avatar_split_clause,[],[f132,f425,f419])).

fof(f132,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f414,plain,(
    spl17_14 ),
    inference(avatar_split_clause,[],[f136,f412])).

fof(f136,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f72])).

fof(f407,plain,(
    spl17_12 ),
    inference(avatar_split_clause,[],[f135,f405])).

fof(f135,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f400,plain,(
    spl17_10 ),
    inference(avatar_split_clause,[],[f134,f398])).

fof(f134,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f274,plain,(
    spl17_8 ),
    inference(avatar_split_clause,[],[f141,f272])).

fof(f141,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f267,plain,(
    spl17_6 ),
    inference(avatar_split_clause,[],[f140,f265])).

fof(f140,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f260,plain,(
    spl17_4 ),
    inference(avatar_split_clause,[],[f139,f258])).

fof(f139,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f253,plain,(
    spl17_2 ),
    inference(avatar_split_clause,[],[f138,f251])).

fof(f138,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f246,plain,(
    ~ spl17_1 ),
    inference(avatar_split_clause,[],[f137,f244])).

fof(f137,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).
%------------------------------------------------------------------------------
