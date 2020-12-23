%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t38_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:29 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 895 expanded)
%              Number of leaves         :   60 ( 323 expanded)
%              Depth                    :   13
%              Number of atoms          :  674 (2260 expanded)
%              Number of equality atoms :   41 ( 264 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3202,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f103,f110,f117,f124,f131,f138,f145,f152,f160,f202,f215,f225,f235,f237,f253,f336,f363,f1510,f1520,f1525,f1535,f1546,f1556,f1570,f1574,f1649,f1685,f1919,f1961,f1978,f2042,f2043,f2121,f2164,f2174,f2245,f2246,f3201])).

fof(f3201,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_16
    | spl5_41 ),
    inference(avatar_contradiction_clause,[],[f3200])).

fof(f3200,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f3199,f362])).

fof(f362,plain,
    ( ~ v3_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl5_41
  <=> ~ v3_pre_topc(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f3199,plain,
    ( v3_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f3196,f151])).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl5_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f3196,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(resolution,[],[f2494,f130])).

fof(f130,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_10
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f2494,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k3_xboole_0(sK1,X0),sK0) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f2492,f144])).

fof(f144,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl5_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f2492,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k3_xboole_0(sK1,X0),sK0) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(resolution,[],[f844,f123])).

fof(f123,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_8
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f844,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X1,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k3_xboole_0(X1,X0),sK0) )
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f843,f102])).

fof(f102,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f843,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0)
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(k3_xboole_0(X1,X0),sK0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f84,f95])).

fof(f95,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',fc6_tops_1)).

fof(f2246,plain,
    ( spl5_46
    | spl5_28
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f2122,f150,f213,f1523])).

fof(f1523,plain,
    ( spl5_46
  <=> ! [X173] :
        ( m1_subset_1(X173,u1_struct_0(sK0))
        | ~ m1_subset_1(X173,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f213,plain,
    ( spl5_28
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f2122,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK2)
        | ~ m1_subset_1(X0,sK2)
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f2052,f73])).

fof(f73,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',idempotence_k3_xboole_0)).

fof(f2052,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | v1_xboole_0(k3_xboole_0(sK2,sK2))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_16 ),
    inference(superposition,[],[f1504,f73])).

fof(f1504,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X14,k3_xboole_0(X15,sK2))
        | v1_xboole_0(k3_xboole_0(X15,sK2))
        | m1_subset_1(X14,u1_struct_0(sK0)) )
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f1503,f308])).

fof(f308,plain,
    ( ! [X20] : k9_subset_1(u1_struct_0(sK0),X20,sK2) = k3_xboole_0(X20,sK2)
    | ~ spl5_16 ),
    inference(resolution,[],[f82,f151])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',redefinition_k9_subset_1)).

fof(f1503,plain,
    ( ! [X14,X15] :
        ( v1_xboole_0(k3_xboole_0(X15,sK2))
        | m1_subset_1(X14,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,k9_subset_1(u1_struct_0(sK0),X15,sK2)) )
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f1442,f308])).

fof(f1442,plain,
    ( ! [X14,X15] :
        ( m1_subset_1(X14,u1_struct_0(sK0))
        | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),X15,sK2))
        | ~ m1_subset_1(X14,k9_subset_1(u1_struct_0(sK0),X15,sK2)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f180,f246])).

fof(f246,plain,
    ( ! [X3] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(resolution,[],[f81,f151])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',dt_k9_subset_1)).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f85,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',t2_subset)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',t4_subset)).

fof(f2245,plain,
    ( spl5_70
    | spl5_28
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f2063,f150,f213,f2119])).

fof(f2119,plain,
    ( spl5_70
  <=> m1_subset_1(sK3(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f2063,plain,
    ( v1_xboole_0(sK2)
    | m1_subset_1(sK3(sK2),u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f2058,f73])).

fof(f2058,plain,
    ( m1_subset_1(sK3(sK2),u1_struct_0(sK0))
    | v1_xboole_0(k3_xboole_0(sK2,sK2))
    | ~ spl5_16 ),
    inference(superposition,[],[f2051,f73])).

fof(f2051,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k3_xboole_0(X0,sK2)),u1_struct_0(sK0))
        | v1_xboole_0(k3_xboole_0(X0,sK2)) )
    | ~ spl5_16 ),
    inference(resolution,[],[f1504,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',existence_m1_subset_1)).

fof(f2174,plain,
    ( ~ spl5_10
    | spl5_41
    | ~ spl5_48 ),
    inference(avatar_contradiction_clause,[],[f2173])).

fof(f2173,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_41
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f2172,f2124])).

fof(f2124,plain,
    ( v3_pre_topc(o_0_0_xboole_0,sK0)
    | ~ spl5_10
    | ~ spl5_48 ),
    inference(superposition,[],[f130,f1534])).

fof(f1534,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f1533])).

fof(f1533,plain,
    ( spl5_48
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f2172,plain,
    ( ~ v3_pre_topc(o_0_0_xboole_0,sK0)
    | ~ spl5_41
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f2133,f88])).

fof(f88,plain,(
    ! [X0] : o_0_0_xboole_0 = k3_xboole_0(X0,o_0_0_xboole_0) ),
    inference(forward_demodulation,[],[f70,f69])).

fof(f69,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',d2_xboole_0)).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',t2_boole)).

fof(f2133,plain,
    ( ~ v3_pre_topc(k3_xboole_0(sK1,o_0_0_xboole_0),sK0)
    | ~ spl5_41
    | ~ spl5_48 ),
    inference(superposition,[],[f362,f1534])).

fof(f2164,plain,
    ( ~ spl5_10
    | spl5_19
    | ~ spl5_48 ),
    inference(avatar_contradiction_clause,[],[f2163])).

fof(f2163,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_19
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f2162,f2124])).

fof(f2162,plain,
    ( ~ v3_pre_topc(o_0_0_xboole_0,sK0)
    | ~ spl5_19
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f2161,f1743])).

fof(f1743,plain,(
    ! [X2,X3] : k9_subset_1(X2,o_0_0_xboole_0,X3) = o_0_0_xboole_0 ),
    inference(superposition,[],[f1704,f1709])).

fof(f1709,plain,(
    ! [X6,X5] : k9_subset_1(X5,X6,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(forward_demodulation,[],[f1705,f88])).

fof(f1705,plain,(
    ! [X6,X5] : k9_subset_1(X5,X6,o_0_0_xboole_0) = k3_xboole_0(X6,o_0_0_xboole_0) ),
    inference(resolution,[],[f1697,f82])).

fof(f1697,plain,(
    ! [X5] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X5)) ),
    inference(superposition,[],[f1669,f161])).

fof(f161,plain,(
    ! [X1] : o_0_0_xboole_0 = k3_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[],[f74,f88])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',commutativity_k3_xboole_0)).

fof(f1669,plain,(
    ! [X4,X5] : m1_subset_1(k3_xboole_0(X5,sK3(k1_zfmisc_1(X4))),k1_zfmisc_1(X4)) ),
    inference(superposition,[],[f244,f309])).

fof(f309,plain,(
    ! [X21,X22] : k9_subset_1(X21,X22,sK3(k1_zfmisc_1(X21))) = k3_xboole_0(X22,sK3(k1_zfmisc_1(X21))) ),
    inference(resolution,[],[f82,f72])).

fof(f244,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(X0,X1,sK3(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f81,f72])).

fof(f1704,plain,(
    ! [X4,X3] : k9_subset_1(X3,X4,o_0_0_xboole_0) = k9_subset_1(X3,o_0_0_xboole_0,X4) ),
    inference(resolution,[],[f1697,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',commutativity_k9_subset_1)).

fof(f2161,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK1),sK0)
    | ~ spl5_19
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f2126,f1704])).

fof(f2126,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0),sK0)
    | ~ spl5_19
    | ~ spl5_48 ),
    inference(superposition,[],[f159,f1534])).

fof(f159,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl5_19
  <=> ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f2121,plain,
    ( spl5_70
    | ~ spl5_16
    | spl5_29 ),
    inference(avatar_split_clause,[],[f2064,f210,f150,f2119])).

fof(f210,plain,
    ( spl5_29
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f2064,plain,
    ( m1_subset_1(sK3(sK2),u1_struct_0(sK0))
    | ~ spl5_16
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f2063,f211])).

fof(f211,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f210])).

fof(f2043,plain,
    ( spl5_42
    | spl5_24
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1920,f143,f200,f1508])).

fof(f1508,plain,
    ( spl5_42
  <=> ! [X172] :
        ( m1_subset_1(X172,u1_struct_0(sK0))
        | ~ m1_subset_1(X172,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f200,plain,
    ( spl5_24
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f1920,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f1899,f73])).

fof(f1899,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(k3_xboole_0(sK1,sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_14 ),
    inference(superposition,[],[f1502,f73])).

fof(f1502,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,k3_xboole_0(X13,sK1))
        | v1_xboole_0(k3_xboole_0(X13,sK1))
        | m1_subset_1(X12,u1_struct_0(sK0)) )
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f1501,f307])).

fof(f307,plain,
    ( ! [X19] : k9_subset_1(u1_struct_0(sK0),X19,sK1) = k3_xboole_0(X19,sK1)
    | ~ spl5_14 ),
    inference(resolution,[],[f82,f144])).

fof(f1501,plain,
    ( ! [X12,X13] :
        ( v1_xboole_0(k3_xboole_0(X13,sK1))
        | m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,k9_subset_1(u1_struct_0(sK0),X13,sK1)) )
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f1441,f307])).

fof(f1441,plain,
    ( ! [X12,X13] :
        ( m1_subset_1(X12,u1_struct_0(sK0))
        | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),X13,sK1))
        | ~ m1_subset_1(X12,k9_subset_1(u1_struct_0(sK0),X13,sK1)) )
    | ~ spl5_14 ),
    inference(resolution,[],[f180,f245])).

fof(f245,plain,
    ( ! [X2] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(resolution,[],[f81,f144])).

fof(f2042,plain,
    ( spl5_68
    | spl5_24
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1910,f143,f200,f1917])).

fof(f1917,plain,
    ( spl5_68
  <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f1910,plain,
    ( v1_xboole_0(sK1)
    | m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f1905,f73])).

fof(f1905,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | v1_xboole_0(k3_xboole_0(sK1,sK1))
    | ~ spl5_14 ),
    inference(superposition,[],[f1898,f73])).

fof(f1898,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k3_xboole_0(X0,sK1)),u1_struct_0(sK0))
        | v1_xboole_0(k3_xboole_0(X0,sK1)) )
    | ~ spl5_14 ),
    inference(resolution,[],[f1502,f72])).

fof(f1978,plain,
    ( ~ spl5_8
    | spl5_41
    | ~ spl5_44 ),
    inference(avatar_contradiction_clause,[],[f1977])).

fof(f1977,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_41
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f1976,f1922])).

fof(f1922,plain,
    ( v3_pre_topc(o_0_0_xboole_0,sK0)
    | ~ spl5_8
    | ~ spl5_44 ),
    inference(superposition,[],[f123,f1519])).

fof(f1519,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f1518])).

fof(f1518,plain,
    ( spl5_44
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f1976,plain,
    ( ~ v3_pre_topc(o_0_0_xboole_0,sK0)
    | ~ spl5_41
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f1935,f161])).

fof(f1935,plain,
    ( ~ v3_pre_topc(k3_xboole_0(o_0_0_xboole_0,sK2),sK0)
    | ~ spl5_41
    | ~ spl5_44 ),
    inference(superposition,[],[f362,f1519])).

fof(f1961,plain,
    ( ~ spl5_8
    | spl5_19
    | ~ spl5_44 ),
    inference(avatar_contradiction_clause,[],[f1960])).

fof(f1960,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_19
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f1959,f1922])).

fof(f1959,plain,
    ( ~ v3_pre_topc(o_0_0_xboole_0,sK0)
    | ~ spl5_19
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f1924,f1743])).

fof(f1924,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,sK2),sK0)
    | ~ spl5_19
    | ~ spl5_44 ),
    inference(superposition,[],[f159,f1519])).

fof(f1919,plain,
    ( spl5_68
    | ~ spl5_14
    | spl5_25 ),
    inference(avatar_split_clause,[],[f1911,f197,f143,f1917])).

fof(f197,plain,
    ( spl5_25
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f1911,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f1910,f198])).

fof(f198,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f197])).

fof(f1685,plain,
    ( spl5_64
    | ~ spl5_67
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f1651,f1572,f1683,f1677])).

fof(f1677,plain,
    ( spl5_64
  <=> v1_xboole_0(sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f1683,plain,
    ( spl5_67
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f1572,plain,
    ( spl5_60
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f1651,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK3(sK2))
    | v1_xboole_0(sK3(sK2))
    | ~ spl5_60 ),
    inference(resolution,[],[f1573,f72])).

fof(f1573,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f1572])).

fof(f1649,plain,
    ( spl5_62
    | ~ spl5_14
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f1576,f1554,f143,f1647])).

fof(f1647,plain,
    ( spl5_62
  <=> m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f1554,plain,
    ( spl5_54
  <=> u1_struct_0(sK0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f1576,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_54 ),
    inference(superposition,[],[f144,f1555])).

fof(f1555,plain,
    ( u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f1554])).

fof(f1574,plain,
    ( spl5_50
    | spl5_60
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1536,f1523,f1572,f1541])).

fof(f1541,plain,
    ( spl5_50
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f1536,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | v1_xboole_0(X0)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),X0) )
    | ~ spl5_46 ),
    inference(resolution,[],[f1524,f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f171,f77])).

fof(f171,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f77,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',antisymmetry_r2_hidden)).

fof(f1524,plain,
    ( ! [X173] :
        ( m1_subset_1(X173,u1_struct_0(sK0))
        | ~ m1_subset_1(X173,sK2) )
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f1523])).

fof(f1570,plain,
    ( spl5_56
    | ~ spl5_59
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f1557,f1544,f1568,f1562])).

fof(f1562,plain,
    ( spl5_56
  <=> v1_xboole_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1568,plain,
    ( spl5_59
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f1544,plain,
    ( spl5_52
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f1557,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK3(sK1))
    | v1_xboole_0(sK3(sK1))
    | ~ spl5_52 ),
    inference(resolution,[],[f1545,f72])).

fof(f1545,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f1544])).

fof(f1556,plain,
    ( spl5_54
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1549,f1541,f1554])).

fof(f1549,plain,
    ( u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl5_50 ),
    inference(resolution,[],[f1542,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f71,f69])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',t6_boole)).

fof(f1542,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f1541])).

fof(f1546,plain,
    ( spl5_50
    | spl5_52
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1521,f1508,f1544,f1541])).

fof(f1521,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(X0)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),X0) )
    | ~ spl5_42 ),
    inference(resolution,[],[f1509,f173])).

fof(f1509,plain,
    ( ! [X172] :
        ( m1_subset_1(X172,u1_struct_0(sK0))
        | ~ m1_subset_1(X172,sK1) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f1508])).

fof(f1535,plain,
    ( spl5_48
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f1528,f213,f1533])).

fof(f1528,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl5_28 ),
    inference(resolution,[],[f214,f89])).

fof(f214,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f213])).

fof(f1525,plain,
    ( spl5_28
    | spl5_46
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1487,f150,f1523,f213])).

fof(f1487,plain,
    ( ! [X173] :
        ( m1_subset_1(X173,u1_struct_0(sK0))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X173,sK2) )
    | ~ spl5_16 ),
    inference(resolution,[],[f180,f151])).

fof(f1520,plain,
    ( spl5_44
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f1513,f200,f1518])).

fof(f1513,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl5_24 ),
    inference(resolution,[],[f201,f89])).

fof(f201,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f200])).

fof(f1510,plain,
    ( spl5_24
    | spl5_42
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1486,f143,f1508,f200])).

fof(f1486,plain,
    ( ! [X172] :
        ( m1_subset_1(X172,u1_struct_0(sK0))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X172,sK1) )
    | ~ spl5_14 ),
    inference(resolution,[],[f180,f144])).

fof(f363,plain,
    ( ~ spl5_41
    | ~ spl5_16
    | spl5_19 ),
    inference(avatar_split_clause,[],[f353,f158,f150,f361])).

fof(f353,plain,
    ( ~ v3_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl5_16
    | ~ spl5_19 ),
    inference(superposition,[],[f159,f308])).

fof(f336,plain,
    ( spl5_38
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f329,f143,f334])).

fof(f334,plain,
    ( spl5_38
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f329,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(superposition,[],[f320,f161])).

fof(f320,plain,
    ( ! [X2] : m1_subset_1(k3_xboole_0(X2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(superposition,[],[f245,f307])).

fof(f253,plain,
    ( spl5_36
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f241,f233,f251])).

fof(f251,plain,
    ( spl5_36
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f233,plain,
    ( spl5_34
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f241,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_34 ),
    inference(superposition,[],[f72,f234])).

fof(f234,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f233])).

fof(f237,plain,(
    ~ spl5_30 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl5_30 ),
    inference(resolution,[],[f218,f72])).

fof(f218,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl5_30
  <=> ! [X0] : ~ m1_subset_1(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f235,plain,
    ( spl5_34
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f228,f223,f233])).

fof(f223,plain,
    ( spl5_32
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f228,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_32 ),
    inference(resolution,[],[f224,f89])).

fof(f224,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,
    ( spl5_30
    | spl5_32
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f176,f108,f223,f217])).

fof(f108,plain,
    ( spl5_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f176,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
        | ~ m1_subset_1(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f175,f77])).

fof(f175,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_4 ),
    inference(resolution,[],[f174,f72])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f86,f109])).

fof(f109,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',t5_subset)).

fof(f215,plain,
    ( ~ spl5_27
    | spl5_22
    | spl5_28
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f183,f150,f213,f194,f207])).

fof(f207,plain,
    ( spl5_27
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f194,plain,
    ( spl5_22
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f183,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)
    | ~ spl5_16 ),
    inference(resolution,[],[f173,f151])).

fof(f202,plain,
    ( ~ spl5_21
    | spl5_22
    | spl5_24
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f182,f143,f200,f194,f188])).

fof(f188,plain,
    ( spl5_21
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f182,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)
    | ~ spl5_14 ),
    inference(resolution,[],[f173,f144])).

fof(f160,plain,(
    ~ spl5_19 ),
    inference(avatar_split_clause,[],[f67,f158])).

fof(f67,plain,(
    ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f55,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v3_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v3_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v3_pre_topc(X2,X0)
            & v3_pre_topc(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v3_pre_topc(X2,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v3_pre_topc(sK2,X0)
        & v3_pre_topc(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v3_pre_topc(X1,X0) )
               => v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',t38_tops_1)).

fof(f152,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f64,f150])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f145,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f63,f143])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f138,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f69,f136])).

fof(f136,plain,
    ( spl5_12
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f131,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f66,f129])).

fof(f66,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f124,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f65,f122])).

fof(f65,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f117,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f87,f115])).

fof(f115,plain,
    ( spl5_6
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f87,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f59])).

fof(f59,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK4) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',existence_l1_pre_topc)).

fof(f110,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f68,f108])).

fof(f68,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t38_tops_1.p',dt_o_0_0_xboole_0)).

fof(f103,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f62,f101])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f61,f94])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
