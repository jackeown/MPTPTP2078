%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t29_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:38 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 252 expanded)
%              Number of leaves         :   35 ( 104 expanded)
%              Depth                    :    9
%              Number of atoms          :  418 ( 670 expanded)
%              Number of equality atoms :   44 (  62 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f401,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f128,f133,f137,f143,f147,f154,f158,f180,f184,f190,f203,f208,f212,f234,f242,f264,f344,f377,f390,f395,f400])).

fof(f400,plain,
    ( ~ spl8_2
    | ~ spl8_20
    | spl8_33
    | ~ spl8_72 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_33
    | ~ spl8_72 ),
    inference(subsumption_resolution,[],[f398,f233])).

fof(f233,plain,
    ( ~ v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl8_33
  <=> ~ v4_pre_topc(k1_setfam_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f398,plain,
    ( v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_72 ),
    inference(subsumption_resolution,[],[f397,f127])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f397,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ spl8_20
    | ~ spl8_72 ),
    inference(subsumption_resolution,[],[f396,f189])).

fof(f189,plain,
    ( m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl8_20
  <=> m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f396,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ spl8_72 ),
    inference(resolution,[],[f394,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',t29_tops_1)).

fof(f394,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0)
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl8_72
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f395,plain,
    ( spl8_72
    | ~ spl8_58
    | ~ spl8_70 ),
    inference(avatar_split_clause,[],[f391,f388,f342,f393])).

fof(f342,plain,
    ( spl8_58
  <=> k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)) = k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f388,plain,
    ( spl8_70
  <=> v3_pre_topc(k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f391,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0)
    | ~ spl8_58
    | ~ spl8_70 ),
    inference(forward_demodulation,[],[f389,f343])).

fof(f343,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)) = k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f342])).

fof(f389,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f388])).

fof(f390,plain,
    ( spl8_70
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_18
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f278,f240,f182,f126,f122,f388])).

fof(f122,plain,
    ( spl8_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f182,plain,
    ( spl8_18
  <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f240,plain,
    ( spl8_36
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f278,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_18
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f277,f183])).

fof(f183,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f182])).

fof(f277,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | v3_pre_topc(k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f276,f123])).

fof(f123,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f122])).

fof(f276,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | v3_pre_topc(k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl8_2
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f265,f127])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | v3_pre_topc(k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl8_36 ),
    inference(resolution,[],[f241,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tops_2(X1,X0)
      | v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v1_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v1_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
           => v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',t26_tops_2)).

fof(f241,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f240])).

fof(f377,plain,
    ( spl8_33
    | ~ spl8_42
    | ~ spl8_56 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl8_33
    | ~ spl8_42
    | ~ spl8_56 ),
    inference(subsumption_resolution,[],[f375,f263])).

fof(f263,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl8_42
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f375,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_33
    | ~ spl8_56 ),
    inference(forward_demodulation,[],[f362,f116])).

fof(f116,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(k1_xboole_0) != X1 ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',d1_setfam_1)).

fof(f362,plain,
    ( ~ v4_pre_topc(k1_setfam_1(k1_xboole_0),sK0)
    | ~ spl8_33
    | ~ spl8_56 ),
    inference(superposition,[],[f233,f340])).

fof(f340,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl8_56
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f344,plain,
    ( spl8_56
    | spl8_58
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f175,f145,f342,f339])).

fof(f145,plain,
    ( spl8_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f175,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)) = k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | k1_xboole_0 = sK1
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f166,f164])).

fof(f164,plain,
    ( k6_setfam_1(u1_struct_0(sK0),sK1) = k1_setfam_1(sK1)
    | ~ spl8_10 ),
    inference(resolution,[],[f146,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',redefinition_k6_setfam_1)).

fof(f146,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f166,plain,
    ( k1_xboole_0 = sK1
    | k3_subset_1(u1_struct_0(sK0),k6_setfam_1(u1_struct_0(sK0),sK1)) = k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl8_10 ),
    inference(resolution,[],[f146,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',t12_tops_2)).

fof(f264,plain,
    ( spl8_42
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f251,f210,f178,f126,f122,f262])).

fof(f178,plain,
    ( spl8_16
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f210,plain,
    ( spl8_26
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f251,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f250,f179])).

fof(f179,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f178])).

fof(f250,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f249,f123])).

fof(f249,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_2
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f244,f127])).

fof(f244,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_26 ),
    inference(resolution,[],[f211,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',cc2_pre_topc)).

fof(f211,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f210])).

fof(f242,plain,
    ( spl8_36
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f162,f145,f240])).

fof(f162,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_10 ),
    inference(resolution,[],[f146,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',dt_k7_setfam_1)).

fof(f234,plain,
    ( ~ spl8_33
    | spl8_13
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f213,f206,f152,f232])).

fof(f152,plain,
    ( spl8_13
  <=> ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f206,plain,
    ( spl8_24
  <=> k6_setfam_1(u1_struct_0(sK0),sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f213,plain,
    ( ~ v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ spl8_13
    | ~ spl8_24 ),
    inference(superposition,[],[f153,f207])).

fof(f207,plain,
    ( k6_setfam_1(u1_struct_0(sK0),sK1) = k1_setfam_1(sK1)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f206])).

fof(f153,plain,
    ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f212,plain,
    ( spl8_26
    | ~ spl8_14
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f204,f201,f156,f210])).

fof(f156,plain,
    ( spl8_14
  <=> k1_xboole_0 = k1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f201,plain,
    ( spl8_22
  <=> m1_subset_1(k1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f204,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_14
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f202,f157])).

fof(f157,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f202,plain,
    ( m1_subset_1(k1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f201])).

fof(f208,plain,
    ( spl8_24
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f164,f145,f206])).

fof(f203,plain,
    ( spl8_22
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f139,f131,f201])).

fof(f131,plain,
    ( spl8_4
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f139,plain,
    ( m1_subset_1(k1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_4 ),
    inference(resolution,[],[f132,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',dt_k1_struct_0)).

fof(f132,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f190,plain,
    ( spl8_20
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f174,f145,f188])).

fof(f174,plain,
    ( m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f165,f164])).

fof(f165,plain,
    ( m1_subset_1(k6_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_10 ),
    inference(resolution,[],[f146,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',dt_k6_setfam_1)).

fof(f184,plain,
    ( spl8_18
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f173,f145,f135,f126,f182])).

fof(f135,plain,
    ( spl8_6
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f173,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f172,f136])).

fof(f136,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f172,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_2(sK1,sK0)
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f160,f127])).

fof(f160,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_2(sK1,sK0)
    | ~ spl8_10 ),
    inference(resolution,[],[f146,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',t16_tops_2)).

fof(f180,plain,
    ( spl8_16
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f176,f156,f141,f178])).

fof(f141,plain,
    ( spl8_8
  <=> v1_xboole_0(k1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f176,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(superposition,[],[f142,f157])).

fof(f142,plain,
    ( v1_xboole_0(k1_struct_0(sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f141])).

fof(f158,plain,
    ( spl8_14
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f148,f141,f156])).

fof(f148,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f142,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',t6_boole)).

fof(f154,plain,(
    ~ spl8_13 ),
    inference(avatar_split_clause,[],[f75,f152])).

fof(f75,plain,(
    ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
             => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',t29_tops_2)).

fof(f147,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f73,f145])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f143,plain,
    ( spl8_8
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f138,f131,f141])).

fof(f138,plain,
    ( v1_xboole_0(k1_struct_0(sK0))
    | ~ spl8_4 ),
    inference(resolution,[],[f132,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_xboole_0(k1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',fc3_struct_0)).

fof(f137,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f74,f135])).

fof(f74,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f133,plain,
    ( spl8_4
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f129,f126,f131])).

fof(f129,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f127,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t29_tops_2.p',dt_l1_pre_topc)).

fof(f128,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f77,f126])).

fof(f77,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f124,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f76,f122])).

fof(f76,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
