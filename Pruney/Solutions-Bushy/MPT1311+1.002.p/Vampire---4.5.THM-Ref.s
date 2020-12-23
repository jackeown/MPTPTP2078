%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1311+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:42 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 285 expanded)
%              Number of leaves         :   44 ( 126 expanded)
%              Depth                    :    7
%              Number of atoms          :  545 ( 864 expanded)
%              Number of equality atoms :   57 (  90 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f332,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f71,f75,f79,f83,f87,f91,f95,f99,f104,f108,f112,f117,f121,f137,f142,f153,f157,f162,f169,f177,f185,f204,f214,f242,f260,f269,f284,f292,f308,f318,f331])).

fof(f331,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_25
    | spl6_46
    | ~ spl6_48 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_25
    | spl6_46
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f329,f307])).

fof(f307,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | spl6_46 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl6_46
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f329,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_25
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f328,f66])).

fof(f66,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl6_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f328,plain,
    ( ~ v2_pre_topc(sK0)
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl6_2
    | ~ spl6_25
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f325,f70])).

fof(f70,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f325,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl6_25
    | ~ spl6_48 ),
    inference(resolution,[],[f317,f176])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v4_pre_topc(k1_xboole_0,X0) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl6_25
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | v4_pre_topc(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f317,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl6_48
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f318,plain,
    ( spl6_48
    | ~ spl6_7
    | ~ spl6_20
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f300,f237,f151,f89,f316])).

fof(f89,plain,
    ( spl6_7
  <=> k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f151,plain,
    ( spl6_20
  <=> m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f237,plain,
    ( spl6_37
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f300,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_7
    | ~ spl6_20
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f297,f90])).

fof(f90,plain,
    ( k1_xboole_0 = k1_setfam_1(k1_xboole_0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f297,plain,
    ( m1_subset_1(k1_setfam_1(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_20
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f152,f238])).

fof(f238,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f237])).

fof(f152,plain,
    ( m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f151])).

fof(f308,plain,
    ( ~ spl6_46
    | ~ spl6_7
    | spl6_17
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f298,f237,f135,f89,f306])).

fof(f135,plain,
    ( spl6_17
  <=> v4_pre_topc(k1_setfam_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f298,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl6_7
    | spl6_17
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f295,f90])).

fof(f295,plain,
    ( ~ v4_pre_topc(k1_setfam_1(k1_xboole_0),sK0)
    | spl6_17
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f136,f238])).

fof(f136,plain,
    ( ~ v4_pre_topc(k1_setfam_1(sK1),sK0)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f135])).

fof(f292,plain,
    ( ~ spl6_2
    | spl6_17
    | ~ spl6_20
    | ~ spl6_23
    | ~ spl6_42 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl6_2
    | spl6_17
    | ~ spl6_20
    | ~ spl6_23
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f290,f136])).

fof(f290,plain,
    ( v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ spl6_2
    | ~ spl6_20
    | ~ spl6_23
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f289,f70])).

fof(f289,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ spl6_20
    | ~ spl6_23
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f287,f152])).

fof(f287,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ spl6_23
    | ~ spl6_42 ),
    inference(resolution,[],[f259,f168])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | v4_pre_topc(X1,X0) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl6_23
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
        | v4_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f259,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl6_42
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f284,plain,
    ( ~ spl6_4
    | ~ spl6_13
    | spl6_41 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_13
    | spl6_41 ),
    inference(subsumption_resolution,[],[f281,f78])).

fof(f78,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f281,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_13
    | spl6_41 ),
    inference(resolution,[],[f256,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_13
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f256,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_41 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl6_41
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f269,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_27
    | spl6_40 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_27
    | spl6_40 ),
    inference(unit_resulting_resolution,[],[f70,f74,f78,f253,f184])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
        | ~ v2_tops_2(X1,X0) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl6_27
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
        | ~ v2_tops_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f253,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | spl6_40 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl6_40
  <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f74,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_3
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f260,plain,
    ( ~ spl6_40
    | ~ spl6_41
    | spl6_42
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_31
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f249,f240,f202,f69,f65,f258,f255,f252])).

fof(f202,plain,
    ( spl6_31
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(X1,X0)
        | v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f240,plain,
    ( spl6_38
  <=> k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f249,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_31
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f248,f66])).

fof(f248,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_31
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f247,f70])).

fof(f247,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_31
    | ~ spl6_38 ),
    inference(superposition,[],[f203,f241])).

fof(f241,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f240])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(X1,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f202])).

fof(f242,plain,
    ( spl6_37
    | spl6_38
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f232,f212,f140,f77,f240,f237])).

fof(f140,plain,
    ( spl6_18
  <=> k6_setfam_1(u1_struct_0(sK0),sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f212,plain,
    ( spl6_33
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k1_xboole_0 = X1
        | k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f232,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))
    | k1_xboole_0 = sK1
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f229,f78])).

fof(f229,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_setfam_1(sK1))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_18
    | ~ spl6_33 ),
    inference(superposition,[],[f213,f141])).

fof(f141,plain,
    ( k6_setfam_1(u1_struct_0(sK0),sK1) = k1_setfam_1(sK1)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f140])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f212])).

fof(f214,plain,(
    spl6_33 ),
    inference(avatar_split_clause,[],[f55,f212])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

fof(f204,plain,(
    spl6_31 ),
    inference(avatar_split_clause,[],[f43,f202])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v1_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v1_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
           => v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tops_2)).

fof(f185,plain,(
    spl6_27 ),
    inference(avatar_split_clause,[],[f41,f183])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

fof(f177,plain,
    ( spl6_25
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f164,f160,f155,f175])).

fof(f155,plain,
    ( spl6_21
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(X1)
        | v4_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f160,plain,
    ( spl6_22
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | v4_pre_topc(k1_xboole_0,X0) )
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(resolution,[],[f161,f156])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | v4_pre_topc(X1,X0) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f155])).

fof(f161,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f160])).

fof(f169,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f38,f167])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f162,plain,
    ( spl6_22
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f131,f119,f93,f85,f160])).

fof(f85,plain,
    ( spl6_6
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f93,plain,
    ( spl6_8
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | v1_xboole_0(k1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f119,plain,
    ( spl6_14
  <=> k1_xboole_0 = k1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f131,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f130,f86])).

fof(f86,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f130,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK5)
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(superposition,[],[f94,f120])).

fof(f120,plain,
    ( k1_xboole_0 = k1_struct_0(sK5)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f94,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_struct_0(X0))
        | ~ l1_struct_0(X0) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f157,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f42,f155])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f153,plain,
    ( spl6_20
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f148,f140,f110,f77,f151])).

fof(f110,plain,
    ( spl6_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f148,plain,
    ( m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f147,f78])).

fof(f147,plain,
    ( m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(superposition,[],[f111,f141])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f142,plain,
    ( spl6_18
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f132,f106,f77,f140])).

fof(f106,plain,
    ( spl6_11
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f132,plain,
    ( k6_setfam_1(u1_struct_0(sK0),sK1) = k1_setfam_1(sK1)
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(resolution,[],[f107,f78])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k6_setfam_1(X0,X1) = k1_setfam_1(X1) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f137,plain,
    ( ~ spl6_17
    | ~ spl6_4
    | spl6_5
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f133,f106,f81,f77,f135])).

fof(f81,plain,
    ( spl6_5
  <=> v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f133,plain,
    ( ~ v4_pre_topc(k1_setfam_1(sK1),sK0)
    | ~ spl6_4
    | spl6_5
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f82,f132])).

fof(f82,plain,
    ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f121,plain,
    ( spl6_14
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f113,f102,f85,f119])).

fof(f102,plain,
    ( spl6_10
  <=> ! [X0] :
        ( k1_xboole_0 = k1_struct_0(X0)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f113,plain,
    ( k1_xboole_0 = k1_struct_0(sK5)
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(resolution,[],[f103,f86])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k1_xboole_0 = k1_struct_0(X0) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f117,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f54,f115])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f112,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f53,f110])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).

fof(f108,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f52,f106])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f104,plain,
    ( spl6_10
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f100,f97,f93,f102])).

fof(f97,plain,
    ( spl6_9
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f100,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_struct_0(X0)
        | ~ l1_struct_0(X0) )
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f98,f94])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f99,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f37,f97])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f95,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f36,f93])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_xboole_0(k1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

fof(f91,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f58,f89])).

fof(f58,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(k1_xboole_0) != X1 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f87,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f56,f85])).

fof(f56,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_l1_struct_0)).

fof(f83,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f33,f81])).

fof(f33,plain,(
    ~ v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
             => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_2)).

fof(f79,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f31,f77])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f71,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f35,f69])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
