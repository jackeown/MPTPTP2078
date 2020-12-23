%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 321 expanded)
%              Number of leaves         :   43 ( 150 expanded)
%              Depth                    :    9
%              Number of atoms          :  494 (1004 expanded)
%              Number of equality atoms :   88 ( 195 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1061,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f82,f103,f104,f109,f114,f119,f131,f134,f199,f202,f208,f214,f221,f235,f240,f242,f245,f267,f507,f512,f523,f531,f547,f553,f571,f1051])).

fof(f1051,plain,
    ( spl7_73
    | ~ spl7_24
    | ~ spl7_62
    | ~ spl7_68
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f1050,f550,f537,f504,f211,f567])).

fof(f567,plain,
    ( spl7_73
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f211,plain,
    ( spl7_24
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f504,plain,
    ( spl7_62
  <=> sP2(k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f537,plain,
    ( spl7_68
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f550,plain,
    ( spl7_70
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f1050,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl7_24
    | ~ spl7_62
    | ~ spl7_68
    | ~ spl7_70 ),
    inference(forward_demodulation,[],[f1049,f584])).

fof(f584,plain,
    ( ! [X0] : k9_subset_1(k2_pre_topc(sK0,sK1),X0,X0) = X0
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f506,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ sP2(X0) ) ),
    inference(general_splitting,[],[f48,f61_D])).

fof(f61,plain,(
    ! [X2,X0] :
      ( sP2(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61_D])).

fof(f61_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    <=> ~ sP2(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f506,plain,
    ( sP2(k2_pre_topc(sK0,sK1))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f504])).

fof(f1049,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1)
    | ~ spl7_24
    | ~ spl7_68
    | ~ spl7_70 ),
    inference(forward_demodulation,[],[f1048,f495])).

fof(f495,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X0)
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f213,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f213,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f211])).

fof(f1048,plain,
    ( k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
    | ~ spl7_24
    | ~ spl7_68
    | ~ spl7_70 ),
    inference(forward_demodulation,[],[f1009,f539])).

fof(f539,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f537])).

fof(f1009,plain,
    ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl7_24
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f213,f552,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f552,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f550])).

fof(f571,plain,
    ( ~ spl7_9
    | ~ spl7_73
    | spl7_26 ),
    inference(avatar_split_clause,[],[f565,f227,f567,f106])).

fof(f106,plain,
    ( spl7_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f227,plain,
    ( spl7_26
  <=> sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f565,plain,
    ( sK1 != k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_26 ),
    inference(superposition,[],[f228,f47])).

fof(f228,plain,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f227])).

fof(f553,plain,
    ( spl7_70
    | ~ spl7_63
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f548,f515,f509,f550])).

fof(f509,plain,
    ( spl7_63
  <=> m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f515,plain,
    ( spl7_64
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f548,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl7_63
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f511,f517])).

fof(f517,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f515])).

fof(f511,plain,
    ( m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f509])).

fof(f547,plain,
    ( spl7_68
    | ~ spl7_64
    | ~ spl7_65 ),
    inference(avatar_split_clause,[],[f546,f520,f515,f537])).

fof(f520,plain,
    ( spl7_65
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f546,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl7_64
    | ~ spl7_65 ),
    inference(backward_demodulation,[],[f522,f517])).

fof(f522,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f520])).

fof(f531,plain,
    ( spl7_64
    | ~ spl7_21
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f530,f211,f190,f515])).

fof(f190,plain,
    ( spl7_21
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f530,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl7_21
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f502,f191])).

fof(f191,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f190])).

fof(f502,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl7_24 ),
    inference(resolution,[],[f213,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f523,plain,
    ( spl7_65
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f498,f211,f520])).

fof(f498,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f213,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f512,plain,
    ( spl7_63
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f500,f211,f509])).

fof(f500,plain,
    ( m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f213,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f507,plain,
    ( spl7_62
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f501,f211,f504])).

fof(f501,plain,
    ( sP2(k2_pre_topc(sK0,sK1))
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f213,f61])).

fof(f267,plain,
    ( spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f266,f218,f111,f106,f100])).

fof(f100,plain,
    ( spl7_8
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f111,plain,
    ( spl7_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f218,plain,
    ( spl7_25
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f266,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f264,f220])).

fof(f220,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f218])).

fof(f264,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f113,f108,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f108,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f113,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f245,plain,
    ( spl7_7
    | ~ spl7_23
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f244,f218,f205,f96])).

fof(f96,plain,
    ( spl7_7
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f205,plain,
    ( spl7_23
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f244,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl7_23
    | ~ spl7_25 ),
    inference(backward_demodulation,[],[f207,f220])).

fof(f207,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f205])).

fof(f242,plain,
    ( spl7_25
    | ~ spl7_26
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f241,f232,f227,f218])).

fof(f232,plain,
    ( spl7_27
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f241,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl7_26
    | ~ spl7_27 ),
    inference(backward_demodulation,[],[f234,f229])).

fof(f229,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f227])).

fof(f234,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f232])).

fof(f240,plain,
    ( ~ spl7_20
    | spl7_21
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f238,f100,f190,f186])).

fof(f186,plain,
    ( spl7_20
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f238,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_8 ),
    inference(superposition,[],[f47,f101])).

fof(f101,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f235,plain,
    ( spl7_27
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f223,f111,f106,f232])).

fof(f223,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f113,f108,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f221,plain,
    ( spl7_25
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f215,f111,f106,f96,f76,f218])).

fof(f76,plain,
    ( spl7_2
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f215,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f113,f97,f108,f77])).

fof(f77,plain,
    ( ! [X3,X1] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f97,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f214,plain,
    ( spl7_24
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f209,f196,f211])).

fof(f196,plain,
    ( spl7_22
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f209,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f198,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f198,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f196])).

fof(f208,plain,
    ( spl7_23
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f203,f116,f111,f106,f205])).

fof(f116,plain,
    ( spl7_11
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f203,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f118,f113,f108,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f118,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f202,plain,
    ( spl7_20
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f200,f111,f106,f186])).

fof(f200,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f113,f108,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f199,plain,
    ( spl7_22
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f194,f111,f106,f196])).

fof(f194,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f113,f108,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f134,plain,
    ( spl7_13
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f132,f106,f128])).

fof(f128,plain,
    ( spl7_13
  <=> sP5(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f132,plain,
    ( sP5(sK0)
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f108,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( sP5(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f67_D])).

fof(f67_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    <=> ~ sP5(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f131,plain,
    ( ~ spl7_13
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f126,f116,f111,f80,f128])).

fof(f80,plain,
    ( spl7_3
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ sP5(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f126,plain,
    ( ~ sP5(sK0)
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f118,f113,f81])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ sP5(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f119,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f42,f116])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f114,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f43,f111])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f44,f106])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f104,plain,
    ( spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f45,f100,f96])).

fof(f45,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f103,plain,
    ( ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f46,f100,f96])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f69,f80,f72])).

fof(f72,plain,
    ( spl7_1
  <=> sP6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP5(X0)
      | sP6 ) ),
    inference(cnf_transformation,[],[f69_D])).

fof(f69_D,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ sP5(X0) )
  <=> ~ sP6 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f78,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f70,f76,f72])).

fof(f70,plain,(
    ! [X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ sP6 ) ),
    inference(general_splitting,[],[f68,f69_D])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP5(X0) ) ),
    inference(general_splitting,[],[f52,f67_D])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (31788)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.46  % (31796)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.49  % (31786)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.49  % (31780)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (31779)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (31797)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (31791)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (31790)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.51  % (31778)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.51  % (31778)Refutation not found, incomplete strategy% (31778)------------------------------
% 0.20/0.51  % (31778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31778)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31778)Memory used [KB]: 10618
% 0.20/0.51  % (31778)Time elapsed: 0.092 s
% 0.20/0.51  % (31778)------------------------------
% 0.20/0.51  % (31778)------------------------------
% 0.20/0.51  % (31789)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (31775)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (31785)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.51  % (31781)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.51  % (31785)Refutation not found, incomplete strategy% (31785)------------------------------
% 0.20/0.51  % (31785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31785)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31785)Memory used [KB]: 10618
% 0.20/0.51  % (31785)Time elapsed: 0.101 s
% 0.20/0.51  % (31785)------------------------------
% 0.20/0.51  % (31785)------------------------------
% 0.20/0.51  % (31782)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (31784)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  % (31794)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.52  % (31793)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.52  % (31787)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.52  % (31783)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.52  % (31777)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.52  % (31795)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.53  % (31776)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.54  % (31792)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.54  % (31781)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f1061,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f78,f82,f103,f104,f109,f114,f119,f131,f134,f199,f202,f208,f214,f221,f235,f240,f242,f245,f267,f507,f512,f523,f531,f547,f553,f571,f1051])).
% 0.20/0.54  fof(f1051,plain,(
% 0.20/0.54    spl7_73 | ~spl7_24 | ~spl7_62 | ~spl7_68 | ~spl7_70),
% 0.20/0.54    inference(avatar_split_clause,[],[f1050,f550,f537,f504,f211,f567])).
% 0.20/0.54  fof(f567,plain,(
% 0.20/0.54    spl7_73 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).
% 0.20/0.54  fof(f211,plain,(
% 0.20/0.54    spl7_24 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.20/0.54  fof(f504,plain,(
% 0.20/0.54    spl7_62 <=> sP2(k2_pre_topc(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 0.20/0.54  fof(f537,plain,(
% 0.20/0.54    spl7_68 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 0.20/0.54  fof(f550,plain,(
% 0.20/0.54    spl7_70 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 0.20/0.54  fof(f1050,plain,(
% 0.20/0.54    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl7_24 | ~spl7_62 | ~spl7_68 | ~spl7_70)),
% 0.20/0.54    inference(forward_demodulation,[],[f1049,f584])).
% 0.20/0.54  fof(f584,plain,(
% 0.20/0.54    ( ! [X0] : (k9_subset_1(k2_pre_topc(sK0,sK1),X0,X0) = X0) ) | ~spl7_62),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f506,f62])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~sP2(X0)) )),
% 0.20/0.54    inference(general_splitting,[],[f48,f61_D])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X2,X0] : (sP2(X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f61_D])).
% 0.20/0.54  fof(f61_D,plain,(
% 0.20/0.54    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(X0)) ) <=> ~sP2(X0)) )),
% 0.20/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 0.20/0.54  fof(f506,plain,(
% 0.20/0.54    sP2(k2_pre_topc(sK0,sK1)) | ~spl7_62),
% 0.20/0.54    inference(avatar_component_clause,[],[f504])).
% 0.20/0.54  fof(f1049,plain,(
% 0.20/0.54    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) | (~spl7_24 | ~spl7_68 | ~spl7_70)),
% 0.20/0.54    inference(forward_demodulation,[],[f1048,f495])).
% 0.20/0.54  fof(f495,plain,(
% 0.20/0.54    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X0)) ) | ~spl7_24),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f213,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.54  fof(f213,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl7_24),
% 0.20/0.54    inference(avatar_component_clause,[],[f211])).
% 0.20/0.54  fof(f1048,plain,(
% 0.20/0.54    k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | (~spl7_24 | ~spl7_68 | ~spl7_70)),
% 0.20/0.54    inference(forward_demodulation,[],[f1009,f539])).
% 0.20/0.54  fof(f539,plain,(
% 0.20/0.54    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl7_68),
% 0.20/0.54    inference(avatar_component_clause,[],[f537])).
% 0.20/0.54  fof(f1009,plain,(
% 0.20/0.54    k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | (~spl7_24 | ~spl7_70)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f213,f552,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 0.20/0.54  fof(f552,plain,(
% 0.20/0.54    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl7_70),
% 0.20/0.54    inference(avatar_component_clause,[],[f550])).
% 0.20/0.54  fof(f571,plain,(
% 0.20/0.54    ~spl7_9 | ~spl7_73 | spl7_26),
% 0.20/0.54    inference(avatar_split_clause,[],[f565,f227,f567,f106])).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    spl7_9 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.54  fof(f227,plain,(
% 0.20/0.54    spl7_26 <=> sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.20/0.54  fof(f565,plain,(
% 0.20/0.54    sK1 != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl7_26),
% 0.20/0.54    inference(superposition,[],[f228,f47])).
% 0.20/0.54  fof(f228,plain,(
% 0.20/0.54    sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | spl7_26),
% 0.20/0.54    inference(avatar_component_clause,[],[f227])).
% 0.20/0.54  fof(f553,plain,(
% 0.20/0.54    spl7_70 | ~spl7_63 | ~spl7_64),
% 0.20/0.54    inference(avatar_split_clause,[],[f548,f515,f509,f550])).
% 0.20/0.54  fof(f509,plain,(
% 0.20/0.54    spl7_63 <=> m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 0.20/0.54  fof(f515,plain,(
% 0.20/0.54    spl7_64 <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 0.20/0.54  fof(f548,plain,(
% 0.20/0.54    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | (~spl7_63 | ~spl7_64)),
% 0.20/0.54    inference(forward_demodulation,[],[f511,f517])).
% 0.20/0.54  fof(f517,plain,(
% 0.20/0.54    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl7_64),
% 0.20/0.54    inference(avatar_component_clause,[],[f515])).
% 0.20/0.54  fof(f511,plain,(
% 0.20/0.54    m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl7_63),
% 0.20/0.54    inference(avatar_component_clause,[],[f509])).
% 0.20/0.54  fof(f547,plain,(
% 0.20/0.54    spl7_68 | ~spl7_64 | ~spl7_65),
% 0.20/0.54    inference(avatar_split_clause,[],[f546,f520,f515,f537])).
% 0.20/0.54  fof(f520,plain,(
% 0.20/0.54    spl7_65 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).
% 0.20/0.54  fof(f546,plain,(
% 0.20/0.54    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl7_64 | ~spl7_65)),
% 0.20/0.54    inference(backward_demodulation,[],[f522,f517])).
% 0.20/0.54  fof(f522,plain,(
% 0.20/0.54    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) | ~spl7_65),
% 0.20/0.54    inference(avatar_component_clause,[],[f520])).
% 0.20/0.54  fof(f531,plain,(
% 0.20/0.54    spl7_64 | ~spl7_21 | ~spl7_24),
% 0.20/0.54    inference(avatar_split_clause,[],[f530,f211,f190,f515])).
% 0.20/0.54  fof(f190,plain,(
% 0.20/0.54    spl7_21 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.20/0.54  fof(f530,plain,(
% 0.20/0.54    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | (~spl7_21 | ~spl7_24)),
% 0.20/0.54    inference(forward_demodulation,[],[f502,f191])).
% 0.20/0.54  fof(f191,plain,(
% 0.20/0.54    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl7_21),
% 0.20/0.54    inference(avatar_component_clause,[],[f190])).
% 0.20/0.54  fof(f502,plain,(
% 0.20/0.54    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl7_24),
% 0.20/0.54    inference(resolution,[],[f213,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.54  fof(f523,plain,(
% 0.20/0.54    spl7_65 | ~spl7_24),
% 0.20/0.54    inference(avatar_split_clause,[],[f498,f211,f520])).
% 0.20/0.54  fof(f498,plain,(
% 0.20/0.54    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) | ~spl7_24),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f213,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.54  fof(f512,plain,(
% 0.20/0.54    spl7_63 | ~spl7_24),
% 0.20/0.54    inference(avatar_split_clause,[],[f500,f211,f509])).
% 0.20/0.54  fof(f500,plain,(
% 0.20/0.54    m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl7_24),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f213,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.54  fof(f507,plain,(
% 0.20/0.54    spl7_62 | ~spl7_24),
% 0.20/0.54    inference(avatar_split_clause,[],[f501,f211,f504])).
% 0.20/0.54  fof(f501,plain,(
% 0.20/0.54    sP2(k2_pre_topc(sK0,sK1)) | ~spl7_24),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f213,f61])).
% 0.20/0.54  fof(f267,plain,(
% 0.20/0.54    spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_25),
% 0.20/0.54    inference(avatar_split_clause,[],[f266,f218,f111,f106,f100])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    spl7_8 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.54  fof(f111,plain,(
% 0.20/0.54    spl7_10 <=> l1_pre_topc(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.54  fof(f218,plain,(
% 0.20/0.54    spl7_25 <=> sK1 = k1_tops_1(sK0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.20/0.54  fof(f266,plain,(
% 0.20/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | (~spl7_9 | ~spl7_10 | ~spl7_25)),
% 0.20/0.54    inference(forward_demodulation,[],[f264,f220])).
% 0.20/0.54  fof(f220,plain,(
% 0.20/0.54    sK1 = k1_tops_1(sK0,sK1) | ~spl7_25),
% 0.20/0.54    inference(avatar_component_clause,[],[f218])).
% 0.20/0.54  fof(f264,plain,(
% 0.20/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl7_9 | ~spl7_10)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f113,f108,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f106])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    l1_pre_topc(sK0) | ~spl7_10),
% 0.20/0.54    inference(avatar_component_clause,[],[f111])).
% 0.20/0.54  fof(f245,plain,(
% 0.20/0.54    spl7_7 | ~spl7_23 | ~spl7_25),
% 0.20/0.54    inference(avatar_split_clause,[],[f244,f218,f205,f96])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    spl7_7 <=> v3_pre_topc(sK1,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.54  fof(f205,plain,(
% 0.20/0.54    spl7_23 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.54  fof(f244,plain,(
% 0.20/0.54    v3_pre_topc(sK1,sK0) | (~spl7_23 | ~spl7_25)),
% 0.20/0.54    inference(backward_demodulation,[],[f207,f220])).
% 0.20/0.54  fof(f207,plain,(
% 0.20/0.54    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl7_23),
% 0.20/0.54    inference(avatar_component_clause,[],[f205])).
% 0.20/0.54  fof(f242,plain,(
% 0.20/0.54    spl7_25 | ~spl7_26 | ~spl7_27),
% 0.20/0.54    inference(avatar_split_clause,[],[f241,f232,f227,f218])).
% 0.20/0.54  fof(f232,plain,(
% 0.20/0.54    spl7_27 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.20/0.54  fof(f241,plain,(
% 0.20/0.54    sK1 = k1_tops_1(sK0,sK1) | (~spl7_26 | ~spl7_27)),
% 0.20/0.54    inference(backward_demodulation,[],[f234,f229])).
% 0.20/0.54  fof(f229,plain,(
% 0.20/0.54    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl7_26),
% 0.20/0.54    inference(avatar_component_clause,[],[f227])).
% 0.20/0.54  fof(f234,plain,(
% 0.20/0.54    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl7_27),
% 0.20/0.54    inference(avatar_component_clause,[],[f232])).
% 0.20/0.54  fof(f240,plain,(
% 0.20/0.54    ~spl7_20 | spl7_21 | ~spl7_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f238,f100,f190,f186])).
% 0.20/0.54  fof(f186,plain,(
% 0.20/0.54    spl7_20 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.54  fof(f238,plain,(
% 0.20/0.54    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_8),
% 0.20/0.54    inference(superposition,[],[f47,f101])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl7_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f100])).
% 0.20/0.54  fof(f235,plain,(
% 0.20/0.54    spl7_27 | ~spl7_9 | ~spl7_10),
% 0.20/0.54    inference(avatar_split_clause,[],[f223,f111,f106,f232])).
% 0.20/0.54  fof(f223,plain,(
% 0.20/0.54    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl7_9 | ~spl7_10)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f113,f108,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 0.20/0.54  fof(f221,plain,(
% 0.20/0.54    spl7_25 | ~spl7_2 | ~spl7_7 | ~spl7_9 | ~spl7_10),
% 0.20/0.54    inference(avatar_split_clause,[],[f215,f111,f106,f96,f76,f218])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    spl7_2 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.54  fof(f215,plain,(
% 0.20/0.54    sK1 = k1_tops_1(sK0,sK1) | (~spl7_2 | ~spl7_7 | ~spl7_9 | ~spl7_10)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f113,f97,f108,f77])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X3,X1] : (~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1)) ) | ~spl7_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f76])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    v3_pre_topc(sK1,sK0) | ~spl7_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f96])).
% 0.20/0.54  fof(f214,plain,(
% 0.20/0.54    spl7_24 | ~spl7_22),
% 0.20/0.54    inference(avatar_split_clause,[],[f209,f196,f211])).
% 0.20/0.54  fof(f196,plain,(
% 0.20/0.54    spl7_22 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.20/0.54  fof(f209,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl7_22),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f198,f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.54    inference(unused_predicate_definition_removal,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f198,plain,(
% 0.20/0.54    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl7_22),
% 0.20/0.54    inference(avatar_component_clause,[],[f196])).
% 0.20/0.54  fof(f208,plain,(
% 0.20/0.54    spl7_23 | ~spl7_9 | ~spl7_10 | ~spl7_11),
% 0.20/0.54    inference(avatar_split_clause,[],[f203,f116,f111,f106,f205])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    spl7_11 <=> v2_pre_topc(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.54  fof(f203,plain,(
% 0.20/0.54    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl7_9 | ~spl7_10 | ~spl7_11)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f118,f113,f108,f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    v2_pre_topc(sK0) | ~spl7_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f116])).
% 0.20/0.54  fof(f202,plain,(
% 0.20/0.54    spl7_20 | ~spl7_9 | ~spl7_10),
% 0.20/0.54    inference(avatar_split_clause,[],[f200,f111,f106,f186])).
% 0.20/0.54  fof(f200,plain,(
% 0.20/0.54    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_9 | ~spl7_10)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f113,f108,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.54  fof(f199,plain,(
% 0.20/0.54    spl7_22 | ~spl7_9 | ~spl7_10),
% 0.20/0.54    inference(avatar_split_clause,[],[f194,f111,f106,f196])).
% 0.20/0.54  fof(f194,plain,(
% 0.20/0.54    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl7_9 | ~spl7_10)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f113,f108,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.20/0.54  fof(f134,plain,(
% 0.20/0.54    spl7_13 | ~spl7_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f132,f106,f128])).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    spl7_13 <=> sP5(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.54  fof(f132,plain,(
% 0.20/0.54    sP5(sK0) | ~spl7_9),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f108,f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X2,X0] : (sP5(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f67_D])).
% 0.20/0.54  fof(f67_D,plain,(
% 0.20/0.54    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) <=> ~sP5(X0)) )),
% 0.20/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.54  fof(f131,plain,(
% 0.20/0.54    ~spl7_13 | ~spl7_3 | ~spl7_10 | ~spl7_11),
% 0.20/0.54    inference(avatar_split_clause,[],[f126,f116,f111,f80,f128])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    spl7_3 <=> ! [X0] : (~l1_pre_topc(X0) | ~sP5(X0) | ~v2_pre_topc(X0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    ~sP5(sK0) | (~spl7_3 | ~spl7_10 | ~spl7_11)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f118,f113,f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X0] : (~sP5(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl7_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f80])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    spl7_11),
% 0.20/0.54    inference(avatar_split_clause,[],[f42,f116])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    v2_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,negated_conjecture,(
% 0.20/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.20/0.54    inference(negated_conjecture,[],[f16])).
% 0.20/0.54  fof(f16,conjecture,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    spl7_10),
% 0.20/0.54    inference(avatar_split_clause,[],[f43,f111])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    l1_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    spl7_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f44,f106])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    spl7_7 | spl7_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f45,f100,f96])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    ~spl7_7 | ~spl7_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f46,f100,f96])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    spl7_1 | spl7_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f69,f80,f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    spl7_1 <=> sP6),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP5(X0) | sP6) )),
% 0.20/0.54    inference(cnf_transformation,[],[f69_D])).
% 0.20/0.54  fof(f69_D,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP5(X0)) ) <=> ~sP6),
% 0.20/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ~spl7_1 | spl7_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f70,f76,f72])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~sP6) )),
% 0.20/0.54    inference(general_splitting,[],[f68,f69_D])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP5(X0)) )),
% 0.20/0.54    inference(general_splitting,[],[f52,f67_D])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (31781)------------------------------
% 0.20/0.54  % (31781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31781)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (31781)Memory used [KB]: 11513
% 0.20/0.54  % (31781)Time elapsed: 0.098 s
% 0.20/0.54  % (31781)------------------------------
% 0.20/0.54  % (31781)------------------------------
% 0.20/0.55  % (31798)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.55  % (31798)Refutation not found, incomplete strategy% (31798)------------------------------
% 0.20/0.55  % (31798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31798)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31798)Memory used [KB]: 10618
% 0.20/0.55  % (31798)Time elapsed: 0.144 s
% 0.20/0.55  % (31798)------------------------------
% 0.20/0.55  % (31798)------------------------------
% 0.20/0.56  % (31774)Success in time 0.205 s
%------------------------------------------------------------------------------
