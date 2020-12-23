%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t96_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:34 EDT 2019

% Result     : Theorem 30.17s
% Output     : Refutation 30.17s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 177 expanded)
%              Number of leaves         :   30 (  81 expanded)
%              Depth                    :    7
%              Number of atoms          :  272 ( 541 expanded)
%              Number of equality atoms :   32 (  46 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4856,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f114,f121,f128,f135,f162,f175,f241,f301,f318,f340,f485,f3146,f4854,f4855])).

fof(f4855,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | v3_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(theory_axiom,[])).

fof(f4854,plain,
    ( ~ spl6_25
    | spl6_562
    | ~ spl6_76
    | ~ spl6_362 ),
    inference(avatar_split_clause,[],[f4853,f3142,f483,f4846,f236])).

fof(f236,plain,
    ( spl6_25
  <=> ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f4846,plain,
    ( spl6_562
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_562])])).

fof(f483,plain,
    ( spl6_76
  <=> k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f3142,plain,
    ( spl6_362
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_362])])).

fof(f4853,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_76
    | ~ spl6_362 ),
    inference(forward_demodulation,[],[f4839,f3143])).

fof(f3143,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl6_362 ),
    inference(avatar_component_clause,[],[f3142])).

fof(f4839,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_76 ),
    inference(superposition,[],[f86,f484])).

fof(f484,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f483])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t96_tops_1.p',redefinition_k9_subset_1)).

fof(f3146,plain,
    ( spl6_362
    | ~ spl6_24
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f3129,f316,f239,f3142])).

fof(f239,plain,
    ( spl6_24
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f316,plain,
    ( spl6_42
  <=> k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f3129,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl6_24
    | ~ spl6_42 ),
    inference(superposition,[],[f317,f423])).

fof(f423,plain,
    ( ! [X0] : k3_xboole_0(X0,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f401,f402])).

fof(f402,plain,
    ( ! [X0] : k3_xboole_0(X0,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f240,f86])).

fof(f240,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f239])).

fof(f401,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f240,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t96_tops_1.p',commutativity_k9_subset_1)).

fof(f317,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f316])).

fof(f485,plain,
    ( spl6_76
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f478,f173,f160,f126,f483])).

fof(f126,plain,
    ( spl6_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f160,plain,
    ( spl6_14
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f173,plain,
    ( spl6_16
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f478,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f442,f174])).

fof(f174,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f173])).

fof(f442,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f127,f161,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t96_tops_1.p',d2_tops_1)).

fof(f161,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f340,plain,
    ( ~ spl6_9
    | ~ spl6_7
    | spl6_48
    | ~ spl6_15
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f333,f299,f157,f338,f123,f130])).

fof(f130,plain,
    ( spl6_9
  <=> ~ v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f123,plain,
    ( spl6_7
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f338,plain,
    ( spl6_48
  <=> v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f157,plain,
    ( spl6_15
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f299,plain,
    ( spl6_38
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f333,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_38 ),
    inference(resolution,[],[f300,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_tops_1(k2_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t96_tops_1.p',fc16_tops_1)).

fof(f300,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f299])).

fof(f318,plain,
    ( spl6_42
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f308,f126,f119,f316])).

fof(f119,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f308,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f127,f120,f81])).

fof(f120,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f301,plain,
    ( spl6_38
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f293,f133,f126,f119,f112,f299])).

fof(f112,plain,
    ( spl6_2
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f133,plain,
    ( spl6_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f293,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f134,f127,f113,f120,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t96_tops_1.p',fc2_tops_1)).

fof(f113,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f134,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f241,plain,
    ( spl6_24
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f232,f126,f119,f239])).

fof(f232,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f127,f120,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t96_tops_1.p',dt_k2_pre_topc)).

fof(f175,plain,
    ( spl6_16
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f167,f119,f173])).

fof(f167,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f120,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t96_tops_1.p',involutiveness_k3_subset_1)).

fof(f162,plain,
    ( spl6_14
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f155,f119,f160])).

fof(f155,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f120,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t96_tops_1.p',dt_k3_subset_1)).

fof(f135,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f74,f133])).

fof(f74,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,
    ( ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f68,f67])).

fof(f67,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(sK0,X1),sK0)
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tops_1(k2_tops_1(X0,sK1),X0)
        & v4_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v4_pre_topc(X1,X0)
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
           => ( v4_pre_topc(X1,X0)
             => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t96_tops_1.p',t96_tops_1)).

fof(f128,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f75,f126])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f121,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f76,f119])).

fof(f76,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f69])).

fof(f114,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f77,f112])).

fof(f77,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f107,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f78,f105])).

fof(f105,plain,
    ( spl6_1
  <=> ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f78,plain,(
    ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f69])).
%------------------------------------------------------------------------------
