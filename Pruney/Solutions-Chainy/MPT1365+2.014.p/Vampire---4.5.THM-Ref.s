%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 325 expanded)
%              Number of leaves         :   36 ( 154 expanded)
%              Depth                    :    8
%              Number of atoms          :  458 (1280 expanded)
%              Number of equality atoms :   25 (  56 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f635,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f101,f166,f179,f198,f203,f212,f231,f274,f318,f323,f416,f535,f549,f630])).

fof(f630,plain,
    ( ~ spl3_57
    | ~ spl3_7
    | ~ spl3_16
    | ~ spl3_18
    | spl3_42 ),
    inference(avatar_split_clause,[],[f629,f383,f176,f163,f93,f546])).

fof(f546,plain,
    ( spl3_57
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f93,plain,
    ( spl3_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f163,plain,
    ( spl3_16
  <=> m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f176,plain,
    ( spl3_18
  <=> sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f383,plain,
    ( spl3_42
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f629,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2))
    | ~ spl3_7
    | ~ spl3_16
    | ~ spl3_18
    | spl3_42 ),
    inference(forward_demodulation,[],[f609,f178])).

fof(f178,plain,
    ( sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f609,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    | ~ spl3_7
    | ~ spl3_16
    | spl3_42 ),
    inference(unit_resulting_resolution,[],[f165,f385,f190])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_7 ),
    inference(resolution,[],[f44,f95])).

fof(f95,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f385,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_42 ),
    inference(avatar_component_clause,[],[f383])).

fof(f165,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f549,plain,
    ( spl3_57
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f541,f532,f546])).

fof(f532,plain,
    ( spl3_56
  <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f541,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2))
    | ~ spl3_56 ),
    inference(unit_resulting_resolution,[],[f534,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f534,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f532])).

fof(f535,plain,
    ( spl3_56
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f525,f306,f532])).

fof(f306,plain,
    ( spl3_38
  <=> k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f525,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | ~ spl3_38 ),
    inference(superposition,[],[f141,f308])).

fof(f308,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f306])).

fof(f141,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[],[f49,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f416,plain,
    ( ~ spl3_42
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_22
    | spl3_33
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f413,f315,f271,f210,f88,f73,f383])).

fof(f73,plain,
    ( spl3_3
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f88,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f210,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v2_compts_1(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_compts_1(X1,sK0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f271,plain,
    ( spl3_33
  <=> v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f315,plain,
    ( spl3_39
  <=> v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f413,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_22
    | spl3_33
    | ~ spl3_39 ),
    inference(unit_resulting_resolution,[],[f141,f317,f273,f75,f90,f211])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ v2_compts_1(X1,sK0)
        | v2_compts_1(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f90,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f75,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f273,plain,
    ( ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f271])).

fof(f317,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f315])).

fof(f323,plain,
    ( spl3_38
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f320,f88,f83,f306])).

fof(f83,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f320,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(superposition,[],[f185,f312])).

fof(f312,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(X0,sK1))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f181,f186])).

fof(f186,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f90,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f57,f50])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f181,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f90,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f185,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f85,f61])).

fof(f85,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f318,plain,
    ( spl3_39
    | ~ spl3_5
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f313,f228,f83,f315])).

fof(f228,plain,
    ( spl3_25
  <=> v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f313,plain,
    ( v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ spl3_5
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f230,f185])).

fof(f230,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f228])).

fof(f274,plain,
    ( ~ spl3_33
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f268,f83,f63,f271])).

fof(f63,plain,
    ( spl3_1
  <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f268,plain,
    ( ~ v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f65,f185])).

fof(f65,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f231,plain,
    ( spl3_25
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f214,f200,f195,f98,f93,f88,f83,f228])).

fof(f98,plain,
    ( spl3_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f195,plain,
    ( spl3_19
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f200,plain,
    ( spl3_20
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f214,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f100,f95,f197,f202,f90,f85,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

fof(f202,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f200])).

fof(f197,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f195])).

fof(f100,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f212,plain,
    ( ~ spl3_7
    | spl3_22
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f208,f98,f210,f93])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,X1)
        | ~ v2_compts_1(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_compts_1(X0,sK0) )
    | ~ spl3_8 ),
    inference(resolution,[],[f48,f100])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_compts_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

fof(f203,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f191,f98,f93,f83,f78,f68,f200])).

fof(f68,plain,
    ( spl3_2
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f78,plain,
    ( spl3_4
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f191,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f100,f95,f80,f70,f85,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

fof(f70,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f80,plain,
    ( v8_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f198,plain,
    ( spl3_19
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f192,f98,f93,f88,f78,f73,f195])).

fof(f192,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f100,f95,f80,f75,f90,f46])).

fof(f179,plain,
    ( spl3_18
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f167,f93,f83,f176])).

fof(f167,plain,
    ( sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f95,f85,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f166,plain,
    ( spl3_16
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f155,f93,f83,f163])).

fof(f155,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f95,f85,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f101,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f36,f98])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_compts_1(X2,X0)
                & v2_compts_1(X1,X0)
                & v8_pre_topc(X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_compts_1(X2,sK0)
              & v2_compts_1(X1,sK0)
              & v8_pre_topc(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v2_compts_1(X2,sK0)
            & v2_compts_1(X1,sK0)
            & v8_pre_topc(sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v2_compts_1(X2,sK0)
          & v2_compts_1(sK1,sK0)
          & v8_pre_topc(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v2_compts_1(X2,sK0)
        & v2_compts_1(sK1,sK0)
        & v8_pre_topc(sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v2_compts_1(sK2,sK0)
      & v2_compts_1(sK1,sK0)
      & v8_pre_topc(sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_compts_1(X2,X0)
                    & v2_compts_1(X1,X0)
                    & v8_pre_topc(X0) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_compts_1(X2,X0)
                  & v2_compts_1(X1,X0)
                  & v8_pre_topc(X0) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

fof(f96,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f37,f93])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f38,f88])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f39,f83])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f41,f73])).

fof(f41,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f42,f68])).

fof(f42,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f43,f63])).

fof(f43,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:44:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (29962)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.53  % (29957)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.53  % (29958)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (29960)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (29959)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.53  % (29961)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.53  % (29965)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.53  % (29970)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.54  % (29968)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.54  % (29966)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.54  % (29969)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.54  % (29967)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.55  % (29960)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f635,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f101,f166,f179,f198,f203,f212,f231,f274,f318,f323,f416,f535,f549,f630])).
% 0.21/0.55  fof(f630,plain,(
% 0.21/0.55    ~spl3_57 | ~spl3_7 | ~spl3_16 | ~spl3_18 | spl3_42),
% 0.21/0.55    inference(avatar_split_clause,[],[f629,f383,f176,f163,f93,f546])).
% 0.21/0.55  fof(f546,plain,(
% 0.21/0.55    spl3_57 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    spl3_7 <=> l1_pre_topc(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    spl3_16 <=> m1_pre_topc(k1_pre_topc(sK0,sK2),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    spl3_18 <=> sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.55  fof(f383,plain,(
% 0.21/0.55    spl3_42 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.55  fof(f629,plain,(
% 0.21/0.55    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2)) | (~spl3_7 | ~spl3_16 | ~spl3_18 | spl3_42)),
% 0.21/0.55    inference(forward_demodulation,[],[f609,f178])).
% 0.21/0.55  fof(f178,plain,(
% 0.21/0.55    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) | ~spl3_18),
% 0.21/0.55    inference(avatar_component_clause,[],[f176])).
% 0.21/0.55  fof(f609,plain,(
% 0.21/0.55    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) | (~spl3_7 | ~spl3_16 | spl3_42)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f165,f385,f190])).
% 0.21/0.55  fof(f190,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_7),
% 0.21/0.55    inference(resolution,[],[f44,f95])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    l1_pre_topc(sK0) | ~spl3_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f93])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.55  fof(f385,plain,(
% 0.21/0.55    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_42),
% 0.21/0.55    inference(avatar_component_clause,[],[f383])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) | ~spl3_16),
% 0.21/0.55    inference(avatar_component_clause,[],[f163])).
% 0.21/0.55  fof(f549,plain,(
% 0.21/0.55    spl3_57 | ~spl3_56),
% 0.21/0.55    inference(avatar_split_clause,[],[f541,f532,f546])).
% 0.21/0.55  fof(f532,plain,(
% 0.21/0.55    spl3_56 <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.21/0.55  fof(f541,plain,(
% 0.21/0.55    m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(sK2)) | ~spl3_56),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f534,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f534,plain,(
% 0.21/0.55    r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | ~spl3_56),
% 0.21/0.55    inference(avatar_component_clause,[],[f532])).
% 0.21/0.55  fof(f535,plain,(
% 0.21/0.55    spl3_56 | ~spl3_38),
% 0.21/0.55    inference(avatar_split_clause,[],[f525,f306,f532])).
% 0.21/0.55  fof(f306,plain,(
% 0.21/0.55    spl3_38 <=> k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.55  fof(f525,plain,(
% 0.21/0.55    r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | ~spl3_38),
% 0.21/0.55    inference(superposition,[],[f141,f308])).
% 0.21/0.55  fof(f308,plain,(
% 0.21/0.55    k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) | ~spl3_38),
% 0.21/0.55    inference(avatar_component_clause,[],[f306])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.21/0.55    inference(superposition,[],[f49,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f51,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.55  fof(f416,plain,(
% 0.21/0.55    ~spl3_42 | ~spl3_3 | ~spl3_6 | ~spl3_22 | spl3_33 | ~spl3_39),
% 0.21/0.55    inference(avatar_split_clause,[],[f413,f315,f271,f210,f88,f73,f383])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    spl3_3 <=> v2_compts_1(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.55  fof(f210,plain,(
% 0.21/0.55    spl3_22 <=> ! [X1,X0] : (~v4_pre_topc(X0,sK0) | v2_compts_1(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0) | ~r1_tarski(X0,X1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.55  fof(f271,plain,(
% 0.21/0.55    spl3_33 <=> v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.55  fof(f315,plain,(
% 0.21/0.55    spl3_39 <=> v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.55  fof(f413,plain,(
% 0.21/0.55    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | ~spl3_6 | ~spl3_22 | spl3_33 | ~spl3_39)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f141,f317,f273,f75,f90,f211])).
% 0.21/0.55  fof(f211,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v2_compts_1(X1,sK0) | v2_compts_1(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~r1_tarski(X0,X1)) ) | ~spl3_22),
% 0.21/0.55    inference(avatar_component_clause,[],[f210])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f88])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    v2_compts_1(sK1,sK0) | ~spl3_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f73])).
% 0.21/0.55  fof(f273,plain,(
% 0.21/0.55    ~v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | spl3_33),
% 0.21/0.55    inference(avatar_component_clause,[],[f271])).
% 0.21/0.55  fof(f317,plain,(
% 0.21/0.55    v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~spl3_39),
% 0.21/0.55    inference(avatar_component_clause,[],[f315])).
% 0.21/0.55  fof(f323,plain,(
% 0.21/0.55    spl3_38 | ~spl3_5 | ~spl3_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f320,f88,f83,f306])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.55  fof(f320,plain,(
% 0.21/0.55    k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) | (~spl3_5 | ~spl3_6)),
% 0.21/0.55    inference(superposition,[],[f185,f312])).
% 0.21/0.55  fof(f312,plain,(
% 0.21/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(X0,sK1))) ) | ~spl3_6),
% 0.21/0.55    inference(forward_demodulation,[],[f181,f186])).
% 0.21/0.55  fof(f186,plain,(
% 0.21/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))) ) | ~spl3_6),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f90,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f57,f50])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.55  fof(f181,plain,(
% 0.21/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl3_6),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f90,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.21/0.55  fof(f185,plain,(
% 0.21/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_5),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f85,f61])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f83])).
% 0.21/0.55  fof(f318,plain,(
% 0.21/0.55    spl3_39 | ~spl3_5 | ~spl3_25),
% 0.21/0.55    inference(avatar_split_clause,[],[f313,f228,f83,f315])).
% 0.21/0.55  fof(f228,plain,(
% 0.21/0.55    spl3_25 <=> v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.55  fof(f313,plain,(
% 0.21/0.55    v4_pre_topc(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (~spl3_5 | ~spl3_25)),
% 0.21/0.55    inference(forward_demodulation,[],[f230,f185])).
% 0.21/0.55  fof(f230,plain,(
% 0.21/0.55    v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | ~spl3_25),
% 0.21/0.55    inference(avatar_component_clause,[],[f228])).
% 0.21/0.55  fof(f274,plain,(
% 0.21/0.55    ~spl3_33 | spl3_1 | ~spl3_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f268,f83,f63,f271])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    spl3_1 <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.55  fof(f268,plain,(
% 0.21/0.55    ~v2_compts_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (spl3_1 | ~spl3_5)),
% 0.21/0.55    inference(backward_demodulation,[],[f65,f185])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f63])).
% 0.21/0.55  fof(f231,plain,(
% 0.21/0.55    spl3_25 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_19 | ~spl3_20),
% 0.21/0.55    inference(avatar_split_clause,[],[f214,f200,f195,f98,f93,f88,f83,f228])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    spl3_8 <=> v2_pre_topc(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.55  fof(f195,plain,(
% 0.21/0.55    spl3_19 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.55  fof(f200,plain,(
% 0.21/0.55    spl3_20 <=> v4_pre_topc(sK2,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.55  fof(f214,plain,(
% 0.21/0.55    v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | (~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_19 | ~spl3_20)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f100,f95,f197,f202,f90,f85,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).
% 0.21/0.55  fof(f202,plain,(
% 0.21/0.55    v4_pre_topc(sK2,sK0) | ~spl3_20),
% 0.21/0.55    inference(avatar_component_clause,[],[f200])).
% 0.21/0.55  fof(f197,plain,(
% 0.21/0.55    v4_pre_topc(sK1,sK0) | ~spl3_19),
% 0.21/0.55    inference(avatar_component_clause,[],[f195])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    v2_pre_topc(sK0) | ~spl3_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f98])).
% 0.21/0.55  fof(f212,plain,(
% 0.21/0.55    ~spl3_7 | spl3_22 | ~spl3_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f208,f98,f210,f93])).
% 0.21/0.55  fof(f208,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v4_pre_topc(X0,sK0) | ~r1_tarski(X0,X1) | ~v2_compts_1(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_compts_1(X0,sK0)) ) | ~spl3_8),
% 0.21/0.55    inference(resolution,[],[f48,f100])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_compts_1(X2,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).
% 0.21/0.55  fof(f203,plain,(
% 0.21/0.55    spl3_20 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f191,f98,f93,f83,f78,f68,f200])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    spl3_2 <=> v2_compts_1(sK2,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    spl3_4 <=> v8_pre_topc(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    v4_pre_topc(sK2,sK0) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_8)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f100,f95,f80,f70,f85,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v8_pre_topc(X0) | ~v2_compts_1(X1,X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    v2_compts_1(sK2,sK0) | ~spl3_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f68])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    v8_pre_topc(sK0) | ~spl3_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f78])).
% 0.21/0.55  fof(f198,plain,(
% 0.21/0.55    spl3_19 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f192,f98,f93,f88,f78,f73,f195])).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    v4_pre_topc(sK1,sK0) | (~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f100,f95,f80,f75,f90,f46])).
% 0.21/0.55  fof(f179,plain,(
% 0.21/0.55    spl3_18 | ~spl3_5 | ~spl3_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f167,f93,f83,f176])).
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) | (~spl3_5 | ~spl3_7)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f95,f85,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    spl3_16 | ~spl3_5 | ~spl3_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f155,f93,f83,f163])).
% 0.21/0.55  fof(f155,plain,(
% 0.21/0.55    m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) | (~spl3_5 | ~spl3_7)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f95,f85,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    spl3_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f36,f98])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    v2_pre_topc(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33,f32,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.55    inference(negated_conjecture,[],[f14])).
% 0.21/0.55  fof(f14,conjecture,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    spl3_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f37,f93])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    l1_pre_topc(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    spl3_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f38,f88])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    spl3_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f39,f83])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    spl3_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f40,f78])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    v8_pre_topc(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    spl3_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f41,f73])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    v2_compts_1(sK1,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f42,f68])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    v2_compts_1(sK2,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ~spl3_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f43,f63])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (29960)------------------------------
% 0.21/0.55  % (29960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29960)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.56  % (29960)Memory used [KB]: 6652
% 0.21/0.56  % (29960)Time elapsed: 0.096 s
% 0.21/0.56  % (29960)------------------------------
% 0.21/0.56  % (29960)------------------------------
% 0.21/0.56  % (29953)Success in time 0.189 s
%------------------------------------------------------------------------------
