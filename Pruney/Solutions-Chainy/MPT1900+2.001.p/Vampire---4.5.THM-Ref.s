%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:24 EST 2020

% Result     : Theorem 2.80s
% Output     : Refutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  345 ( 669 expanded)
%              Number of leaves         :   78 ( 285 expanded)
%              Depth                    :   12
%              Number of atoms          : 1373 (2715 expanded)
%              Number of equality atoms :  125 ( 267 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6316,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f166,f171,f176,f181,f186,f191,f201,f208,f214,f219,f230,f240,f252,f258,f263,f268,f275,f283,f325,f382,f397,f410,f475,f511,f559,f564,f602,f647,f657,f1155,f1830,f2015,f4075,f4151,f4160,f4256,f4258,f4400,f4500,f5050,f5051,f5345,f5381,f5403,f5645,f5757,f5842,f5897,f6178,f6269])).

fof(f6269,plain,
    ( ~ spl8_4
    | ~ spl8_5
    | ~ spl8_46
    | ~ spl8_47
    | spl8_158
    | ~ spl8_161
    | ~ spl8_187
    | ~ spl8_206
    | ~ spl8_212 ),
    inference(avatar_contradiction_clause,[],[f6268])).

fof(f6268,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_46
    | ~ spl8_47
    | spl8_158
    | ~ spl8_161
    | ~ spl8_187
    | ~ spl8_206
    | ~ spl8_212 ),
    inference(subsumption_resolution,[],[f6267,f102])).

fof(f102,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f6267,plain,
    ( ~ r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_46
    | ~ spl8_47
    | spl8_158
    | ~ spl8_161
    | ~ spl8_187
    | ~ spl8_206
    | ~ spl8_212 ),
    inference(forward_demodulation,[],[f6266,f646])).

fof(f646,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f644])).

fof(f644,plain,
    ( spl8_46
  <=> k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f6266,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_xboole_0),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_47
    | spl8_158
    | ~ spl8_161
    | ~ spl8_187
    | ~ spl8_206
    | ~ spl8_212 ),
    inference(forward_demodulation,[],[f6218,f656])).

fof(f656,plain,
    ( ! [X2,X1] : k1_xboole_0 = k8_relset_1(X1,X2,k1_xboole_0,X2)
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f655])).

fof(f655,plain,
    ( spl8_47
  <=> ! [X1,X2] : k1_xboole_0 = k8_relset_1(X1,X2,k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f6218,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ spl8_4
    | ~ spl8_5
    | spl8_158
    | ~ spl8_161
    | ~ spl8_187
    | ~ spl8_206
    | ~ spl8_212 ),
    inference(forward_demodulation,[],[f6217,f5883])).

fof(f5883,plain,
    ( k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0)
    | ~ spl8_206 ),
    inference(avatar_component_clause,[],[f5881])).

fof(f5881,plain,
    ( spl8_206
  <=> k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_206])])).

fof(f6217,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | ~ spl8_4
    | ~ spl8_5
    | spl8_158
    | ~ spl8_161
    | ~ spl8_187
    | ~ spl8_212 ),
    inference(subsumption_resolution,[],[f6216,f180])).

fof(f180,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl8_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f6216,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | ~ v2_pre_topc(sK1)
    | ~ spl8_5
    | spl8_158
    | ~ spl8_161
    | ~ spl8_187
    | ~ spl8_212 ),
    inference(subsumption_resolution,[],[f6215,f185])).

fof(f185,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl8_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f6215,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl8_158
    | ~ spl8_161
    | ~ spl8_187
    | ~ spl8_212 ),
    inference(subsumption_resolution,[],[f6214,f4242])).

fof(f4242,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl8_158 ),
    inference(avatar_component_clause,[],[f4240])).

fof(f4240,plain,
    ( spl8_158
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_158])])).

fof(f6214,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_161
    | ~ spl8_187
    | ~ spl8_212 ),
    inference(subsumption_resolution,[],[f6211,f4255])).

fof(f4255,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl8_161 ),
    inference(avatar_component_clause,[],[f4253])).

fof(f4253,plain,
    ( spl8_161
  <=> v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_161])])).

fof(f6211,plain,
    ( ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_187
    | ~ spl8_212 ),
    inference(superposition,[],[f6177,f5644])).

fof(f5644,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl8_187 ),
    inference(avatar_component_clause,[],[f5642])).

fof(f5642,plain,
    ( spl8_187
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_187])])).

fof(f6177,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,sK6(sK0,X0,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,k2_pre_topc(X0,sK6(sK0,X0,k1_xboole_0))))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_212 ),
    inference(avatar_component_clause,[],[f6176])).

fof(f6176,plain,
    ( spl8_212
  <=> ! [X0] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,sK6(sK0,X0,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,k2_pre_topc(X0,sK6(sK0,X0,k1_xboole_0))))
        | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_212])])).

fof(f6178,plain,
    ( spl8_212
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_16
    | ~ spl8_170 ),
    inference(avatar_split_clause,[],[f4512,f4498,f255,f173,f163,f6176])).

fof(f163,plain,
    ( spl8_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f173,plain,
    ( spl8_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f255,plain,
    ( spl8_16
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f4498,plain,
    ( spl8_170
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,sK6(X0,X1,k1_xboole_0))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,k2_pre_topc(X1,sK6(X0,X1,k1_xboole_0))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_170])])).

fof(f4512,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,sK6(sK0,X0,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,k2_pre_topc(X0,sK6(sK0,X0,k1_xboole_0))))
        | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_16
    | ~ spl8_170 ),
    inference(forward_demodulation,[],[f4511,f257])).

fof(f257,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f255])).

fof(f4511,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,sK6(sK0,X0,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,k2_pre_topc(X0,sK6(sK0,X0,k1_xboole_0)))) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_16
    | ~ spl8_170 ),
    inference(forward_demodulation,[],[f4510,f257])).

fof(f4510,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,sK6(sK0,X0,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,k2_pre_topc(X0,sK6(sK0,X0,k1_xboole_0)))) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_170 ),
    inference(subsumption_resolution,[],[f4508,f175])).

fof(f175,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f173])).

fof(f4508,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,sK6(sK0,X0,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,k2_pre_topc(X0,sK6(sK0,X0,k1_xboole_0)))) )
    | ~ spl8_1
    | ~ spl8_170 ),
    inference(resolution,[],[f4499,f165])).

fof(f165,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f163])).

fof(f4499,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,sK6(X0,X1,k1_xboole_0))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,k2_pre_topc(X1,sK6(X0,X1,k1_xboole_0)))) )
    | ~ spl8_170 ),
    inference(avatar_component_clause,[],[f4498])).

fof(f5897,plain,
    ( spl8_206
    | ~ spl8_204 ),
    inference(avatar_split_clause,[],[f5868,f5839,f5881])).

fof(f5839,plain,
    ( spl8_204
  <=> r1_tarski(sK6(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_204])])).

fof(f5868,plain,
    ( k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0)
    | ~ spl8_204 ),
    inference(subsumption_resolution,[],[f5867,f102])).

fof(f5867,plain,
    ( ~ r1_tarski(k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))
    | k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0)
    | ~ spl8_204 ),
    inference(resolution,[],[f5841,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5841,plain,
    ( r1_tarski(sK6(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl8_204 ),
    inference(avatar_component_clause,[],[f5839])).

fof(f5842,plain,
    ( spl8_204
    | ~ spl8_196 ),
    inference(avatar_split_clause,[],[f5785,f5754,f5839])).

fof(f5754,plain,
    ( spl8_196
  <=> m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_196])])).

fof(f5785,plain,
    ( r1_tarski(sK6(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl8_196 ),
    inference(resolution,[],[f5756,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f5756,plain,
    ( m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_196 ),
    inference(avatar_component_clause,[],[f5754])).

fof(f5757,plain,
    ( spl8_196
    | ~ spl8_4
    | ~ spl8_5
    | spl8_158
    | ~ spl8_161
    | ~ spl8_182
    | ~ spl8_187 ),
    inference(avatar_split_clause,[],[f5661,f5642,f5343,f4253,f4240,f183,f178,f5754])).

fof(f5343,plain,
    ( spl8_182
  <=> ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | m1_subset_1(sK6(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_182])])).

fof(f5661,plain,
    ( m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_4
    | ~ spl8_5
    | spl8_158
    | ~ spl8_161
    | ~ spl8_182
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f5660,f180])).

fof(f5660,plain,
    ( ~ v2_pre_topc(sK1)
    | m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_5
    | spl8_158
    | ~ spl8_161
    | ~ spl8_182
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f5659,f185])).

fof(f5659,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl8_158
    | ~ spl8_161
    | ~ spl8_182
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f5658,f4242])).

fof(f5658,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_161
    | ~ spl8_182
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f5656,f4255])).

fof(f5656,plain,
    ( ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_182
    | ~ spl8_187 ),
    inference(superposition,[],[f5344,f5644])).

fof(f5344,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | m1_subset_1(sK6(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl8_182 ),
    inference(avatar_component_clause,[],[f5343])).

fof(f5645,plain,
    ( spl8_187
    | ~ spl8_18
    | ~ spl8_140 ),
    inference(avatar_split_clause,[],[f5585,f3680,f265,f5642])).

fof(f265,plain,
    ( spl8_18
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f3680,plain,
    ( spl8_140
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_140])])).

fof(f5585,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl8_18
    | ~ spl8_140 ),
    inference(backward_demodulation,[],[f267,f3682])).

fof(f3682,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl8_140 ),
    inference(avatar_component_clause,[],[f3680])).

fof(f267,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f265])).

fof(f5403,plain,
    ( ~ spl8_5
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | spl8_140
    | ~ spl8_185 ),
    inference(avatar_contradiction_clause,[],[f5402])).

fof(f5402,plain,
    ( $false
    | ~ spl8_5
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | spl8_140
    | ~ spl8_185 ),
    inference(subsumption_resolution,[],[f5401,f185])).

fof(f5401,plain,
    ( ~ l1_pre_topc(sK1)
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | spl8_140
    | ~ spl8_185 ),
    inference(subsumption_resolution,[],[f5400,f200])).

fof(f200,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl8_8
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f5400,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | spl8_140
    | ~ spl8_185 ),
    inference(subsumption_resolution,[],[f5399,f3681])).

fof(f3681,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | spl8_140 ),
    inference(avatar_component_clause,[],[f3680])).

fof(f5399,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_185 ),
    inference(subsumption_resolution,[],[f5398,f282])).

fof(f282,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl8_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f5398,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_185 ),
    inference(subsumption_resolution,[],[f5396,f274])).

fof(f274,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl8_19
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f5396,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl8_18
    | ~ spl8_185 ),
    inference(superposition,[],[f5380,f267])).

fof(f5380,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | k1_xboole_0 = k2_struct_0(X0)
        | v5_pre_topc(sK2,sK0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_185 ),
    inference(avatar_component_clause,[],[f5379])).

fof(f5379,plain,
    ( spl8_185
  <=> ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | k1_xboole_0 = k2_struct_0(X0)
        | v5_pre_topc(sK2,sK0,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_185])])).

fof(f5381,plain,
    ( spl8_185
    | ~ spl8_3
    | ~ spl8_16
    | ~ spl8_68
    | ~ spl8_105 ),
    inference(avatar_split_clause,[],[f5231,f2013,f1153,f255,f173,f5379])).

fof(f1153,plain,
    ( spl8_68
  <=> ! [X1,X0] :
        ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK3(X0,X1,sK2)),X0)
        | k1_xboole_0 = k2_struct_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(sK2,X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f2013,plain,
    ( spl8_105
  <=> ! [X1,X0,X2] :
        ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),X0,X1,X2),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f5231,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | k1_xboole_0 = k2_struct_0(X0)
        | v5_pre_topc(sK2,sK0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_3
    | ~ spl8_16
    | ~ spl8_68
    | ~ spl8_105 ),
    inference(subsumption_resolution,[],[f5230,f2014])).

fof(f2014,plain,
    ( ! [X2,X0,X1] :
        ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),X0,X1,X2),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) )
    | ~ spl8_105 ),
    inference(avatar_component_clause,[],[f2013])).

fof(f5230,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2,sK3(sK0,X0,sK2)),sK0)
        | ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | k1_xboole_0 = k2_struct_0(X0)
        | v5_pre_topc(sK2,sK0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_3
    | ~ spl8_16
    | ~ spl8_68 ),
    inference(forward_demodulation,[],[f5229,f257])).

fof(f5229,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | k1_xboole_0 = k2_struct_0(X0)
        | v5_pre_topc(sK2,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK3(sK0,X0,sK2)),sK0) )
    | ~ spl8_3
    | ~ spl8_16
    | ~ spl8_68 ),
    inference(forward_demodulation,[],[f5228,f257])).

fof(f5228,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | k1_xboole_0 = k2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | v5_pre_topc(sK2,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK3(sK0,X0,sK2)),sK0) )
    | ~ spl8_3
    | ~ spl8_16
    | ~ spl8_68 ),
    inference(forward_demodulation,[],[f5226,f257])).

fof(f5226,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | v5_pre_topc(sK2,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK3(sK0,X0,sK2)),sK0) )
    | ~ spl8_3
    | ~ spl8_68 ),
    inference(resolution,[],[f1154,f175])).

fof(f1154,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | k1_xboole_0 = k2_struct_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(sK2,X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK3(X0,X1,sK2)),X0) )
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f1153])).

fof(f5345,plain,
    ( spl8_182
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_16
    | ~ spl8_165 ),
    inference(avatar_split_clause,[],[f4415,f4398,f255,f173,f163,f5343])).

fof(f4398,plain,
    ( spl8_165
  <=> ! [X5,X4] :
        ( m1_subset_1(sK6(X4,X5,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X4),u1_struct_0(X5))
        | v5_pre_topc(k1_xboole_0,X4,X5)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_165])])).

fof(f4415,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | m1_subset_1(sK6(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_16
    | ~ spl8_165 ),
    inference(forward_demodulation,[],[f4414,f257])).

fof(f4414,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | m1_subset_1(sK6(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_165 ),
    inference(subsumption_resolution,[],[f4412,f175])).

fof(f4412,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(sK0)
        | m1_subset_1(sK6(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl8_1
    | ~ spl8_165 ),
    inference(resolution,[],[f4399,f165])).

fof(f4399,plain,
    ( ! [X4,X5] :
        ( ~ v2_pre_topc(X4)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X4),u1_struct_0(X5))
        | v5_pre_topc(k1_xboole_0,X4,X5)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X4)
        | m1_subset_1(sK6(X4,X5,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X5))) )
    | ~ spl8_165 ),
    inference(avatar_component_clause,[],[f4398])).

fof(f5051,plain,
    ( k1_xboole_0 != sK2
    | v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f5050,plain,
    ( ~ spl8_158
    | spl8_8
    | ~ spl8_156 ),
    inference(avatar_split_clause,[],[f4327,f4208,f198,f4240])).

fof(f4208,plain,
    ( spl8_156
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_156])])).

fof(f4327,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl8_8
    | ~ spl8_156 ),
    inference(backward_demodulation,[],[f200,f4210])).

fof(f4210,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_156 ),
    inference(avatar_component_clause,[],[f4208])).

fof(f4500,plain,
    ( spl8_170
    | ~ spl8_157 ),
    inference(avatar_split_clause,[],[f4234,f4225,f4498])).

fof(f4225,plain,
    ( spl8_157
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_157])])).

fof(f4234,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,sK6(X0,X1,k1_xboole_0))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,k2_pre_topc(X1,sK6(X0,X1,k1_xboole_0))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_157 ),
    inference(subsumption_resolution,[],[f4229,f104])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f4229,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,sK6(X0,X1,k1_xboole_0))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,k2_pre_topc(X1,sK6(X0,X1,k1_xboole_0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_157 ),
    inference(resolution,[],[f4227,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2))))
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f78,f79])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2))))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).

fof(f4227,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_157 ),
    inference(avatar_component_clause,[],[f4225])).

fof(f4400,plain,
    ( spl8_165
    | ~ spl8_157 ),
    inference(avatar_split_clause,[],[f4236,f4225,f4398])).

fof(f4236,plain,
    ( ! [X4,X5] :
        ( m1_subset_1(sK6(X4,X5,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X4),u1_struct_0(X5))
        | v5_pre_topc(k1_xboole_0,X4,X5)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4) )
    | ~ spl8_157 ),
    inference(subsumption_resolution,[],[f4231,f104])).

fof(f4231,plain,
    ( ! [X4,X5] :
        ( m1_subset_1(sK6(X4,X5,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X4),u1_struct_0(X5))
        | v5_pre_topc(k1_xboole_0,X4,X5)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4) )
    | ~ spl8_157 ),
    inference(resolution,[],[f4227,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f4258,plain,
    ( spl8_156
    | ~ spl8_155 ),
    inference(avatar_split_clause,[],[f4176,f4157,f4208])).

fof(f4157,plain,
    ( spl8_155
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_155])])).

fof(f4176,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_155 ),
    inference(subsumption_resolution,[],[f4175,f102])).

fof(f4175,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl8_155 ),
    inference(resolution,[],[f4159,f136])).

fof(f4159,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl8_155 ),
    inference(avatar_component_clause,[],[f4157])).

fof(f4256,plain,
    ( spl8_161
    | ~ spl8_101
    | ~ spl8_140
    | ~ spl8_154 ),
    inference(avatar_split_clause,[],[f4205,f4148,f3680,f1823,f4253])).

fof(f1823,plain,
    ( spl8_101
  <=> sK2 = k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f4148,plain,
    ( spl8_154
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_154])])).

fof(f4205,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl8_101
    | ~ spl8_140
    | ~ spl8_154 ),
    inference(backward_demodulation,[],[f4150,f4105])).

fof(f4105,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_101
    | ~ spl8_140 ),
    inference(forward_demodulation,[],[f4104,f160])).

fof(f160,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f4104,plain,
    ( sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl8_101
    | ~ spl8_140 ),
    inference(forward_demodulation,[],[f1825,f3682])).

fof(f1825,plain,
    ( sK2 = k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl8_101 ),
    inference(avatar_component_clause,[],[f1823])).

fof(f4150,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl8_154 ),
    inference(avatar_component_clause,[],[f4148])).

fof(f4160,plain,
    ( spl8_155
    | ~ spl8_30
    | ~ spl8_140 ),
    inference(avatar_split_clause,[],[f4062,f3680,f472,f4157])).

fof(f472,plain,
    ( spl8_30
  <=> r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f4062,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl8_30
    | ~ spl8_140 ),
    inference(forward_demodulation,[],[f4011,f160])).

fof(f4011,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))
    | ~ spl8_30
    | ~ spl8_140 ),
    inference(backward_demodulation,[],[f474,f3682])).

fof(f474,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f472])).

fof(f4151,plain,
    ( spl8_154
    | ~ spl8_19
    | ~ spl8_140 ),
    inference(avatar_split_clause,[],[f4008,f3680,f272,f4148])).

fof(f4008,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl8_19
    | ~ spl8_140 ),
    inference(backward_demodulation,[],[f274,f3682])).

fof(f4075,plain,
    ( spl8_102
    | ~ spl8_140 ),
    inference(avatar_contradiction_clause,[],[f4074])).

fof(f4074,plain,
    ( $false
    | spl8_102
    | ~ spl8_140 ),
    inference(subsumption_resolution,[],[f4073,f102])).

fof(f4073,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl8_102
    | ~ spl8_140 ),
    inference(forward_demodulation,[],[f4035,f160])).

fof(f4035,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0),sK2)
    | spl8_102
    | ~ spl8_140 ),
    inference(backward_demodulation,[],[f1829,f3682])).

fof(f1829,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2)
    | spl8_102 ),
    inference(avatar_component_clause,[],[f1827])).

fof(f1827,plain,
    ( spl8_102
  <=> r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f2015,plain,
    ( spl8_105
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f574,f557,f2013])).

fof(f557,plain,
    ( spl8_38
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f574,plain,
    ( ! [X2,X0,X1] :
        ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),X0,X1,X2),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) )
    | ~ spl8_38 ),
    inference(resolution,[],[f558,f154])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f558,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f557])).

fof(f1830,plain,
    ( spl8_101
    | ~ spl8_102
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f476,f472,f1827,f1823])).

fof(f476,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2)
    | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl8_30 ),
    inference(resolution,[],[f474,f136])).

fof(f1155,plain,
    ( spl8_68
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f463,f188,f1153])).

fof(f188,plain,
    ( spl8_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f463,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK3(X0,X1,sK2)),X0)
        | k1_xboole_0 = k2_struct_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | v5_pre_topc(sK2,X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f117,f190])).

fof(f190,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f188])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
                    & v3_pre_topc(sK3(X0,X1,X2),X1)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
        & v3_pre_topc(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v3_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(f657,plain,
    ( spl8_47
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f653,f509,f655])).

fof(f509,plain,
    ( spl8_31
  <=> ! [X1,X2] : k1_xboole_0 = k1_relset_1(X1,X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f653,plain,
    ( ! [X2,X1] : k1_xboole_0 = k8_relset_1(X1,X2,k1_xboole_0,X2)
    | ~ spl8_31 ),
    inference(forward_demodulation,[],[f433,f510])).

fof(f510,plain,
    ( ! [X2,X1] : k1_xboole_0 = k1_relset_1(X1,X2,k1_xboole_0)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f509])).

fof(f433,plain,(
    ! [X2,X1] : k1_relset_1(X1,X2,k1_xboole_0) = k8_relset_1(X1,X2,k1_xboole_0,X2) ),
    inference(resolution,[],[f152,f104])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f647,plain,
    ( spl8_46
    | ~ spl8_3
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f612,f599,f173,f644])).

fof(f599,plain,
    ( spl8_42
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f612,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f611,f175])).

fof(f611,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f610,f104])).

fof(f610,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_42 ),
    inference(resolution,[],[f601,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f601,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f599])).

fof(f602,plain,
    ( spl8_42
    | ~ spl8_39 ),
    inference(avatar_split_clause,[],[f581,f562,f599])).

fof(f562,plain,
    ( spl8_39
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f581,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_39 ),
    inference(resolution,[],[f563,f104])).

fof(f563,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f562])).

fof(f564,plain,
    ( spl8_39
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f392,f255,f173,f168,f562])).

fof(f168,plain,
    ( spl8_2
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f392,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f391,f257])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f390,f175])).

fof(f390,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f383,f170])).

fof(f170,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f168])).

fof(f383,plain,(
    ! [X2,X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f124,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f124,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK5(X0),X0)
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f74,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(f559,plain,
    ( spl8_38
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f375,f255,f173,f168,f557])).

fof(f375,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f374,f257])).

fof(f374,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f373,f175])).

fof(f373,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f372,f170])).

fof(f372,plain,(
    ! [X2,X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f121,f110])).

fof(f121,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK4(X0),X0)
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f70,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f511,plain,
    ( spl8_31
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f507,f407,f509])).

fof(f407,plain,
    ( spl8_27
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f507,plain,
    ( ! [X2,X1] : k1_xboole_0 = k1_relset_1(X1,X2,k1_xboole_0)
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f367,f409])).

fof(f409,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f407])).

fof(f367,plain,(
    ! [X2,X1] : k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f148,f104])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f475,plain,
    ( spl8_30
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f284,f280,f472])).

fof(f284,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl8_20 ),
    inference(resolution,[],[f282,f141])).

fof(f410,plain,
    ( spl8_27
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f403,f394,f322,f407])).

fof(f322,plain,
    ( spl8_22
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f394,plain,
    ( spl8_26
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f403,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f402,f324])).

fof(f324,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f322])).

fof(f402,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f401,f316])).

fof(f316,plain,(
    ! [X1] : v4_relat_1(k1_xboole_0,X1) ),
    inference(resolution,[],[f149,f104])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f401,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl8_26 ),
    inference(resolution,[],[f396,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f396,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f394])).

fof(f397,plain,
    ( spl8_26
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f389,f379,f394])).

fof(f379,plain,
    ( spl8_25
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f389,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_25 ),
    inference(superposition,[],[f106,f381])).

fof(f381,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f379])).

fof(f106,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f382,plain,
    ( spl8_25
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f313,f237,f379])).

fof(f237,plain,
    ( spl8_13
  <=> r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f313,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f311,f102])).

fof(f311,plain,
    ( ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0))
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl8_13 ),
    inference(resolution,[],[f136,f239])).

fof(f239,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f237])).

fof(f325,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f299,f322])).

fof(f299,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f147,f104])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f283,plain,
    ( spl8_20
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f276,f265,f255,f249,f280])).

fof(f249,plain,
    ( spl8_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f276,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f269,f267])).

fof(f269,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f251,f257])).

fof(f251,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f249])).

fof(f275,plain,
    ( spl8_19
    | ~ spl8_17
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f270,f265,f260,f272])).

fof(f260,plain,
    ( spl8_17
  <=> v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f270,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl8_17
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f262,f267])).

fof(f262,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f260])).

fof(f268,plain,
    ( spl8_18
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f229,f211,f265])).

fof(f211,plain,
    ( spl8_10
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f229,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl8_10 ),
    inference(resolution,[],[f108,f213])).

fof(f213,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f211])).

fof(f108,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f263,plain,
    ( spl8_17
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f253,f216,f205,f260])).

fof(f205,plain,
    ( spl8_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f216,plain,
    ( spl8_11
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f253,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f218,f228])).

fof(f228,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl8_9 ),
    inference(resolution,[],[f108,f207])).

fof(f207,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f205])).

fof(f218,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f216])).

fof(f258,plain,
    ( spl8_16
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f228,f205,f255])).

fof(f252,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f98,f249])).

fof(f98,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f63,f62,f61])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v5_pre_topc(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v5_pre_topc(X2,sK0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ~ v5_pre_topc(X2,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X2] :
        ( ~ v5_pre_topc(X2,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ v5_pre_topc(sK2,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).

fof(f240,plain,
    ( spl8_13
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f234,f224,f237])).

fof(f224,plain,
    ( spl8_12
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f234,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)
    | ~ spl8_12 ),
    inference(resolution,[],[f226,f141])).

fof(f226,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f224])).

fof(f230,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f222,f224])).

fof(f222,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f107,f161])).

fof(f161,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f90])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f219,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f97,f216])).

fof(f97,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

fof(f214,plain,
    ( spl8_10
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f203,f183,f211])).

fof(f203,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_5 ),
    inference(resolution,[],[f109,f185])).

fof(f109,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f208,plain,
    ( spl8_9
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f202,f173,f205])).

fof(f202,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_3 ),
    inference(resolution,[],[f109,f175])).

fof(f201,plain,(
    ~ spl8_8 ),
    inference(avatar_split_clause,[],[f99,f198])).

fof(f99,plain,(
    ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f191,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f96,f188])).

fof(f96,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

fof(f186,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f95,f183])).

fof(f95,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f181,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f94,f178])).

fof(f94,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f176,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f93,f173])).

fof(f93,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f171,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f92,f168])).

fof(f92,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f166,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f91,f163])).

fof(f91,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (27303)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.46  % (27298)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (27285)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  % (27298)Refutation not found, incomplete strategy% (27298)------------------------------
% 0.21/0.48  % (27298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27298)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (27298)Memory used [KB]: 6140
% 0.21/0.48  % (27298)Time elapsed: 0.084 s
% 0.21/0.48  % (27298)------------------------------
% 0.21/0.48  % (27298)------------------------------
% 0.21/0.48  % (27287)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.48  % (27285)Refutation not found, incomplete strategy% (27285)------------------------------
% 0.21/0.48  % (27285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27285)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (27285)Memory used [KB]: 10490
% 0.21/0.48  % (27285)Time elapsed: 0.002 s
% 0.21/0.48  % (27285)------------------------------
% 0.21/0.48  % (27285)------------------------------
% 0.21/0.49  % (27292)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  % (27304)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.49  % (27290)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (27294)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (27308)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (27302)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.50  % (27291)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (27306)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (27289)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (27299)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (27300)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (27305)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (27293)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (27307)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (27297)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (27286)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (27291)Refutation not found, incomplete strategy% (27291)------------------------------
% 0.21/0.52  % (27291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27291)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27291)Memory used [KB]: 10618
% 0.21/0.52  % (27291)Time elapsed: 0.097 s
% 0.21/0.52  % (27291)------------------------------
% 0.21/0.52  % (27291)------------------------------
% 0.21/0.52  % (27296)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (27296)Refutation not found, incomplete strategy% (27296)------------------------------
% 0.21/0.52  % (27296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27296)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27296)Memory used [KB]: 10490
% 0.21/0.52  % (27296)Time elapsed: 0.002 s
% 0.21/0.52  % (27296)------------------------------
% 0.21/0.52  % (27296)------------------------------
% 0.21/0.53  % (27310)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (27309)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (27288)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (27301)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (27290)Refutation not found, incomplete strategy% (27290)------------------------------
% 0.21/0.54  % (27290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27290)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27290)Memory used [KB]: 6652
% 0.21/0.54  % (27290)Time elapsed: 0.147 s
% 0.21/0.54  % (27290)------------------------------
% 0.21/0.54  % (27290)------------------------------
% 0.21/0.54  % (27295)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.94/0.60  % (27294)Refutation not found, incomplete strategy% (27294)------------------------------
% 1.94/0.60  % (27294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.60  % (27294)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.60  
% 1.94/0.60  % (27294)Memory used [KB]: 6140
% 1.94/0.60  % (27294)Time elapsed: 0.209 s
% 1.94/0.60  % (27294)------------------------------
% 1.94/0.60  % (27294)------------------------------
% 2.80/0.77  % (27287)Refutation found. Thanks to Tanya!
% 2.80/0.77  % SZS status Theorem for theBenchmark
% 2.80/0.77  % SZS output start Proof for theBenchmark
% 2.80/0.77  fof(f6316,plain,(
% 2.80/0.77    $false),
% 2.80/0.77    inference(avatar_sat_refutation,[],[f166,f171,f176,f181,f186,f191,f201,f208,f214,f219,f230,f240,f252,f258,f263,f268,f275,f283,f325,f382,f397,f410,f475,f511,f559,f564,f602,f647,f657,f1155,f1830,f2015,f4075,f4151,f4160,f4256,f4258,f4400,f4500,f5050,f5051,f5345,f5381,f5403,f5645,f5757,f5842,f5897,f6178,f6269])).
% 2.80/0.77  fof(f6269,plain,(
% 2.80/0.77    ~spl8_4 | ~spl8_5 | ~spl8_46 | ~spl8_47 | spl8_158 | ~spl8_161 | ~spl8_187 | ~spl8_206 | ~spl8_212),
% 2.80/0.77    inference(avatar_contradiction_clause,[],[f6268])).
% 2.80/0.77  fof(f6268,plain,(
% 2.80/0.77    $false | (~spl8_4 | ~spl8_5 | ~spl8_46 | ~spl8_47 | spl8_158 | ~spl8_161 | ~spl8_187 | ~spl8_206 | ~spl8_212)),
% 2.80/0.77    inference(subsumption_resolution,[],[f6267,f102])).
% 2.80/0.77  fof(f102,plain,(
% 2.80/0.77    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.80/0.77    inference(cnf_transformation,[],[f3])).
% 2.80/0.77  fof(f3,axiom,(
% 2.80/0.77    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.80/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.80/0.77  fof(f6267,plain,(
% 2.80/0.77    ~r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | (~spl8_4 | ~spl8_5 | ~spl8_46 | ~spl8_47 | spl8_158 | ~spl8_161 | ~spl8_187 | ~spl8_206 | ~spl8_212)),
% 2.80/0.77    inference(forward_demodulation,[],[f6266,f646])).
% 2.80/0.77  fof(f646,plain,(
% 2.80/0.77    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~spl8_46),
% 2.80/0.77    inference(avatar_component_clause,[],[f644])).
% 2.80/0.77  fof(f644,plain,(
% 2.80/0.77    spl8_46 <=> k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 2.80/0.77  fof(f6266,plain,(
% 2.80/0.77    ~r1_tarski(k2_pre_topc(sK0,k1_xboole_0),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | (~spl8_4 | ~spl8_5 | ~spl8_47 | spl8_158 | ~spl8_161 | ~spl8_187 | ~spl8_206 | ~spl8_212)),
% 2.80/0.77    inference(forward_demodulation,[],[f6218,f656])).
% 2.80/0.77  fof(f656,plain,(
% 2.80/0.77    ( ! [X2,X1] : (k1_xboole_0 = k8_relset_1(X1,X2,k1_xboole_0,X2)) ) | ~spl8_47),
% 2.80/0.77    inference(avatar_component_clause,[],[f655])).
% 2.80/0.77  fof(f655,plain,(
% 2.80/0.77    spl8_47 <=> ! [X1,X2] : k1_xboole_0 = k8_relset_1(X1,X2,k1_xboole_0,X2)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 2.80/0.77  fof(f6218,plain,(
% 2.80/0.77    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | (~spl8_4 | ~spl8_5 | spl8_158 | ~spl8_161 | ~spl8_187 | ~spl8_206 | ~spl8_212)),
% 2.80/0.77    inference(forward_demodulation,[],[f6217,f5883])).
% 2.80/0.77  fof(f5883,plain,(
% 2.80/0.77    k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0) | ~spl8_206),
% 2.80/0.77    inference(avatar_component_clause,[],[f5881])).
% 2.80/0.77  fof(f5881,plain,(
% 2.80/0.77    spl8_206 <=> k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_206])])).
% 2.80/0.77  fof(f6217,plain,(
% 2.80/0.77    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | (~spl8_4 | ~spl8_5 | spl8_158 | ~spl8_161 | ~spl8_187 | ~spl8_212)),
% 2.80/0.77    inference(subsumption_resolution,[],[f6216,f180])).
% 2.80/0.77  fof(f180,plain,(
% 2.80/0.77    v2_pre_topc(sK1) | ~spl8_4),
% 2.80/0.77    inference(avatar_component_clause,[],[f178])).
% 2.80/0.77  fof(f178,plain,(
% 2.80/0.77    spl8_4 <=> v2_pre_topc(sK1)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.80/0.77  fof(f6216,plain,(
% 2.80/0.77    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | ~v2_pre_topc(sK1) | (~spl8_5 | spl8_158 | ~spl8_161 | ~spl8_187 | ~spl8_212)),
% 2.80/0.77    inference(subsumption_resolution,[],[f6215,f185])).
% 2.80/0.77  fof(f185,plain,(
% 2.80/0.77    l1_pre_topc(sK1) | ~spl8_5),
% 2.80/0.77    inference(avatar_component_clause,[],[f183])).
% 2.80/0.77  fof(f183,plain,(
% 2.80/0.77    spl8_5 <=> l1_pre_topc(sK1)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.80/0.77  fof(f6215,plain,(
% 2.80/0.77    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl8_158 | ~spl8_161 | ~spl8_187 | ~spl8_212)),
% 2.80/0.77    inference(subsumption_resolution,[],[f6214,f4242])).
% 2.80/0.77  fof(f4242,plain,(
% 2.80/0.77    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl8_158),
% 2.80/0.77    inference(avatar_component_clause,[],[f4240])).
% 2.80/0.77  fof(f4240,plain,(
% 2.80/0.77    spl8_158 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_158])])).
% 2.80/0.77  fof(f6214,plain,(
% 2.80/0.77    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_161 | ~spl8_187 | ~spl8_212)),
% 2.80/0.77    inference(subsumption_resolution,[],[f6211,f4255])).
% 2.80/0.77  fof(f4255,plain,(
% 2.80/0.77    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~spl8_161),
% 2.80/0.77    inference(avatar_component_clause,[],[f4253])).
% 2.80/0.77  fof(f4253,plain,(
% 2.80/0.77    spl8_161 <=> v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_161])])).
% 2.80/0.77  fof(f6211,plain,(
% 2.80/0.77    ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_187 | ~spl8_212)),
% 2.80/0.77    inference(superposition,[],[f6177,f5644])).
% 2.80/0.77  fof(f5644,plain,(
% 2.80/0.77    k1_xboole_0 = u1_struct_0(sK1) | ~spl8_187),
% 2.80/0.77    inference(avatar_component_clause,[],[f5642])).
% 2.80/0.77  fof(f5642,plain,(
% 2.80/0.77    spl8_187 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_187])])).
% 2.80/0.77  fof(f6177,plain,(
% 2.80/0.77    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0)) | ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,sK6(sK0,X0,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,k2_pre_topc(X0,sK6(sK0,X0,k1_xboole_0)))) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl8_212),
% 2.80/0.77    inference(avatar_component_clause,[],[f6176])).
% 2.80/0.77  fof(f6176,plain,(
% 2.80/0.77    spl8_212 <=> ! [X0] : (~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,sK6(sK0,X0,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,k2_pre_topc(X0,sK6(sK0,X0,k1_xboole_0)))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_212])])).
% 2.80/0.77  fof(f6178,plain,(
% 2.80/0.77    spl8_212 | ~spl8_1 | ~spl8_3 | ~spl8_16 | ~spl8_170),
% 2.80/0.77    inference(avatar_split_clause,[],[f4512,f4498,f255,f173,f163,f6176])).
% 2.80/0.77  fof(f163,plain,(
% 2.80/0.77    spl8_1 <=> v2_pre_topc(sK0)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.80/0.77  fof(f173,plain,(
% 2.80/0.77    spl8_3 <=> l1_pre_topc(sK0)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.80/0.77  fof(f255,plain,(
% 2.80/0.77    spl8_16 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 2.80/0.77  fof(f4498,plain,(
% 2.80/0.77    spl8_170 <=> ! [X1,X0] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,sK6(X0,X1,k1_xboole_0))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,k2_pre_topc(X1,sK6(X0,X1,k1_xboole_0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_170])])).
% 2.80/0.77  fof(f4512,plain,(
% 2.80/0.77    ( ! [X0] : (~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,sK6(sK0,X0,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,k2_pre_topc(X0,sK6(sK0,X0,k1_xboole_0)))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl8_1 | ~spl8_3 | ~spl8_16 | ~spl8_170)),
% 2.80/0.77    inference(forward_demodulation,[],[f4511,f257])).
% 2.80/0.77  fof(f257,plain,(
% 2.80/0.77    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl8_16),
% 2.80/0.77    inference(avatar_component_clause,[],[f255])).
% 2.80/0.77  fof(f4511,plain,(
% 2.80/0.77    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,sK6(sK0,X0,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,k2_pre_topc(X0,sK6(sK0,X0,k1_xboole_0))))) ) | (~spl8_1 | ~spl8_3 | ~spl8_16 | ~spl8_170)),
% 2.80/0.77    inference(forward_demodulation,[],[f4510,f257])).
% 2.80/0.77  fof(f4510,plain,(
% 2.80/0.77    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,sK6(sK0,X0,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,k2_pre_topc(X0,sK6(sK0,X0,k1_xboole_0))))) ) | (~spl8_1 | ~spl8_3 | ~spl8_170)),
% 2.80/0.77    inference(subsumption_resolution,[],[f4508,f175])).
% 2.80/0.77  fof(f175,plain,(
% 2.80/0.77    l1_pre_topc(sK0) | ~spl8_3),
% 2.80/0.77    inference(avatar_component_clause,[],[f173])).
% 2.80/0.77  fof(f4508,plain,(
% 2.80/0.77    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(sK0) | ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,sK6(sK0,X0,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),k1_xboole_0,k2_pre_topc(X0,sK6(sK0,X0,k1_xboole_0))))) ) | (~spl8_1 | ~spl8_170)),
% 2.80/0.77    inference(resolution,[],[f4499,f165])).
% 2.80/0.77  fof(f165,plain,(
% 2.80/0.77    v2_pre_topc(sK0) | ~spl8_1),
% 2.80/0.77    inference(avatar_component_clause,[],[f163])).
% 2.80/0.77  fof(f4499,plain,(
% 2.80/0.77    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,sK6(X0,X1,k1_xboole_0))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,k2_pre_topc(X1,sK6(X0,X1,k1_xboole_0))))) ) | ~spl8_170),
% 2.80/0.77    inference(avatar_component_clause,[],[f4498])).
% 2.80/0.77  fof(f5897,plain,(
% 2.80/0.77    spl8_206 | ~spl8_204),
% 2.80/0.77    inference(avatar_split_clause,[],[f5868,f5839,f5881])).
% 2.80/0.77  fof(f5839,plain,(
% 2.80/0.77    spl8_204 <=> r1_tarski(sK6(sK0,sK1,k1_xboole_0),k1_xboole_0)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_204])])).
% 2.80/0.77  fof(f5868,plain,(
% 2.80/0.77    k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0) | ~spl8_204),
% 2.80/0.77    inference(subsumption_resolution,[],[f5867,f102])).
% 2.80/0.77  fof(f5867,plain,(
% 2.80/0.77    ~r1_tarski(k1_xboole_0,sK6(sK0,sK1,k1_xboole_0)) | k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0) | ~spl8_204),
% 2.80/0.77    inference(resolution,[],[f5841,f136])).
% 2.80/0.77  fof(f136,plain,(
% 2.80/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.80/0.77    inference(cnf_transformation,[],[f83])).
% 2.80/0.77  fof(f83,plain,(
% 2.80/0.77    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.80/0.77    inference(flattening,[],[f82])).
% 2.80/0.77  fof(f82,plain,(
% 2.80/0.77    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.80/0.77    inference(nnf_transformation,[],[f2])).
% 2.80/0.77  fof(f2,axiom,(
% 2.80/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.80/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.80/0.77  fof(f5841,plain,(
% 2.80/0.77    r1_tarski(sK6(sK0,sK1,k1_xboole_0),k1_xboole_0) | ~spl8_204),
% 2.80/0.77    inference(avatar_component_clause,[],[f5839])).
% 2.80/0.77  fof(f5842,plain,(
% 2.80/0.77    spl8_204 | ~spl8_196),
% 2.80/0.77    inference(avatar_split_clause,[],[f5785,f5754,f5839])).
% 2.80/0.77  fof(f5754,plain,(
% 2.80/0.77    spl8_196 <=> m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_196])])).
% 2.80/0.77  fof(f5785,plain,(
% 2.80/0.77    r1_tarski(sK6(sK0,sK1,k1_xboole_0),k1_xboole_0) | ~spl8_196),
% 2.80/0.77    inference(resolution,[],[f5756,f141])).
% 2.80/0.77  fof(f141,plain,(
% 2.80/0.77    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.80/0.77    inference(cnf_transformation,[],[f88])).
% 2.80/0.77  fof(f88,plain,(
% 2.80/0.77    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.80/0.77    inference(nnf_transformation,[],[f12])).
% 2.80/0.77  fof(f12,axiom,(
% 2.80/0.77    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.80/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.80/0.77  fof(f5756,plain,(
% 2.80/0.77    m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl8_196),
% 2.80/0.77    inference(avatar_component_clause,[],[f5754])).
% 2.80/0.77  fof(f5757,plain,(
% 2.80/0.77    spl8_196 | ~spl8_4 | ~spl8_5 | spl8_158 | ~spl8_161 | ~spl8_182 | ~spl8_187),
% 2.80/0.77    inference(avatar_split_clause,[],[f5661,f5642,f5343,f4253,f4240,f183,f178,f5754])).
% 2.80/0.77  fof(f5343,plain,(
% 2.80/0.77    spl8_182 <=> ! [X0] : (~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK6(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_182])])).
% 2.80/0.77  fof(f5661,plain,(
% 2.80/0.77    m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl8_4 | ~spl8_5 | spl8_158 | ~spl8_161 | ~spl8_182 | ~spl8_187)),
% 2.80/0.77    inference(subsumption_resolution,[],[f5660,f180])).
% 2.80/0.77  fof(f5660,plain,(
% 2.80/0.77    ~v2_pre_topc(sK1) | m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl8_5 | spl8_158 | ~spl8_161 | ~spl8_182 | ~spl8_187)),
% 2.80/0.77    inference(subsumption_resolution,[],[f5659,f185])).
% 2.80/0.77  fof(f5659,plain,(
% 2.80/0.77    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl8_158 | ~spl8_161 | ~spl8_182 | ~spl8_187)),
% 2.80/0.77    inference(subsumption_resolution,[],[f5658,f4242])).
% 2.80/0.77  fof(f5658,plain,(
% 2.80/0.77    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl8_161 | ~spl8_182 | ~spl8_187)),
% 2.80/0.77    inference(subsumption_resolution,[],[f5656,f4255])).
% 2.80/0.77  fof(f5656,plain,(
% 2.80/0.77    ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | m1_subset_1(sK6(sK0,sK1,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl8_182 | ~spl8_187)),
% 2.80/0.77    inference(superposition,[],[f5344,f5644])).
% 2.80/0.77  fof(f5344,plain,(
% 2.80/0.77    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK6(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl8_182),
% 2.80/0.77    inference(avatar_component_clause,[],[f5343])).
% 2.80/0.77  fof(f5645,plain,(
% 2.80/0.77    spl8_187 | ~spl8_18 | ~spl8_140),
% 2.80/0.77    inference(avatar_split_clause,[],[f5585,f3680,f265,f5642])).
% 2.80/0.77  fof(f265,plain,(
% 2.80/0.77    spl8_18 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 2.80/0.77  fof(f3680,plain,(
% 2.80/0.77    spl8_140 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_140])])).
% 2.80/0.77  fof(f5585,plain,(
% 2.80/0.77    k1_xboole_0 = u1_struct_0(sK1) | (~spl8_18 | ~spl8_140)),
% 2.80/0.77    inference(backward_demodulation,[],[f267,f3682])).
% 2.80/0.77  fof(f3682,plain,(
% 2.80/0.77    k1_xboole_0 = k2_struct_0(sK1) | ~spl8_140),
% 2.80/0.77    inference(avatar_component_clause,[],[f3680])).
% 2.80/0.77  fof(f267,plain,(
% 2.80/0.77    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl8_18),
% 2.80/0.77    inference(avatar_component_clause,[],[f265])).
% 2.80/0.77  fof(f5403,plain,(
% 2.80/0.77    ~spl8_5 | spl8_8 | ~spl8_18 | ~spl8_19 | ~spl8_20 | spl8_140 | ~spl8_185),
% 2.80/0.77    inference(avatar_contradiction_clause,[],[f5402])).
% 2.80/0.77  fof(f5402,plain,(
% 2.80/0.77    $false | (~spl8_5 | spl8_8 | ~spl8_18 | ~spl8_19 | ~spl8_20 | spl8_140 | ~spl8_185)),
% 2.80/0.77    inference(subsumption_resolution,[],[f5401,f185])).
% 2.80/0.77  fof(f5401,plain,(
% 2.80/0.77    ~l1_pre_topc(sK1) | (spl8_8 | ~spl8_18 | ~spl8_19 | ~spl8_20 | spl8_140 | ~spl8_185)),
% 2.80/0.77    inference(subsumption_resolution,[],[f5400,f200])).
% 2.80/0.77  fof(f200,plain,(
% 2.80/0.77    ~v5_pre_topc(sK2,sK0,sK1) | spl8_8),
% 2.80/0.77    inference(avatar_component_clause,[],[f198])).
% 2.80/0.77  fof(f198,plain,(
% 2.80/0.77    spl8_8 <=> v5_pre_topc(sK2,sK0,sK1)),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.80/0.77  fof(f5400,plain,(
% 2.80/0.77    v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | (~spl8_18 | ~spl8_19 | ~spl8_20 | spl8_140 | ~spl8_185)),
% 2.80/0.77    inference(subsumption_resolution,[],[f5399,f3681])).
% 2.80/0.77  fof(f3681,plain,(
% 2.80/0.77    k1_xboole_0 != k2_struct_0(sK1) | spl8_140),
% 2.80/0.77    inference(avatar_component_clause,[],[f3680])).
% 2.80/0.77  fof(f5399,plain,(
% 2.80/0.77    k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | (~spl8_18 | ~spl8_19 | ~spl8_20 | ~spl8_185)),
% 2.80/0.77    inference(subsumption_resolution,[],[f5398,f282])).
% 2.80/0.77  fof(f282,plain,(
% 2.80/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl8_20),
% 2.80/0.77    inference(avatar_component_clause,[],[f280])).
% 2.80/0.77  fof(f280,plain,(
% 2.80/0.77    spl8_20 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 2.80/0.77    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 2.80/0.78  fof(f5398,plain,(
% 2.80/0.78    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | (~spl8_18 | ~spl8_19 | ~spl8_185)),
% 2.80/0.78    inference(subsumption_resolution,[],[f5396,f274])).
% 2.80/0.78  fof(f274,plain,(
% 2.80/0.78    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl8_19),
% 2.80/0.78    inference(avatar_component_clause,[],[f272])).
% 2.80/0.78  fof(f272,plain,(
% 2.80/0.78    spl8_19 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 2.80/0.78  fof(f5396,plain,(
% 2.80/0.78    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | (~spl8_18 | ~spl8_185)),
% 2.80/0.78    inference(superposition,[],[f5380,f267])).
% 2.80/0.78  fof(f5380,plain,(
% 2.80/0.78    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | v5_pre_topc(sK2,sK0,X0) | ~l1_pre_topc(X0)) ) | ~spl8_185),
% 2.80/0.78    inference(avatar_component_clause,[],[f5379])).
% 2.80/0.78  fof(f5379,plain,(
% 2.80/0.78    spl8_185 <=> ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | v5_pre_topc(sK2,sK0,X0) | ~l1_pre_topc(X0))),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_185])])).
% 2.80/0.78  fof(f5381,plain,(
% 2.80/0.78    spl8_185 | ~spl8_3 | ~spl8_16 | ~spl8_68 | ~spl8_105),
% 2.80/0.78    inference(avatar_split_clause,[],[f5231,f2013,f1153,f255,f173,f5379])).
% 2.80/0.78  fof(f1153,plain,(
% 2.80/0.78    spl8_68 <=> ! [X1,X0] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK3(X0,X1,sK2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0))),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).
% 2.80/0.78  fof(f2013,plain,(
% 2.80/0.78    spl8_105 <=> ! [X1,X0,X2] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),X0,X1,X2),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))))),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).
% 2.80/0.78  fof(f5231,plain,(
% 2.80/0.78    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | v5_pre_topc(sK2,sK0,X0) | ~l1_pre_topc(X0)) ) | (~spl8_3 | ~spl8_16 | ~spl8_68 | ~spl8_105)),
% 2.80/0.78    inference(subsumption_resolution,[],[f5230,f2014])).
% 2.80/0.78  fof(f2014,plain,(
% 2.80/0.78    ( ! [X2,X0,X1] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),X0,X1,X2),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | ~spl8_105),
% 2.80/0.78    inference(avatar_component_clause,[],[f2013])).
% 2.80/0.78  fof(f5230,plain,(
% 2.80/0.78    ( ! [X0] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),sK2,sK3(sK0,X0,sK2)),sK0) | ~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | v5_pre_topc(sK2,sK0,X0) | ~l1_pre_topc(X0)) ) | (~spl8_3 | ~spl8_16 | ~spl8_68)),
% 2.80/0.78    inference(forward_demodulation,[],[f5229,f257])).
% 2.80/0.78  fof(f5229,plain,(
% 2.80/0.78    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | v5_pre_topc(sK2,sK0,X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK3(sK0,X0,sK2)),sK0)) ) | (~spl8_3 | ~spl8_16 | ~spl8_68)),
% 2.80/0.78    inference(forward_demodulation,[],[f5228,f257])).
% 2.80/0.78  fof(f5228,plain,(
% 2.80/0.78    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k1_xboole_0 = k2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK2,sK0,X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK3(sK0,X0,sK2)),sK0)) ) | (~spl8_3 | ~spl8_16 | ~spl8_68)),
% 2.80/0.78    inference(forward_demodulation,[],[f5226,f257])).
% 2.80/0.78  fof(f5226,plain,(
% 2.80/0.78    ( ! [X0] : (k1_xboole_0 = k2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK2,sK0,X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK3(sK0,X0,sK2)),sK0)) ) | (~spl8_3 | ~spl8_68)),
% 2.80/0.78    inference(resolution,[],[f1154,f175])).
% 2.80/0.78  fof(f1154,plain,(
% 2.80/0.78    ( ! [X0,X1] : (~l1_pre_topc(X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | ~l1_pre_topc(X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK3(X0,X1,sK2)),X0)) ) | ~spl8_68),
% 2.80/0.78    inference(avatar_component_clause,[],[f1153])).
% 2.80/0.78  fof(f5345,plain,(
% 2.80/0.78    spl8_182 | ~spl8_1 | ~spl8_3 | ~spl8_16 | ~spl8_165),
% 2.80/0.78    inference(avatar_split_clause,[],[f4415,f4398,f255,f173,f163,f5343])).
% 2.80/0.78  fof(f4398,plain,(
% 2.80/0.78    spl8_165 <=> ! [X5,X4] : (m1_subset_1(sK6(X4,X5,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X5))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X4),u1_struct_0(X5)) | v5_pre_topc(k1_xboole_0,X4,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4))),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_165])])).
% 2.80/0.78  fof(f4415,plain,(
% 2.80/0.78    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK6(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl8_1 | ~spl8_3 | ~spl8_16 | ~spl8_165)),
% 2.80/0.78    inference(forward_demodulation,[],[f4414,f257])).
% 2.80/0.78  fof(f4414,plain,(
% 2.80/0.78    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK6(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl8_1 | ~spl8_3 | ~spl8_165)),
% 2.80/0.78    inference(subsumption_resolution,[],[f4412,f175])).
% 2.80/0.78  fof(f4412,plain,(
% 2.80/0.78    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(sK0) | m1_subset_1(sK6(sK0,X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl8_1 | ~spl8_165)),
% 2.80/0.78    inference(resolution,[],[f4399,f165])).
% 2.80/0.78  fof(f4399,plain,(
% 2.80/0.78    ( ! [X4,X5] : (~v2_pre_topc(X4) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X4),u1_struct_0(X5)) | v5_pre_topc(k1_xboole_0,X4,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X4) | m1_subset_1(sK6(X4,X5,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X5)))) ) | ~spl8_165),
% 2.80/0.78    inference(avatar_component_clause,[],[f4398])).
% 2.80/0.78  fof(f5051,plain,(
% 2.80/0.78    k1_xboole_0 != sK2 | v1_funct_1(k1_xboole_0) | ~v1_funct_1(sK2)),
% 2.80/0.78    introduced(theory_tautology_sat_conflict,[])).
% 2.80/0.78  fof(f5050,plain,(
% 2.80/0.78    ~spl8_158 | spl8_8 | ~spl8_156),
% 2.80/0.78    inference(avatar_split_clause,[],[f4327,f4208,f198,f4240])).
% 2.80/0.78  fof(f4208,plain,(
% 2.80/0.78    spl8_156 <=> k1_xboole_0 = sK2),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_156])])).
% 2.80/0.78  fof(f4327,plain,(
% 2.80/0.78    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl8_8 | ~spl8_156)),
% 2.80/0.78    inference(backward_demodulation,[],[f200,f4210])).
% 2.80/0.78  fof(f4210,plain,(
% 2.80/0.78    k1_xboole_0 = sK2 | ~spl8_156),
% 2.80/0.78    inference(avatar_component_clause,[],[f4208])).
% 2.80/0.78  fof(f4500,plain,(
% 2.80/0.78    spl8_170 | ~spl8_157),
% 2.80/0.78    inference(avatar_split_clause,[],[f4234,f4225,f4498])).
% 2.80/0.78  fof(f4225,plain,(
% 2.80/0.78    spl8_157 <=> v1_funct_1(k1_xboole_0)),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_157])])).
% 2.80/0.78  fof(f4234,plain,(
% 2.80/0.78    ( ! [X0,X1] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,sK6(X0,X1,k1_xboole_0))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,k2_pre_topc(X1,sK6(X0,X1,k1_xboole_0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl8_157),
% 2.80/0.78    inference(subsumption_resolution,[],[f4229,f104])).
% 2.80/0.78  fof(f104,plain,(
% 2.80/0.78    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.80/0.78    inference(cnf_transformation,[],[f10])).
% 2.80/0.78  fof(f10,axiom,(
% 2.80/0.78    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.80/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.80/0.78  fof(f4229,plain,(
% 2.80/0.78    ( ! [X0,X1] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,sK6(X0,X1,k1_xboole_0))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k1_xboole_0,k2_pre_topc(X1,sK6(X0,X1,k1_xboole_0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl8_157),
% 2.80/0.78    inference(resolution,[],[f4227,f129])).
% 2.80/0.78  fof(f129,plain,(
% 2.80/0.78    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.80/0.78    inference(cnf_transformation,[],[f80])).
% 2.80/0.78  fof(f80,plain,(
% 2.80/0.78    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.80/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f78,f79])).
% 2.80/0.78  fof(f79,plain,(
% 2.80/0.78    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.80/0.78    introduced(choice_axiom,[])).
% 2.80/0.78  fof(f78,plain,(
% 2.80/0.78    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.80/0.78    inference(rectify,[],[f77])).
% 2.80/0.78  fof(f77,plain,(
% 2.80/0.78    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.80/0.78    inference(nnf_transformation,[],[f47])).
% 2.80/0.78  fof(f47,plain,(
% 2.80/0.78    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.80/0.78    inference(flattening,[],[f46])).
% 2.80/0.78  fof(f46,plain,(
% 2.80/0.78    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.80/0.78    inference(ennf_transformation,[],[f26])).
% 2.80/0.78  fof(f26,axiom,(
% 2.80/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 2.80/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).
% 2.80/0.78  fof(f4227,plain,(
% 2.80/0.78    v1_funct_1(k1_xboole_0) | ~spl8_157),
% 2.80/0.78    inference(avatar_component_clause,[],[f4225])).
% 2.80/0.78  fof(f4400,plain,(
% 2.80/0.78    spl8_165 | ~spl8_157),
% 2.80/0.78    inference(avatar_split_clause,[],[f4236,f4225,f4398])).
% 2.80/0.78  fof(f4236,plain,(
% 2.80/0.78    ( ! [X4,X5] : (m1_subset_1(sK6(X4,X5,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X5))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X4),u1_struct_0(X5)) | v5_pre_topc(k1_xboole_0,X4,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4)) ) | ~spl8_157),
% 2.80/0.78    inference(subsumption_resolution,[],[f4231,f104])).
% 2.80/0.78  fof(f4231,plain,(
% 2.80/0.78    ( ! [X4,X5] : (m1_subset_1(sK6(X4,X5,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X5))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X4),u1_struct_0(X5)) | v5_pre_topc(k1_xboole_0,X4,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4)) ) | ~spl8_157),
% 2.80/0.78    inference(resolution,[],[f4227,f128])).
% 2.80/0.78  fof(f128,plain,(
% 2.80/0.78    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.80/0.78    inference(cnf_transformation,[],[f80])).
% 2.80/0.78  fof(f4258,plain,(
% 2.80/0.78    spl8_156 | ~spl8_155),
% 2.80/0.78    inference(avatar_split_clause,[],[f4176,f4157,f4208])).
% 2.80/0.78  fof(f4157,plain,(
% 2.80/0.78    spl8_155 <=> r1_tarski(sK2,k1_xboole_0)),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_155])])).
% 2.80/0.78  fof(f4176,plain,(
% 2.80/0.78    k1_xboole_0 = sK2 | ~spl8_155),
% 2.80/0.78    inference(subsumption_resolution,[],[f4175,f102])).
% 2.80/0.78  fof(f4175,plain,(
% 2.80/0.78    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2 | ~spl8_155),
% 2.80/0.78    inference(resolution,[],[f4159,f136])).
% 2.80/0.78  fof(f4159,plain,(
% 2.80/0.78    r1_tarski(sK2,k1_xboole_0) | ~spl8_155),
% 2.80/0.78    inference(avatar_component_clause,[],[f4157])).
% 2.80/0.78  fof(f4256,plain,(
% 2.80/0.78    spl8_161 | ~spl8_101 | ~spl8_140 | ~spl8_154),
% 2.80/0.78    inference(avatar_split_clause,[],[f4205,f4148,f3680,f1823,f4253])).
% 2.80/0.78  fof(f1823,plain,(
% 2.80/0.78    spl8_101 <=> sK2 = k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).
% 2.80/0.78  fof(f4148,plain,(
% 2.80/0.78    spl8_154 <=> v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_154])])).
% 2.80/0.78  fof(f4205,plain,(
% 2.80/0.78    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | (~spl8_101 | ~spl8_140 | ~spl8_154)),
% 2.80/0.78    inference(backward_demodulation,[],[f4150,f4105])).
% 2.80/0.78  fof(f4105,plain,(
% 2.80/0.78    k1_xboole_0 = sK2 | (~spl8_101 | ~spl8_140)),
% 2.80/0.78    inference(forward_demodulation,[],[f4104,f160])).
% 2.80/0.78  fof(f160,plain,(
% 2.80/0.78    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.80/0.78    inference(equality_resolution,[],[f145])).
% 2.80/0.78  fof(f145,plain,(
% 2.80/0.78    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.80/0.78    inference(cnf_transformation,[],[f90])).
% 2.80/0.78  fof(f90,plain,(
% 2.80/0.78    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.80/0.78    inference(flattening,[],[f89])).
% 2.80/0.78  fof(f89,plain,(
% 2.80/0.78    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.80/0.78    inference(nnf_transformation,[],[f6])).
% 2.80/0.78  fof(f6,axiom,(
% 2.80/0.78    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.80/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.80/0.78  fof(f4104,plain,(
% 2.80/0.78    sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0) | (~spl8_101 | ~spl8_140)),
% 2.80/0.78    inference(forward_demodulation,[],[f1825,f3682])).
% 2.80/0.78  fof(f1825,plain,(
% 2.80/0.78    sK2 = k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl8_101),
% 2.80/0.78    inference(avatar_component_clause,[],[f1823])).
% 2.80/0.78  fof(f4150,plain,(
% 2.80/0.78    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~spl8_154),
% 2.80/0.78    inference(avatar_component_clause,[],[f4148])).
% 2.80/0.78  fof(f4160,plain,(
% 2.80/0.78    spl8_155 | ~spl8_30 | ~spl8_140),
% 2.80/0.78    inference(avatar_split_clause,[],[f4062,f3680,f472,f4157])).
% 2.80/0.78  fof(f472,plain,(
% 2.80/0.78    spl8_30 <=> r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 2.80/0.78  fof(f4062,plain,(
% 2.80/0.78    r1_tarski(sK2,k1_xboole_0) | (~spl8_30 | ~spl8_140)),
% 2.80/0.78    inference(forward_demodulation,[],[f4011,f160])).
% 2.80/0.78  fof(f4011,plain,(
% 2.80/0.78    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) | (~spl8_30 | ~spl8_140)),
% 2.80/0.78    inference(backward_demodulation,[],[f474,f3682])).
% 2.80/0.78  fof(f474,plain,(
% 2.80/0.78    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | ~spl8_30),
% 2.80/0.78    inference(avatar_component_clause,[],[f472])).
% 2.80/0.78  fof(f4151,plain,(
% 2.80/0.78    spl8_154 | ~spl8_19 | ~spl8_140),
% 2.80/0.78    inference(avatar_split_clause,[],[f4008,f3680,f272,f4148])).
% 2.80/0.78  fof(f4008,plain,(
% 2.80/0.78    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | (~spl8_19 | ~spl8_140)),
% 2.80/0.78    inference(backward_demodulation,[],[f274,f3682])).
% 2.80/0.78  fof(f4075,plain,(
% 2.80/0.78    spl8_102 | ~spl8_140),
% 2.80/0.78    inference(avatar_contradiction_clause,[],[f4074])).
% 2.80/0.78  fof(f4074,plain,(
% 2.80/0.78    $false | (spl8_102 | ~spl8_140)),
% 2.80/0.78    inference(subsumption_resolution,[],[f4073,f102])).
% 2.80/0.78  fof(f4073,plain,(
% 2.80/0.78    ~r1_tarski(k1_xboole_0,sK2) | (spl8_102 | ~spl8_140)),
% 2.80/0.78    inference(forward_demodulation,[],[f4035,f160])).
% 2.80/0.78  fof(f4035,plain,(
% 2.80/0.78    ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0),sK2) | (spl8_102 | ~spl8_140)),
% 2.80/0.78    inference(backward_demodulation,[],[f1829,f3682])).
% 2.80/0.78  fof(f1829,plain,(
% 2.80/0.78    ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2) | spl8_102),
% 2.80/0.78    inference(avatar_component_clause,[],[f1827])).
% 2.80/0.78  fof(f1827,plain,(
% 2.80/0.78    spl8_102 <=> r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2)),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).
% 2.80/0.78  fof(f2015,plain,(
% 2.80/0.78    spl8_105 | ~spl8_38),
% 2.80/0.78    inference(avatar_split_clause,[],[f574,f557,f2013])).
% 2.80/0.78  fof(f557,plain,(
% 2.80/0.78    spl8_38 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(X0,sK0))),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 2.80/0.78  fof(f574,plain,(
% 2.80/0.78    ( ! [X2,X0,X1] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),X0,X1,X2),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | ~spl8_38),
% 2.80/0.78    inference(resolution,[],[f558,f154])).
% 2.80/0.78  fof(f154,plain,(
% 2.80/0.78    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.78    inference(cnf_transformation,[],[f60])).
% 2.80/0.78  fof(f60,plain,(
% 2.80/0.78    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.78    inference(ennf_transformation,[],[f17])).
% 2.80/0.78  fof(f17,axiom,(
% 2.80/0.78    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 2.80/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 2.80/0.78  fof(f558,plain,(
% 2.80/0.78    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(X0,sK0)) ) | ~spl8_38),
% 2.80/0.78    inference(avatar_component_clause,[],[f557])).
% 2.80/0.78  fof(f1830,plain,(
% 2.80/0.78    spl8_101 | ~spl8_102 | ~spl8_30),
% 2.80/0.78    inference(avatar_split_clause,[],[f476,f472,f1827,f1823])).
% 2.80/0.78  fof(f476,plain,(
% 2.80/0.78    ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2) | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl8_30),
% 2.80/0.78    inference(resolution,[],[f474,f136])).
% 2.80/0.78  fof(f1155,plain,(
% 2.80/0.78    spl8_68 | ~spl8_6),
% 2.80/0.78    inference(avatar_split_clause,[],[f463,f188,f1153])).
% 2.80/0.78  fof(f188,plain,(
% 2.80/0.78    spl8_6 <=> v1_funct_1(sK2)),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.80/0.78  fof(f463,plain,(
% 2.80/0.78    ( ! [X0,X1] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK3(X0,X1,sK2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) ) | ~spl8_6),
% 2.80/0.78    inference(resolution,[],[f117,f190])).
% 2.80/0.78  fof(f190,plain,(
% 2.80/0.78    v1_funct_1(sK2) | ~spl8_6),
% 2.80/0.78    inference(avatar_component_clause,[],[f188])).
% 2.80/0.78  fof(f117,plain,(
% 2.80/0.78    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.80/0.78    inference(cnf_transformation,[],[f68])).
% 2.80/0.78  fof(f68,plain,(
% 2.80/0.78    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.80/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f66,f67])).
% 2.80/0.78  fof(f67,plain,(
% 2.80/0.78    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.80/0.78    introduced(choice_axiom,[])).
% 2.80/0.78  fof(f66,plain,(
% 2.80/0.78    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.80/0.78    inference(rectify,[],[f65])).
% 2.80/0.78  fof(f65,plain,(
% 2.80/0.78    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.80/0.78    inference(nnf_transformation,[],[f39])).
% 2.80/0.78  fof(f39,plain,(
% 2.80/0.78    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.80/0.78    inference(flattening,[],[f38])).
% 2.80/0.78  fof(f38,plain,(
% 2.80/0.78    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.80/0.78    inference(ennf_transformation,[],[f25])).
% 2.80/0.78  fof(f25,axiom,(
% 2.80/0.78    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 2.80/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).
% 2.80/0.78  fof(f657,plain,(
% 2.80/0.78    spl8_47 | ~spl8_31),
% 2.80/0.78    inference(avatar_split_clause,[],[f653,f509,f655])).
% 2.80/0.78  fof(f509,plain,(
% 2.80/0.78    spl8_31 <=> ! [X1,X2] : k1_xboole_0 = k1_relset_1(X1,X2,k1_xboole_0)),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 2.80/0.78  fof(f653,plain,(
% 2.80/0.78    ( ! [X2,X1] : (k1_xboole_0 = k8_relset_1(X1,X2,k1_xboole_0,X2)) ) | ~spl8_31),
% 2.80/0.78    inference(forward_demodulation,[],[f433,f510])).
% 2.80/0.78  fof(f510,plain,(
% 2.80/0.78    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(X1,X2,k1_xboole_0)) ) | ~spl8_31),
% 2.80/0.78    inference(avatar_component_clause,[],[f509])).
% 2.80/0.78  fof(f433,plain,(
% 2.80/0.78    ( ! [X2,X1] : (k1_relset_1(X1,X2,k1_xboole_0) = k8_relset_1(X1,X2,k1_xboole_0,X2)) )),
% 2.80/0.78    inference(resolution,[],[f152,f104])).
% 2.80/0.78  fof(f152,plain,(
% 2.80/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 2.80/0.78    inference(cnf_transformation,[],[f57])).
% 2.80/0.78  fof(f57,plain,(
% 2.80/0.78    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.78    inference(ennf_transformation,[],[f19])).
% 2.80/0.78  fof(f19,axiom,(
% 2.80/0.78    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 2.80/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 2.80/0.78  fof(f647,plain,(
% 2.80/0.78    spl8_46 | ~spl8_3 | ~spl8_42),
% 2.80/0.78    inference(avatar_split_clause,[],[f612,f599,f173,f644])).
% 2.80/0.78  fof(f599,plain,(
% 2.80/0.78    spl8_42 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 2.80/0.78  fof(f612,plain,(
% 2.80/0.78    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | (~spl8_3 | ~spl8_42)),
% 2.80/0.78    inference(subsumption_resolution,[],[f611,f175])).
% 2.80/0.78  fof(f611,plain,(
% 2.80/0.78    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~l1_pre_topc(sK0) | ~spl8_42),
% 2.80/0.78    inference(subsumption_resolution,[],[f610,f104])).
% 2.80/0.78  fof(f610,plain,(
% 2.80/0.78    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl8_42),
% 2.80/0.78    inference(resolution,[],[f601,f119])).
% 2.80/0.78  fof(f119,plain,(
% 2.80/0.78    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.80/0.78    inference(cnf_transformation,[],[f41])).
% 2.80/0.78  fof(f41,plain,(
% 2.80/0.78    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.80/0.78    inference(flattening,[],[f40])).
% 2.80/0.78  fof(f40,plain,(
% 2.80/0.78    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.80/0.78    inference(ennf_transformation,[],[f24])).
% 2.80/0.78  fof(f24,axiom,(
% 2.80/0.78    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.80/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.80/0.78  fof(f601,plain,(
% 2.80/0.78    v4_pre_topc(k1_xboole_0,sK0) | ~spl8_42),
% 2.80/0.78    inference(avatar_component_clause,[],[f599])).
% 2.80/0.78  fof(f602,plain,(
% 2.80/0.78    spl8_42 | ~spl8_39),
% 2.80/0.78    inference(avatar_split_clause,[],[f581,f562,f599])).
% 2.80/0.78  fof(f562,plain,(
% 2.80/0.78    spl8_39 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0))),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 2.80/0.78  fof(f581,plain,(
% 2.80/0.78    v4_pre_topc(k1_xboole_0,sK0) | ~spl8_39),
% 2.80/0.78    inference(resolution,[],[f563,f104])).
% 2.80/0.78  fof(f563,plain,(
% 2.80/0.78    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | ~spl8_39),
% 2.80/0.78    inference(avatar_component_clause,[],[f562])).
% 2.80/0.78  fof(f564,plain,(
% 2.80/0.78    spl8_39 | ~spl8_2 | ~spl8_3 | ~spl8_16),
% 2.80/0.78    inference(avatar_split_clause,[],[f392,f255,f173,f168,f562])).
% 2.80/0.78  fof(f168,plain,(
% 2.80/0.78    spl8_2 <=> v1_tdlat_3(sK0)),
% 2.80/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.80/0.78  fof(f392,plain,(
% 2.80/0.78    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_16)),
% 2.80/0.78    inference(forward_demodulation,[],[f391,f257])).
% 2.80/0.78  fof(f391,plain,(
% 2.80/0.78    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl8_2 | ~spl8_3)),
% 2.80/0.78    inference(subsumption_resolution,[],[f390,f175])).
% 2.80/0.78  fof(f390,plain,(
% 2.80/0.78    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl8_2),
% 2.80/0.78    inference(resolution,[],[f383,f170])).
% 2.80/0.78  fof(f170,plain,(
% 2.80/0.78    v1_tdlat_3(sK0) | ~spl8_2),
% 2.80/0.78    inference(avatar_component_clause,[],[f168])).
% 2.80/0.78  fof(f383,plain,(
% 2.80/0.78    ( ! [X2,X0] : (~v1_tdlat_3(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 2.80/0.78    inference(subsumption_resolution,[],[f124,f110])).
% 2.80/0.78  fof(f110,plain,(
% 2.80/0.78    ( ! [X0] : (~v1_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.80/0.78    inference(cnf_transformation,[],[f37])).
% 2.80/0.78  fof(f37,plain,(
% 2.80/0.78    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.80/0.78    inference(flattening,[],[f36])).
% 2.80/0.78  fof(f36,plain,(
% 2.80/0.78    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.80/0.78    inference(ennf_transformation,[],[f27])).
% 2.80/0.78  fof(f27,axiom,(
% 2.80/0.78    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.80/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 2.80/0.78  fof(f124,plain,(
% 2.80/0.78    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.80/0.78    inference(cnf_transformation,[],[f76])).
% 2.80/0.78  fof(f76,plain,(
% 2.80/0.78    ! [X0] : (((v1_tdlat_3(X0) | (~v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.80/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f74,f75])).
% 2.80/0.78  fof(f75,plain,(
% 2.80/0.78    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.80/0.78    introduced(choice_axiom,[])).
% 2.80/0.78  fof(f74,plain,(
% 2.80/0.78    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.80/0.78    inference(rectify,[],[f73])).
% 2.80/0.78  fof(f73,plain,(
% 2.80/0.78    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.80/0.78    inference(nnf_transformation,[],[f45])).
% 2.80/0.78  fof(f45,plain,(
% 2.80/0.78    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.80/0.78    inference(flattening,[],[f44])).
% 2.80/0.78  fof(f44,plain,(
% 2.80/0.78    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.80/0.78    inference(ennf_transformation,[],[f29])).
% 2.80/0.78  fof(f29,axiom,(
% 2.80/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 2.80/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).
% 2.80/0.78  fof(f559,plain,(
% 2.80/0.78    spl8_38 | ~spl8_2 | ~spl8_3 | ~spl8_16),
% 2.80/0.78    inference(avatar_split_clause,[],[f375,f255,f173,f168,f557])).
% 2.80/0.78  fof(f375,plain,(
% 2.80/0.78    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(X0,sK0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_16)),
% 2.80/0.78    inference(forward_demodulation,[],[f374,f257])).
% 2.80/0.78  fof(f374,plain,(
% 2.80/0.78    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) ) | (~spl8_2 | ~spl8_3)),
% 2.80/0.78    inference(subsumption_resolution,[],[f373,f175])).
% 2.80/0.78  fof(f373,plain,(
% 2.80/0.78    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl8_2),
% 2.80/0.78    inference(resolution,[],[f372,f170])).
% 2.80/0.78  fof(f372,plain,(
% 2.80/0.78    ( ! [X2,X0] : (~v1_tdlat_3(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 2.80/0.78    inference(subsumption_resolution,[],[f121,f110])).
% 2.80/0.78  fof(f121,plain,(
% 2.80/0.78    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.80/0.78    inference(cnf_transformation,[],[f72])).
% 2.80/0.78  fof(f72,plain,(
% 2.80/0.78    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.80/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f70,f71])).
% 2.80/0.78  fof(f71,plain,(
% 2.80/0.78    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.80/0.78    introduced(choice_axiom,[])).
% 2.80/0.78  fof(f70,plain,(
% 2.80/0.78    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.80/0.78    inference(rectify,[],[f69])).
% 3.41/0.78  fof(f69,plain,(
% 3.41/0.78    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.41/0.78    inference(nnf_transformation,[],[f43])).
% 3.41/0.78  fof(f43,plain,(
% 3.41/0.78    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.41/0.78    inference(flattening,[],[f42])).
% 3.41/0.78  fof(f42,plain,(
% 3.41/0.78    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.41/0.78    inference(ennf_transformation,[],[f28])).
% 3.41/0.78  fof(f28,axiom,(
% 3.41/0.78    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 3.41/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 3.41/0.78  fof(f511,plain,(
% 3.41/0.78    spl8_31 | ~spl8_27),
% 3.41/0.78    inference(avatar_split_clause,[],[f507,f407,f509])).
% 3.41/0.78  fof(f407,plain,(
% 3.41/0.78    spl8_27 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.41/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 3.41/0.78  fof(f507,plain,(
% 3.41/0.78    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(X1,X2,k1_xboole_0)) ) | ~spl8_27),
% 3.41/0.78    inference(forward_demodulation,[],[f367,f409])).
% 3.41/0.78  fof(f409,plain,(
% 3.41/0.78    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl8_27),
% 3.41/0.78    inference(avatar_component_clause,[],[f407])).
% 3.41/0.78  fof(f367,plain,(
% 3.41/0.78    ( ! [X2,X1] : (k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 3.41/0.78    inference(resolution,[],[f148,f104])).
% 3.41/0.78  fof(f148,plain,(
% 3.41/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 3.41/0.78    inference(cnf_transformation,[],[f55])).
% 3.41/0.78  fof(f55,plain,(
% 3.41/0.78    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.41/0.78    inference(ennf_transformation,[],[f18])).
% 3.41/0.78  fof(f18,axiom,(
% 3.41/0.78    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.41/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 3.41/0.78  fof(f475,plain,(
% 3.41/0.78    spl8_30 | ~spl8_20),
% 3.41/0.78    inference(avatar_split_clause,[],[f284,f280,f472])).
% 3.41/0.78  fof(f284,plain,(
% 3.41/0.78    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | ~spl8_20),
% 3.41/0.78    inference(resolution,[],[f282,f141])).
% 3.41/0.78  fof(f410,plain,(
% 3.41/0.78    spl8_27 | ~spl8_22 | ~spl8_26),
% 3.41/0.78    inference(avatar_split_clause,[],[f403,f394,f322,f407])).
% 3.41/0.78  fof(f322,plain,(
% 3.41/0.78    spl8_22 <=> v1_relat_1(k1_xboole_0)),
% 3.41/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 3.41/0.78  fof(f394,plain,(
% 3.41/0.78    spl8_26 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 3.41/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 3.41/0.78  fof(f403,plain,(
% 3.41/0.78    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl8_22 | ~spl8_26)),
% 3.41/0.78    inference(subsumption_resolution,[],[f402,f324])).
% 3.41/0.78  fof(f324,plain,(
% 3.41/0.78    v1_relat_1(k1_xboole_0) | ~spl8_22),
% 3.41/0.78    inference(avatar_component_clause,[],[f322])).
% 3.41/0.78  fof(f402,plain,(
% 3.41/0.78    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl8_26),
% 3.41/0.78    inference(subsumption_resolution,[],[f401,f316])).
% 3.41/0.78  fof(f316,plain,(
% 3.41/0.78    ( ! [X1] : (v4_relat_1(k1_xboole_0,X1)) )),
% 3.41/0.78    inference(resolution,[],[f149,f104])).
% 3.41/0.78  fof(f149,plain,(
% 3.41/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 3.41/0.78    inference(cnf_transformation,[],[f56])).
% 3.41/0.78  fof(f56,plain,(
% 3.41/0.78    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.41/0.78    inference(ennf_transformation,[],[f15])).
% 3.41/0.78  fof(f15,axiom,(
% 3.41/0.78    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.41/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.41/0.78  fof(f401,plain,(
% 3.41/0.78    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl8_26),
% 3.41/0.78    inference(resolution,[],[f396,f132])).
% 3.41/0.78  fof(f132,plain,(
% 3.41/0.78    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.41/0.78    inference(cnf_transformation,[],[f81])).
% 3.41/0.78  fof(f81,plain,(
% 3.41/0.78    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.41/0.78    inference(nnf_transformation,[],[f52])).
% 3.41/0.78  fof(f52,plain,(
% 3.41/0.78    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.41/0.78    inference(flattening,[],[f51])).
% 3.41/0.78  fof(f51,plain,(
% 3.41/0.78    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.41/0.78    inference(ennf_transformation,[],[f20])).
% 3.41/0.78  fof(f20,axiom,(
% 3.41/0.78    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.41/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 3.41/0.78  fof(f396,plain,(
% 3.41/0.78    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl8_26),
% 3.41/0.78    inference(avatar_component_clause,[],[f394])).
% 3.41/0.78  fof(f397,plain,(
% 3.41/0.78    spl8_26 | ~spl8_25),
% 3.41/0.78    inference(avatar_split_clause,[],[f389,f379,f394])).
% 3.41/0.78  fof(f379,plain,(
% 3.41/0.78    spl8_25 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.41/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 3.41/0.78  fof(f389,plain,(
% 3.41/0.78    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl8_25),
% 3.41/0.78    inference(superposition,[],[f106,f381])).
% 3.41/0.78  fof(f381,plain,(
% 3.41/0.78    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl8_25),
% 3.41/0.78    inference(avatar_component_clause,[],[f379])).
% 3.41/0.78  fof(f106,plain,(
% 3.41/0.78    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 3.41/0.78    inference(cnf_transformation,[],[f21])).
% 3.41/0.78  fof(f21,axiom,(
% 3.41/0.78    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.41/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 3.41/0.78  fof(f382,plain,(
% 3.41/0.78    spl8_25 | ~spl8_13),
% 3.41/0.78    inference(avatar_split_clause,[],[f313,f237,f379])).
% 3.41/0.78  fof(f237,plain,(
% 3.41/0.78    spl8_13 <=> r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0)),
% 3.41/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 3.41/0.78  fof(f313,plain,(
% 3.41/0.78    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl8_13),
% 3.41/0.78    inference(subsumption_resolution,[],[f311,f102])).
% 3.41/0.78  fof(f311,plain,(
% 3.41/0.78    ~r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) | k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl8_13),
% 3.41/0.78    inference(resolution,[],[f136,f239])).
% 3.41/0.78  fof(f239,plain,(
% 3.41/0.78    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) | ~spl8_13),
% 3.41/0.78    inference(avatar_component_clause,[],[f237])).
% 3.41/0.78  fof(f325,plain,(
% 3.41/0.78    spl8_22),
% 3.41/0.78    inference(avatar_split_clause,[],[f299,f322])).
% 3.41/0.78  fof(f299,plain,(
% 3.41/0.78    v1_relat_1(k1_xboole_0)),
% 3.41/0.78    inference(resolution,[],[f147,f104])).
% 3.41/0.78  fof(f147,plain,(
% 3.41/0.78    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 3.41/0.78    inference(cnf_transformation,[],[f54])).
% 3.41/0.78  fof(f54,plain,(
% 3.41/0.78    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.41/0.78    inference(ennf_transformation,[],[f14])).
% 3.41/0.78  fof(f14,axiom,(
% 3.41/0.78    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.41/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.41/0.78  fof(f283,plain,(
% 3.41/0.78    spl8_20 | ~spl8_15 | ~spl8_16 | ~spl8_18),
% 3.41/0.78    inference(avatar_split_clause,[],[f276,f265,f255,f249,f280])).
% 3.41/0.78  fof(f249,plain,(
% 3.41/0.78    spl8_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.41/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 3.41/0.78  fof(f276,plain,(
% 3.41/0.78    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl8_15 | ~spl8_16 | ~spl8_18)),
% 3.41/0.78    inference(forward_demodulation,[],[f269,f267])).
% 3.41/0.78  fof(f269,plain,(
% 3.41/0.78    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | (~spl8_15 | ~spl8_16)),
% 3.41/0.78    inference(forward_demodulation,[],[f251,f257])).
% 3.41/0.78  fof(f251,plain,(
% 3.41/0.78    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl8_15),
% 3.41/0.78    inference(avatar_component_clause,[],[f249])).
% 3.41/0.78  fof(f275,plain,(
% 3.41/0.78    spl8_19 | ~spl8_17 | ~spl8_18),
% 3.41/0.78    inference(avatar_split_clause,[],[f270,f265,f260,f272])).
% 3.41/0.78  fof(f260,plain,(
% 3.41/0.78    spl8_17 <=> v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 3.41/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 3.41/0.78  fof(f270,plain,(
% 3.41/0.78    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl8_17 | ~spl8_18)),
% 3.41/0.78    inference(backward_demodulation,[],[f262,f267])).
% 3.41/0.78  fof(f262,plain,(
% 3.41/0.78    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | ~spl8_17),
% 3.41/0.78    inference(avatar_component_clause,[],[f260])).
% 3.41/0.78  fof(f268,plain,(
% 3.41/0.78    spl8_18 | ~spl8_10),
% 3.41/0.78    inference(avatar_split_clause,[],[f229,f211,f265])).
% 3.41/0.78  fof(f211,plain,(
% 3.41/0.78    spl8_10 <=> l1_struct_0(sK1)),
% 3.41/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 3.41/0.78  fof(f229,plain,(
% 3.41/0.78    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl8_10),
% 3.41/0.78    inference(resolution,[],[f108,f213])).
% 3.41/0.78  fof(f213,plain,(
% 3.41/0.78    l1_struct_0(sK1) | ~spl8_10),
% 3.41/0.78    inference(avatar_component_clause,[],[f211])).
% 3.41/0.78  fof(f108,plain,(
% 3.41/0.78    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 3.41/0.78    inference(cnf_transformation,[],[f34])).
% 3.41/0.78  fof(f34,plain,(
% 3.41/0.78    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.41/0.78    inference(ennf_transformation,[],[f22])).
% 3.41/0.78  fof(f22,axiom,(
% 3.41/0.78    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.41/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 3.41/0.78  fof(f263,plain,(
% 3.41/0.78    spl8_17 | ~spl8_9 | ~spl8_11),
% 3.41/0.78    inference(avatar_split_clause,[],[f253,f216,f205,f260])).
% 3.41/0.78  fof(f205,plain,(
% 3.41/0.78    spl8_9 <=> l1_struct_0(sK0)),
% 3.41/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 3.41/0.78  fof(f216,plain,(
% 3.41/0.78    spl8_11 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.41/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 3.41/0.78  fof(f253,plain,(
% 3.41/0.78    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl8_9 | ~spl8_11)),
% 3.41/0.78    inference(backward_demodulation,[],[f218,f228])).
% 3.41/0.78  fof(f228,plain,(
% 3.41/0.78    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl8_9),
% 3.41/0.78    inference(resolution,[],[f108,f207])).
% 3.41/0.78  fof(f207,plain,(
% 3.41/0.78    l1_struct_0(sK0) | ~spl8_9),
% 3.41/0.78    inference(avatar_component_clause,[],[f205])).
% 3.41/0.78  fof(f218,plain,(
% 3.41/0.78    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl8_11),
% 3.41/0.78    inference(avatar_component_clause,[],[f216])).
% 3.41/0.78  fof(f258,plain,(
% 3.41/0.78    spl8_16 | ~spl8_9),
% 3.41/0.78    inference(avatar_split_clause,[],[f228,f205,f255])).
% 3.41/0.78  fof(f252,plain,(
% 3.41/0.78    spl8_15),
% 3.41/0.78    inference(avatar_split_clause,[],[f98,f249])).
% 3.41/0.78  fof(f98,plain,(
% 3.41/0.78    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.41/0.78    inference(cnf_transformation,[],[f64])).
% 3.41/0.78  fof(f64,plain,(
% 3.41/0.78    ((~v5_pre_topc(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0)),
% 3.41/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f63,f62,f61])).
% 3.41/0.78  fof(f61,plain,(
% 3.41/0.78    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v5_pre_topc(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0))),
% 3.41/0.78    introduced(choice_axiom,[])).
% 3.41/0.78  fof(f62,plain,(
% 3.41/0.78    ? [X1] : (? [X2] : (~v5_pre_topc(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (~v5_pre_topc(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.41/0.78    introduced(choice_axiom,[])).
% 3.41/0.78  fof(f63,plain,(
% 3.41/0.78    ? [X2] : (~v5_pre_topc(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~v5_pre_topc(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 3.41/0.78    introduced(choice_axiom,[])).
% 3.41/0.78  fof(f33,plain,(
% 3.41/0.78    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 3.41/0.78    inference(flattening,[],[f32])).
% 3.41/0.78  fof(f32,plain,(
% 3.41/0.78    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 3.41/0.78    inference(ennf_transformation,[],[f31])).
% 3.41/0.78  fof(f31,negated_conjecture,(
% 3.41/0.78    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 3.41/0.78    inference(negated_conjecture,[],[f30])).
% 3.41/0.78  fof(f30,conjecture,(
% 3.41/0.78    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 3.41/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).
% 3.41/0.78  fof(f240,plain,(
% 3.41/0.78    spl8_13 | ~spl8_12),
% 3.41/0.78    inference(avatar_split_clause,[],[f234,f224,f237])).
% 3.41/0.78  fof(f224,plain,(
% 3.41/0.78    spl8_12 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 3.41/0.78    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 3.41/0.78  fof(f234,plain,(
% 3.41/0.78    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) | ~spl8_12),
% 3.41/0.78    inference(resolution,[],[f226,f141])).
% 3.41/0.78  fof(f226,plain,(
% 3.41/0.78    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl8_12),
% 3.41/0.78    inference(avatar_component_clause,[],[f224])).
% 3.41/0.78  fof(f230,plain,(
% 3.41/0.78    spl8_12),
% 3.41/0.78    inference(avatar_split_clause,[],[f222,f224])).
% 3.41/0.78  fof(f222,plain,(
% 3.41/0.78    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 3.41/0.78    inference(superposition,[],[f107,f161])).
% 3.41/0.78  fof(f161,plain,(
% 3.41/0.78    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.41/0.78    inference(equality_resolution,[],[f144])).
% 3.41/0.78  fof(f144,plain,(
% 3.41/0.78    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.41/0.78    inference(cnf_transformation,[],[f90])).
% 3.41/0.78  fof(f107,plain,(
% 3.41/0.78    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.41/0.78    inference(cnf_transformation,[],[f21])).
% 3.41/0.78  fof(f219,plain,(
% 3.41/0.78    spl8_11),
% 3.41/0.78    inference(avatar_split_clause,[],[f97,f216])).
% 3.41/0.78  fof(f97,plain,(
% 3.41/0.78    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.41/0.78    inference(cnf_transformation,[],[f64])).
% 3.41/0.78  fof(f214,plain,(
% 3.41/0.78    spl8_10 | ~spl8_5),
% 3.41/0.78    inference(avatar_split_clause,[],[f203,f183,f211])).
% 3.41/0.78  fof(f203,plain,(
% 3.41/0.78    l1_struct_0(sK1) | ~spl8_5),
% 3.41/0.78    inference(resolution,[],[f109,f185])).
% 3.41/0.78  fof(f109,plain,(
% 3.41/0.78    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 3.41/0.78    inference(cnf_transformation,[],[f35])).
% 3.41/0.78  fof(f35,plain,(
% 3.41/0.78    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.41/0.78    inference(ennf_transformation,[],[f23])).
% 3.41/0.78  fof(f23,axiom,(
% 3.41/0.78    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.41/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 3.41/0.78  fof(f208,plain,(
% 3.41/0.78    spl8_9 | ~spl8_3),
% 3.41/0.78    inference(avatar_split_clause,[],[f202,f173,f205])).
% 3.41/0.78  fof(f202,plain,(
% 3.41/0.78    l1_struct_0(sK0) | ~spl8_3),
% 3.41/0.78    inference(resolution,[],[f109,f175])).
% 3.41/0.78  fof(f201,plain,(
% 3.41/0.78    ~spl8_8),
% 3.41/0.78    inference(avatar_split_clause,[],[f99,f198])).
% 3.41/0.78  fof(f99,plain,(
% 3.41/0.78    ~v5_pre_topc(sK2,sK0,sK1)),
% 3.41/0.78    inference(cnf_transformation,[],[f64])).
% 3.41/0.78  fof(f191,plain,(
% 3.41/0.78    spl8_6),
% 3.41/0.78    inference(avatar_split_clause,[],[f96,f188])).
% 3.41/0.78  fof(f96,plain,(
% 3.41/0.78    v1_funct_1(sK2)),
% 3.41/0.78    inference(cnf_transformation,[],[f64])).
% 3.41/0.78  fof(f186,plain,(
% 3.41/0.78    spl8_5),
% 3.41/0.78    inference(avatar_split_clause,[],[f95,f183])).
% 3.41/0.78  fof(f95,plain,(
% 3.41/0.78    l1_pre_topc(sK1)),
% 3.41/0.78    inference(cnf_transformation,[],[f64])).
% 3.41/0.78  fof(f181,plain,(
% 3.41/0.78    spl8_4),
% 3.41/0.78    inference(avatar_split_clause,[],[f94,f178])).
% 3.41/0.78  fof(f94,plain,(
% 3.41/0.78    v2_pre_topc(sK1)),
% 3.41/0.78    inference(cnf_transformation,[],[f64])).
% 3.41/0.78  fof(f176,plain,(
% 3.41/0.78    spl8_3),
% 3.41/0.78    inference(avatar_split_clause,[],[f93,f173])).
% 3.41/0.78  fof(f93,plain,(
% 3.41/0.78    l1_pre_topc(sK0)),
% 3.41/0.78    inference(cnf_transformation,[],[f64])).
% 3.41/0.78  fof(f171,plain,(
% 3.41/0.78    spl8_2),
% 3.41/0.78    inference(avatar_split_clause,[],[f92,f168])).
% 3.41/0.78  fof(f92,plain,(
% 3.41/0.78    v1_tdlat_3(sK0)),
% 3.41/0.78    inference(cnf_transformation,[],[f64])).
% 3.41/0.78  fof(f166,plain,(
% 3.41/0.78    spl8_1),
% 3.41/0.78    inference(avatar_split_clause,[],[f91,f163])).
% 3.41/0.78  fof(f91,plain,(
% 3.41/0.78    v2_pre_topc(sK0)),
% 3.41/0.78    inference(cnf_transformation,[],[f64])).
% 3.41/0.78  % SZS output end Proof for theBenchmark
% 3.41/0.78  % (27287)------------------------------
% 3.41/0.78  % (27287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.41/0.78  % (27287)Termination reason: Refutation
% 3.41/0.78  
% 3.41/0.78  % (27287)Memory used [KB]: 9338
% 3.41/0.78  % (27287)Time elapsed: 0.386 s
% 3.41/0.78  % (27287)------------------------------
% 3.41/0.78  % (27287)------------------------------
% 3.41/0.79  % (27284)Success in time 0.432 s
%------------------------------------------------------------------------------
