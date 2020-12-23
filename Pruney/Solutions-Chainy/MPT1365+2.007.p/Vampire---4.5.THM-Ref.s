%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 244 expanded)
%              Number of leaves         :   33 ( 118 expanded)
%              Depth                    :    7
%              Number of atoms          :  460 (1210 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f72,f77,f82,f87,f91,f99,f103,f115,f128,f136,f143,f152,f156,f178,f186,f195,f209,f320,f348])).

fof(f348,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_24
    | spl3_27
    | ~ spl3_38 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_24
    | spl3_27
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f190,f345])).

fof(f345,plain,
    ( ~ v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_24
    | spl3_27
    | ~ spl3_38 ),
    inference(unit_resulting_resolution,[],[f56,f51,f66,f90,f76,f194,f208,f319])).

fof(f319,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ r1_tarski(X2,X4)
        | ~ v2_compts_1(X4,X3)
        | v2_compts_1(X2,X3)
        | ~ v4_pre_topc(X2,X3)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ r1_tarski(X2,u1_struct_0(X3)) )
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl3_38
  <=> ! [X3,X2,X4] :
        ( ~ v4_pre_topc(X2,X3)
        | ~ r1_tarski(X2,X4)
        | ~ v2_compts_1(X4,X3)
        | v2_compts_1(X2,X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ r1_tarski(X2,u1_struct_0(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

% (17731)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f208,plain,
    ( ~ v2_compts_1(k3_xboole_0(sK1,sK2),sK0)
    | spl3_27 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl3_27
  <=> v2_compts_1(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f194,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl3_24
  <=> ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f76,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f90,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_9
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f66,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_4
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f51,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f56,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f190,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_19
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f51,f56,f177,f76,f81,f185,f151])).

fof(f151,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k3_xboole_0(X1,X2),X0)
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f185,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl3_23
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f81,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f177,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_22
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f320,plain,
    ( spl3_38
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f165,f154,f101,f318])).

fof(f101,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f154,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( v2_compts_1(X2,X0)
        | ~ v4_pre_topc(X2,X0)
        | ~ r1_tarski(X2,X1)
        | ~ v2_compts_1(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f165,plain,
    ( ! [X4,X2,X3] :
        ( ~ v4_pre_topc(X2,X3)
        | ~ r1_tarski(X2,X4)
        | ~ v2_compts_1(X4,X3)
        | v2_compts_1(X2,X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ r1_tarski(X2,u1_struct_0(X3)) )
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(resolution,[],[f155,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f155,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X2,X0)
        | ~ r1_tarski(X2,X1)
        | ~ v2_compts_1(X1,X0)
        | v2_compts_1(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f154])).

fof(f209,plain,
    ( ~ spl3_7
    | ~ spl3_27
    | spl3_8
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f139,f134,f84,f206,f79])).

fof(f84,plain,
    ( spl3_8
  <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f134,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f139,plain,
    ( ~ v2_compts_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8
    | ~ spl3_17 ),
    inference(superposition,[],[f86,f135])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f134])).

fof(f86,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f195,plain,
    ( spl3_24
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f157,f125,f113,f193])).

fof(f113,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f125,plain,
    ( spl3_16
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f157,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f127,f114])).

fof(f114,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f113])).

fof(f127,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f125])).

fof(f186,plain,
    ( spl3_23
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f145,f141,f79,f69,f59,f54,f49,f183])).

fof(f59,plain,
    ( spl3_3
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f69,plain,
    ( spl3_5
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f141,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | ~ v2_compts_1(X1,X0)
        | ~ v8_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f145,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f51,f56,f61,f71,f81,f142])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(X1,X0)
        | ~ v8_pre_topc(X0)
        | v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f71,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f61,plain,
    ( v8_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f178,plain,
    ( spl3_22
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f144,f141,f74,f64,f59,f54,f49,f175])).

fof(f144,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f51,f56,f61,f66,f76,f142])).

fof(f156,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f38,f154])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f152,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f47,f150])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tops_1)).

fof(f143,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f37,f141])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

fof(f136,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f46,f134])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f128,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f116,f97,f74,f125])).

fof(f97,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f116,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f76,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f115,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f45,f113])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f103,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f44,f101])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f99,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f43,f97])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f39,f89])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f87,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f36,f84])).

fof(f36,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f82,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f35,f69])).

fof(f35,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f33,f59])).

fof(f33,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f29,f49])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (17736)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (17732)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (17739)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (17733)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (17734)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (17735)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (17747)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (17740)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (17742)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (17743)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (17744)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (17735)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (17738)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f349,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f72,f77,f82,f87,f91,f99,f103,f115,f128,f136,f143,f152,f156,f178,f186,f195,f209,f320,f348])).
% 0.20/0.49  fof(f348,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_19 | ~spl3_22 | ~spl3_23 | ~spl3_24 | spl3_27 | ~spl3_38),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f347])).
% 0.20/0.49  fof(f347,plain,(
% 0.20/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_19 | ~spl3_22 | ~spl3_23 | ~spl3_24 | spl3_27 | ~spl3_38)),
% 0.20/0.49    inference(subsumption_resolution,[],[f190,f345])).
% 0.20/0.49  fof(f345,plain,(
% 0.20/0.49    ~v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_9 | ~spl3_24 | spl3_27 | ~spl3_38)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f56,f51,f66,f90,f76,f194,f208,f319])).
% 0.20/0.49  fof(f319,plain,(
% 0.20/0.49    ( ! [X4,X2,X3] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~r1_tarski(X2,X4) | ~v2_compts_1(X4,X3) | v2_compts_1(X2,X3) | ~v4_pre_topc(X2,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~r1_tarski(X2,u1_struct_0(X3))) ) | ~spl3_38),
% 0.20/0.49    inference(avatar_component_clause,[],[f318])).
% 0.20/0.49  fof(f318,plain,(
% 0.20/0.49    spl3_38 <=> ! [X3,X2,X4] : (~v4_pre_topc(X2,X3) | ~r1_tarski(X2,X4) | ~v2_compts_1(X4,X3) | v2_compts_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~r1_tarski(X2,u1_struct_0(X3)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.49  % (17731)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    ~v2_compts_1(k3_xboole_0(sK1,sK2),sK0) | spl3_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f206])).
% 0.20/0.49  fof(f206,plain,(
% 0.20/0.49    spl3_27 <=> v2_compts_1(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))) ) | ~spl3_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f193])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    spl3_24 <=> ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl3_9 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    v2_compts_1(sK1,sK0) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    spl3_4 <=> v2_compts_1(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    v2_pre_topc(sK0) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    spl3_1 <=> v2_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    l1_pre_topc(sK0) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl3_2 <=> l1_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_19 | ~spl3_22 | ~spl3_23)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f51,f56,f177,f76,f81,f185,f151])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f150])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    spl3_19 <=> ! [X1,X0,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    v4_pre_topc(sK2,sK0) | ~spl3_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f183])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    spl3_23 <=> v4_pre_topc(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    v4_pre_topc(sK1,sK0) | ~spl3_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f175])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    spl3_22 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.49  fof(f320,plain,(
% 0.20/0.49    spl3_38 | ~spl3_12 | ~spl3_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f165,f154,f101,f318])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    spl3_12 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    spl3_20 <=> ! [X1,X0,X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    ( ! [X4,X2,X3] : (~v4_pre_topc(X2,X3) | ~r1_tarski(X2,X4) | ~v2_compts_1(X4,X3) | v2_compts_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~r1_tarski(X2,u1_struct_0(X3))) ) | (~spl3_12 | ~spl3_20)),
% 0.20/0.49    inference(resolution,[],[f155,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f101])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | v2_compts_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f154])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    ~spl3_7 | ~spl3_27 | spl3_8 | ~spl3_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f139,f134,f84,f206,f79])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl3_8 <=> v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    spl3_17 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ~v2_compts_1(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_8 | ~spl3_17)),
% 0.20/0.49    inference(superposition,[],[f86,f135])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f134])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f84])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    spl3_24 | ~spl3_15 | ~spl3_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f157,f125,f113,f193])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    spl3_15 <=> ! [X1,X0,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    spl3_16 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))) ) | (~spl3_15 | ~spl3_16)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f127,f114])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) ) | ~spl3_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f113])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f125])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    spl3_23 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f145,f141,f79,f69,f59,f54,f49,f183])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    spl3_3 <=> v8_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl3_5 <=> v2_compts_1(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    spl3_18 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    v4_pre_topc(sK2,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_18)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f51,f56,f61,f71,f81,f142])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f141])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    v2_compts_1(sK2,sK0) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f69])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    v8_pre_topc(sK0) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f59])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    spl3_22 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f144,f141,f74,f64,f59,f54,f49,f175])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    v4_pre_topc(sK1,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_18)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f51,f56,f61,f66,f76,f142])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    spl3_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f154])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    spl3_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f47,f150])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k3_xboole_0(X1,X2),X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tops_1)).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    spl3_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f141])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    spl3_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f46,f134])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    spl3_16 | ~spl3_6 | ~spl3_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f116,f97,f74,f125])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    spl3_11 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | (~spl3_6 | ~spl3_11)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f76,f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f97])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl3_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f113])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    spl3_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f101])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    spl3_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f97])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f39,f89])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f84])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f11])).
% 0.20/0.49  fof(f11,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f79])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f74])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f69])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    v2_compts_1(sK2,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f34,f64])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    v2_compts_1(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f59])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    v8_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f54])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f29,f49])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (17735)------------------------------
% 0.20/0.49  % (17735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17735)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (17735)Memory used [KB]: 6396
% 0.20/0.49  % (17735)Time elapsed: 0.061 s
% 0.20/0.49  % (17735)------------------------------
% 0.20/0.49  % (17735)------------------------------
% 0.20/0.49  % (17746)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (17741)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (17729)Success in time 0.137 s
%------------------------------------------------------------------------------
