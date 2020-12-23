%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:06 EST 2020

% Result     : Theorem 3.55s
% Output     : Refutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 503 expanded)
%              Number of leaves         :   46 ( 216 expanded)
%              Depth                    :   13
%              Number of atoms          :  968 (2131 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1316,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f173,f250,f287,f296,f319,f365,f374,f375,f403,f452,f663,f833,f1015,f1056,f1062,f1085,f1109,f1125,f1305,f1315])).

fof(f1315,plain,
    ( ~ spl6_22
    | ~ spl6_24
    | spl6_43 ),
    inference(avatar_contradiction_clause,[],[f1314])).

fof(f1314,plain,
    ( $false
    | ~ spl6_22
    | ~ spl6_24
    | spl6_43 ),
    inference(subsumption_resolution,[],[f1313,f318])).

fof(f318,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl6_22
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f1313,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl6_24
    | spl6_43 ),
    inference(subsumption_resolution,[],[f1308,f331])).

fof(f331,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl6_24
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f1308,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,sK2)
    | spl6_43 ),
    inference(resolution,[],[f832,f99])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f832,plain,
    ( ~ r2_hidden(sK1,k3_xboole_0(sK2,sK3))
    | spl6_43 ),
    inference(avatar_component_clause,[],[f830])).

fof(f830,plain,
    ( spl6_43
  <=> r2_hidden(sK1,k3_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f1305,plain,
    ( ~ spl6_29
    | spl6_50 ),
    inference(avatar_contradiction_clause,[],[f1304])).

fof(f1304,plain,
    ( $false
    | ~ spl6_29
    | spl6_50 ),
    inference(subsumption_resolution,[],[f1292,f74])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1292,plain,
    ( ~ r1_tarski(k3_xboole_0(sK2,sK3),sK2)
    | ~ spl6_29
    | spl6_50 ),
    inference(resolution,[],[f1124,f632])).

fof(f632,plain,
    ( ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK2) )
    | ~ spl6_29 ),
    inference(resolution,[],[f402,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f402,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl6_29
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f1124,plain,
    ( ~ r1_tarski(k3_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | spl6_50 ),
    inference(avatar_component_clause,[],[f1122])).

fof(f1122,plain,
    ( spl6_50
  <=> r1_tarski(k3_xboole_0(sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f1125,plain,
    ( ~ spl6_50
    | spl6_42 ),
    inference(avatar_split_clause,[],[f1115,f826,f1122])).

fof(f826,plain,
    ( spl6_42
  <=> m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f1115,plain,
    ( ~ r1_tarski(k3_xboole_0(sK2,sK3),u1_struct_0(sK0))
    | spl6_42 ),
    inference(resolution,[],[f828,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f828,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_42 ),
    inference(avatar_component_clause,[],[f826])).

fof(f1109,plain,
    ( ~ spl6_5
    | ~ spl6_6
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_33
    | spl6_41 ),
    inference(avatar_contradiction_clause,[],[f1106])).

fof(f1106,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_33
    | spl6_41 ),
    inference(unit_resulting_resolution,[],[f127,f132,f345,f496,f824,f313,f354,f358])).

fof(f358,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X8)))
      | ~ v3_pre_topc(X7,X8)
      | v3_pre_topc(k3_xboole_0(X6,X7),X8)
      | ~ v3_pre_topc(X6,X8)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | ~ r1_tarski(X7,u1_struct_0(X8)) ) ),
    inference(resolution,[],[f72,f81])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

fof(f354,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl6_26
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f313,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl6_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f824,plain,
    ( ~ v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)
    | spl6_41 ),
    inference(avatar_component_clause,[],[f822])).

fof(f822,plain,
    ( spl6_41
  <=> v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f496,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl6_33
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f345,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl6_25
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f132,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1085,plain,
    ( spl6_25
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f1084,f312,f206,f135,f130,f125,f120,f343])).

fof(f120,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f135,plain,
    ( spl6_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f206,plain,
    ( spl6_16
  <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f1084,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f1083,f137])).

fof(f137,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f1083,plain,
    ( v3_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f1082,f132])).

fof(f1082,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f1081,f127])).

fof(f1081,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f1080,f122])).

fof(f122,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f1080,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f1073,f313])).

fof(f1073,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_16 ),
    inference(resolution,[],[f208,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f208,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f206])).

fof(f1062,plain,
    ( spl6_24
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f1061,f325,f200,f135,f130,f125,f120,f329])).

fof(f200,plain,
    ( spl6_15
  <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f325,plain,
    ( spl6_23
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f1061,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f1060,f137])).

fof(f1060,plain,
    ( r2_hidden(sK1,sK3)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f1059,f132])).

fof(f1059,plain,
    ( r2_hidden(sK1,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f1058,f127])).

fof(f1058,plain,
    ( r2_hidden(sK1,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f1057,f122])).

fof(f1057,plain,
    ( r2_hidden(sK1,sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f1045,f326])).

fof(f326,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f325])).

fof(f1045,plain,
    ( r2_hidden(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_15 ),
    inference(resolution,[],[f202,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f202,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f200])).

fof(f1056,plain,
    ( spl6_26
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f1055,f325,f200,f135,f130,f125,f120,f352])).

fof(f1055,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f1054,f137])).

fof(f1054,plain,
    ( v3_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f1053,f132])).

fof(f1053,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f1052,f127])).

fof(f1052,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f1051,f122])).

fof(f1051,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f1044,f326])).

fof(f1044,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_15 ),
    inference(resolution,[],[f202,f77])).

fof(f1015,plain,
    ( ~ spl6_12
    | spl6_1
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f1012,f223,f115,f105,f170])).

fof(f170,plain,
    ( spl6_12
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f105,plain,
    ( spl6_1
  <=> m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f115,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f223,plain,
    ( spl6_17
  <=> ! [X7,X6] :
        ( ~ r2_hidden(X6,X7)
        | ~ v1_xboole_0(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f1012,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_1
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f1007,f117])).

fof(f117,plain,
    ( m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f1007,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ v1_xboole_0(sK2)
    | spl6_1
    | ~ spl6_17 ),
    inference(superposition,[],[f107,f524])).

fof(f524,plain,
    ( ! [X6,X7] :
        ( k3_xboole_0(X6,X7) = X6
        | ~ v1_xboole_0(X6) )
    | ~ spl6_17 ),
    inference(resolution,[],[f255,f224])).

fof(f224,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,X7)
        | ~ v1_xboole_0(X7) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f223])).

fof(f255,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f107,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f833,plain,
    ( ~ spl6_41
    | ~ spl6_42
    | ~ spl6_43
    | spl6_1
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f820,f135,f130,f125,f105,f830,f826,f822])).

fof(f820,plain,
    ( ~ r2_hidden(sK1,k3_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)
    | spl6_1
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f819,f137])).

fof(f819,plain,
    ( ~ r2_hidden(sK1,k3_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)
    | spl6_1
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f818,f132])).

fof(f818,plain,
    ( ~ r2_hidden(sK1,k3_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)
    | spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f814,f127])).

fof(f814,plain,
    ( ~ r2_hidden(sK1,k3_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)
    | spl6_1 ),
    inference(resolution,[],[f381,f107])).

fof(f381,plain,(
    ! [X14,X15,X13] :
      ( m1_subset_1(X13,u1_struct_0(k9_yellow_6(X14,X15)))
      | ~ r2_hidden(X15,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ l1_pre_topc(X14)
      | ~ v2_pre_topc(X14)
      | v2_struct_0(X14)
      | ~ v3_pre_topc(X13,X14) ) ),
    inference(resolution,[],[f376,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f376,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f78,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f663,plain,
    ( spl6_33
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f662,f284,f135,f130,f125,f120,f494])).

fof(f284,plain,
    ( spl6_19
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f662,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f661,f137])).

fof(f661,plain,
    ( v2_struct_0(sK0)
    | r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f660,f132])).

fof(f660,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f659,f127])).

fof(f659,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl6_4
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f657,f122])).

fof(f657,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl6_19 ),
    inference(resolution,[],[f269,f286])).

fof(f286,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f284])).

fof(f269,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_connsp_2(X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | r1_tarski(X8,u1_struct_0(X9)) ) ),
    inference(resolution,[],[f83,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f452,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_19
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_19
    | spl6_23 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f286,f327,f83])).

fof(f327,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f325])).

fof(f403,plain,
    ( spl6_29
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f389,f312,f400])).

fof(f389,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl6_21 ),
    inference(resolution,[],[f313,f80])).

fof(f375,plain,
    ( spl6_10
    | spl6_15
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f187,f110,f200,f161])).

fof(f161,plain,
    ( spl6_10
  <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f110,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f187,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_2 ),
    inference(resolution,[],[f88,f112])).

fof(f112,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f374,plain,
    ( spl6_10
    | spl6_16
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f188,f115,f206,f161])).

fof(f188,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_3 ),
    inference(resolution,[],[f88,f117])).

fof(f365,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_20
    | spl6_21 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_20
    | spl6_21 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f295,f314,f83])).

fof(f314,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f312])).

fof(f295,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl6_20
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f319,plain,
    ( ~ spl6_21
    | spl6_22
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f310,f206,f135,f130,f125,f120,f316,f312])).

fof(f310,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f309,f137])).

fof(f309,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f308,f132])).

fof(f308,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f307,f127])).

fof(f307,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f302,f122])).

fof(f302,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_16 ),
    inference(resolution,[],[f76,f208])).

fof(f296,plain,
    ( spl6_20
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f291,f135,f130,f125,f120,f115,f293])).

fof(f291,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f290,f137])).

fof(f290,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f289,f132])).

fof(f289,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f288,f127])).

fof(f288,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f277,f122])).

fof(f277,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f75,f117])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f287,plain,
    ( spl6_19
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f282,f135,f130,f125,f120,f110,f284])).

fof(f282,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f281,f137])).

fof(f281,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f280,f132])).

fof(f280,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f279,f127])).

fof(f279,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f276,f122])).

fof(f276,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f75,f112])).

fof(f250,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f219,f223])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f84,f139])).

fof(f139,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f97,f96])).

fof(f96,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f173,plain,
    ( ~ spl6_10
    | spl6_12
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f148,f115,f170,f161])).

fof(f148,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_3 ),
    inference(resolution,[],[f90,f117])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f138,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f59,f135])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f42,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k3_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1)))
        & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1))) )
   => ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
      & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).

fof(f133,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f60,f130])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f128,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f61,f125])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f123,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f62,f120])).

fof(f62,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f118,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f63,f115])).

fof(f63,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f113,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f64,f110])).

fof(f64,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f65,f105])).

fof(f65,plain,(
    ~ m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:28:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (3567)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (3567)Refutation not found, incomplete strategy% (3567)------------------------------
% 0.21/0.51  % (3567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3567)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3567)Memory used [KB]: 10618
% 0.21/0.51  % (3567)Time elapsed: 0.092 s
% 0.21/0.51  % (3567)------------------------------
% 0.21/0.51  % (3567)------------------------------
% 0.21/0.52  % (3559)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (3574)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (3563)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.54  % (3558)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.54  % (3561)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.54  % (3560)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.54  % (3565)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.54  % (3571)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.54  % (3557)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.55  % (3578)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.55  % (3570)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.55  % (3581)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.55  % (3576)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.55  % (3585)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.55  % (3580)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.50/0.56  % (3575)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (3565)Refutation not found, incomplete strategy% (3565)------------------------------
% 1.50/0.56  % (3565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (3569)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.50/0.56  % (3577)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.56  % (3565)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (3565)Memory used [KB]: 10618
% 1.50/0.56  % (3565)Time elapsed: 0.133 s
% 1.50/0.56  % (3565)------------------------------
% 1.50/0.56  % (3565)------------------------------
% 1.50/0.56  % (3566)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.56  % (3582)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.56  % (3584)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.56  % (3566)Refutation not found, incomplete strategy% (3566)------------------------------
% 1.50/0.56  % (3566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (3566)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (3566)Memory used [KB]: 10618
% 1.50/0.56  % (3566)Time elapsed: 0.145 s
% 1.50/0.56  % (3566)------------------------------
% 1.50/0.56  % (3566)------------------------------
% 1.50/0.56  % (3556)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.50/0.56  % (3556)Refutation not found, incomplete strategy% (3556)------------------------------
% 1.50/0.56  % (3556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (3556)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (3556)Memory used [KB]: 1663
% 1.50/0.56  % (3556)Time elapsed: 0.139 s
% 1.50/0.56  % (3556)------------------------------
% 1.50/0.56  % (3556)------------------------------
% 1.50/0.57  % (3583)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.57  % (3579)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.50/0.57  % (3564)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.50/0.57  % (3572)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.57  % (3562)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.57  % (3568)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.58  % (3573)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.58  % (3573)Refutation not found, incomplete strategy% (3573)------------------------------
% 1.50/0.58  % (3573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (3573)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.58  
% 1.50/0.58  % (3573)Memory used [KB]: 10618
% 1.50/0.58  % (3573)Time elapsed: 0.163 s
% 1.50/0.58  % (3573)------------------------------
% 1.50/0.58  % (3573)------------------------------
% 2.00/0.64  % (3586)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.28/0.69  % (3587)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.28/0.71  % (3589)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.28/0.72  % (3590)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.28/0.73  % (3588)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.37/0.84  % (3561)Time limit reached!
% 3.37/0.84  % (3561)------------------------------
% 3.37/0.84  % (3561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.84  % (3561)Termination reason: Time limit
% 3.37/0.84  
% 3.37/0.84  % (3561)Memory used [KB]: 7675
% 3.37/0.84  % (3561)Time elapsed: 0.423 s
% 3.37/0.84  % (3561)------------------------------
% 3.37/0.84  % (3561)------------------------------
% 3.55/0.87  % (3588)Refutation found. Thanks to Tanya!
% 3.55/0.87  % SZS status Theorem for theBenchmark
% 3.55/0.87  % SZS output start Proof for theBenchmark
% 3.55/0.87  fof(f1316,plain,(
% 3.55/0.87    $false),
% 3.55/0.87    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f173,f250,f287,f296,f319,f365,f374,f375,f403,f452,f663,f833,f1015,f1056,f1062,f1085,f1109,f1125,f1305,f1315])).
% 3.55/0.87  fof(f1315,plain,(
% 3.55/0.87    ~spl6_22 | ~spl6_24 | spl6_43),
% 3.55/0.87    inference(avatar_contradiction_clause,[],[f1314])).
% 3.55/0.87  fof(f1314,plain,(
% 3.55/0.87    $false | (~spl6_22 | ~spl6_24 | spl6_43)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1313,f318])).
% 3.55/0.87  fof(f318,plain,(
% 3.55/0.87    r2_hidden(sK1,sK2) | ~spl6_22),
% 3.55/0.87    inference(avatar_component_clause,[],[f316])).
% 3.55/0.87  fof(f316,plain,(
% 3.55/0.87    spl6_22 <=> r2_hidden(sK1,sK2)),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 3.55/0.87  fof(f1313,plain,(
% 3.55/0.87    ~r2_hidden(sK1,sK2) | (~spl6_24 | spl6_43)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1308,f331])).
% 3.55/0.87  fof(f331,plain,(
% 3.55/0.87    r2_hidden(sK1,sK3) | ~spl6_24),
% 3.55/0.87    inference(avatar_component_clause,[],[f329])).
% 3.55/0.87  fof(f329,plain,(
% 3.55/0.87    spl6_24 <=> r2_hidden(sK1,sK3)),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 3.55/0.87  fof(f1308,plain,(
% 3.55/0.87    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,sK2) | spl6_43),
% 3.55/0.87    inference(resolution,[],[f832,f99])).
% 3.55/0.87  fof(f99,plain,(
% 3.55/0.87    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.55/0.87    inference(equality_resolution,[],[f68])).
% 3.55/0.87  fof(f68,plain,(
% 3.55/0.87    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.55/0.87    inference(cnf_transformation,[],[f48])).
% 3.55/0.87  fof(f48,plain,(
% 3.55/0.87    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.55/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 3.55/0.87  fof(f47,plain,(
% 3.55/0.87    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.55/0.87    introduced(choice_axiom,[])).
% 3.55/0.87  fof(f46,plain,(
% 3.55/0.87    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.55/0.87    inference(rectify,[],[f45])).
% 3.55/0.87  fof(f45,plain,(
% 3.55/0.87    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.55/0.87    inference(flattening,[],[f44])).
% 3.55/0.87  fof(f44,plain,(
% 3.55/0.87    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.55/0.87    inference(nnf_transformation,[],[f3])).
% 3.55/0.87  fof(f3,axiom,(
% 3.55/0.87    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 3.55/0.87  fof(f832,plain,(
% 3.55/0.87    ~r2_hidden(sK1,k3_xboole_0(sK2,sK3)) | spl6_43),
% 3.55/0.87    inference(avatar_component_clause,[],[f830])).
% 3.55/0.87  fof(f830,plain,(
% 3.55/0.87    spl6_43 <=> r2_hidden(sK1,k3_xboole_0(sK2,sK3))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 3.55/0.87  fof(f1305,plain,(
% 3.55/0.87    ~spl6_29 | spl6_50),
% 3.55/0.87    inference(avatar_contradiction_clause,[],[f1304])).
% 3.55/0.87  fof(f1304,plain,(
% 3.55/0.87    $false | (~spl6_29 | spl6_50)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1292,f74])).
% 3.55/0.87  fof(f74,plain,(
% 3.55/0.87    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f5])).
% 3.55/0.87  fof(f5,axiom,(
% 3.55/0.87    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.55/0.87  fof(f1292,plain,(
% 3.55/0.87    ~r1_tarski(k3_xboole_0(sK2,sK3),sK2) | (~spl6_29 | spl6_50)),
% 3.55/0.87    inference(resolution,[],[f1124,f632])).
% 3.55/0.87  fof(f632,plain,(
% 3.55/0.87    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK2)) ) | ~spl6_29),
% 3.55/0.87    inference(resolution,[],[f402,f98])).
% 3.55/0.87  fof(f98,plain,(
% 3.55/0.87    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f38])).
% 3.55/0.87  fof(f38,plain,(
% 3.55/0.87    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.55/0.87    inference(flattening,[],[f37])).
% 3.55/0.87  fof(f37,plain,(
% 3.55/0.87    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.55/0.87    inference(ennf_transformation,[],[f6])).
% 3.55/0.87  fof(f6,axiom,(
% 3.55/0.87    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.55/0.87  fof(f402,plain,(
% 3.55/0.87    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl6_29),
% 3.55/0.87    inference(avatar_component_clause,[],[f400])).
% 3.55/0.87  fof(f400,plain,(
% 3.55/0.87    spl6_29 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 3.55/0.87  fof(f1124,plain,(
% 3.55/0.87    ~r1_tarski(k3_xboole_0(sK2,sK3),u1_struct_0(sK0)) | spl6_50),
% 3.55/0.87    inference(avatar_component_clause,[],[f1122])).
% 3.55/0.87  fof(f1122,plain,(
% 3.55/0.87    spl6_50 <=> r1_tarski(k3_xboole_0(sK2,sK3),u1_struct_0(sK0))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 3.55/0.87  fof(f1125,plain,(
% 3.55/0.87    ~spl6_50 | spl6_42),
% 3.55/0.87    inference(avatar_split_clause,[],[f1115,f826,f1122])).
% 3.55/0.87  fof(f826,plain,(
% 3.55/0.87    spl6_42 <=> m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 3.55/0.87  fof(f1115,plain,(
% 3.55/0.87    ~r1_tarski(k3_xboole_0(sK2,sK3),u1_struct_0(sK0)) | spl6_42),
% 3.55/0.87    inference(resolution,[],[f828,f81])).
% 3.55/0.87  fof(f81,plain,(
% 3.55/0.87    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f51])).
% 3.55/0.87  fof(f51,plain,(
% 3.55/0.87    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.55/0.87    inference(nnf_transformation,[],[f12])).
% 3.55/0.87  fof(f12,axiom,(
% 3.55/0.87    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.55/0.87  fof(f828,plain,(
% 3.55/0.87    ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_42),
% 3.55/0.87    inference(avatar_component_clause,[],[f826])).
% 3.55/0.87  fof(f1109,plain,(
% 3.55/0.87    ~spl6_5 | ~spl6_6 | ~spl6_21 | ~spl6_25 | ~spl6_26 | ~spl6_33 | spl6_41),
% 3.55/0.87    inference(avatar_contradiction_clause,[],[f1106])).
% 3.55/0.87  fof(f1106,plain,(
% 3.55/0.87    $false | (~spl6_5 | ~spl6_6 | ~spl6_21 | ~spl6_25 | ~spl6_26 | ~spl6_33 | spl6_41)),
% 3.55/0.87    inference(unit_resulting_resolution,[],[f127,f132,f345,f496,f824,f313,f354,f358])).
% 3.55/0.87  fof(f358,plain,(
% 3.55/0.87    ( ! [X6,X8,X7] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X8))) | ~v3_pre_topc(X7,X8) | v3_pre_topc(k3_xboole_0(X6,X7),X8) | ~v3_pre_topc(X6,X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | ~r1_tarski(X7,u1_struct_0(X8))) )),
% 3.55/0.87    inference(resolution,[],[f72,f81])).
% 3.55/0.87  fof(f72,plain,(
% 3.55/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f24])).
% 3.55/0.87  fof(f24,plain,(
% 3.55/0.87    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.55/0.87    inference(flattening,[],[f23])).
% 3.55/0.87  fof(f23,plain,(
% 3.55/0.87    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.55/0.87    inference(ennf_transformation,[],[f15])).
% 3.55/0.87  fof(f15,axiom,(
% 3.55/0.87    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).
% 3.55/0.87  fof(f354,plain,(
% 3.55/0.87    v3_pre_topc(sK3,sK0) | ~spl6_26),
% 3.55/0.87    inference(avatar_component_clause,[],[f352])).
% 3.55/0.87  fof(f352,plain,(
% 3.55/0.87    spl6_26 <=> v3_pre_topc(sK3,sK0)),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 3.55/0.87  fof(f313,plain,(
% 3.55/0.87    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_21),
% 3.55/0.87    inference(avatar_component_clause,[],[f312])).
% 3.55/0.87  fof(f312,plain,(
% 3.55/0.87    spl6_21 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 3.55/0.87  fof(f824,plain,(
% 3.55/0.87    ~v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) | spl6_41),
% 3.55/0.87    inference(avatar_component_clause,[],[f822])).
% 3.55/0.87  fof(f822,plain,(
% 3.55/0.87    spl6_41 <=> v3_pre_topc(k3_xboole_0(sK2,sK3),sK0)),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 3.55/0.87  fof(f496,plain,(
% 3.55/0.87    r1_tarski(sK3,u1_struct_0(sK0)) | ~spl6_33),
% 3.55/0.87    inference(avatar_component_clause,[],[f494])).
% 3.55/0.87  fof(f494,plain,(
% 3.55/0.87    spl6_33 <=> r1_tarski(sK3,u1_struct_0(sK0))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 3.55/0.87  fof(f345,plain,(
% 3.55/0.87    v3_pre_topc(sK2,sK0) | ~spl6_25),
% 3.55/0.87    inference(avatar_component_clause,[],[f343])).
% 3.55/0.87  fof(f343,plain,(
% 3.55/0.87    spl6_25 <=> v3_pre_topc(sK2,sK0)),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 3.55/0.87  fof(f132,plain,(
% 3.55/0.87    v2_pre_topc(sK0) | ~spl6_6),
% 3.55/0.87    inference(avatar_component_clause,[],[f130])).
% 3.55/0.87  fof(f130,plain,(
% 3.55/0.87    spl6_6 <=> v2_pre_topc(sK0)),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 3.55/0.87  fof(f127,plain,(
% 3.55/0.87    l1_pre_topc(sK0) | ~spl6_5),
% 3.55/0.87    inference(avatar_component_clause,[],[f125])).
% 3.55/0.87  fof(f125,plain,(
% 3.55/0.87    spl6_5 <=> l1_pre_topc(sK0)),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 3.55/0.87  fof(f1085,plain,(
% 3.55/0.87    spl6_25 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_16 | ~spl6_21),
% 3.55/0.87    inference(avatar_split_clause,[],[f1084,f312,f206,f135,f130,f125,f120,f343])).
% 3.55/0.87  fof(f120,plain,(
% 3.55/0.87    spl6_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 3.55/0.87  fof(f135,plain,(
% 3.55/0.87    spl6_7 <=> v2_struct_0(sK0)),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 3.55/0.87  fof(f206,plain,(
% 3.55/0.87    spl6_16 <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 3.55/0.87  fof(f1084,plain,(
% 3.55/0.87    v3_pre_topc(sK2,sK0) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_16 | ~spl6_21)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1083,f137])).
% 3.55/0.87  fof(f137,plain,(
% 3.55/0.87    ~v2_struct_0(sK0) | spl6_7),
% 3.55/0.87    inference(avatar_component_clause,[],[f135])).
% 3.55/0.87  fof(f1083,plain,(
% 3.55/0.87    v3_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_16 | ~spl6_21)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1082,f132])).
% 3.55/0.87  fof(f1082,plain,(
% 3.55/0.87    v3_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_16 | ~spl6_21)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1081,f127])).
% 3.55/0.87  fof(f1081,plain,(
% 3.55/0.87    v3_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_16 | ~spl6_21)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1080,f122])).
% 3.55/0.87  fof(f122,plain,(
% 3.55/0.87    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_4),
% 3.55/0.87    inference(avatar_component_clause,[],[f120])).
% 3.55/0.87  fof(f1080,plain,(
% 3.55/0.87    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_16 | ~spl6_21)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1073,f313])).
% 3.55/0.87  fof(f1073,plain,(
% 3.55/0.87    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_16),
% 3.55/0.87    inference(resolution,[],[f208,f77])).
% 3.55/0.87  fof(f77,plain,(
% 3.55/0.87    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f50])).
% 3.55/0.87  fof(f50,plain,(
% 3.55/0.87    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/0.87    inference(flattening,[],[f49])).
% 3.55/0.87  fof(f49,plain,(
% 3.55/0.87    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/0.87    inference(nnf_transformation,[],[f28])).
% 3.55/0.87  fof(f28,plain,(
% 3.55/0.87    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/0.87    inference(flattening,[],[f27])).
% 3.55/0.87  fof(f27,plain,(
% 3.55/0.87    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/0.87    inference(ennf_transformation,[],[f17])).
% 3.55/0.87  fof(f17,axiom,(
% 3.55/0.87    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).
% 3.55/0.87  fof(f208,plain,(
% 3.55/0.87    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_16),
% 3.55/0.87    inference(avatar_component_clause,[],[f206])).
% 3.55/0.87  fof(f1062,plain,(
% 3.55/0.87    spl6_24 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_15 | ~spl6_23),
% 3.55/0.87    inference(avatar_split_clause,[],[f1061,f325,f200,f135,f130,f125,f120,f329])).
% 3.55/0.87  fof(f200,plain,(
% 3.55/0.87    spl6_15 <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 3.55/0.87  fof(f325,plain,(
% 3.55/0.87    spl6_23 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 3.55/0.87  fof(f1061,plain,(
% 3.55/0.87    r2_hidden(sK1,sK3) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_15 | ~spl6_23)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1060,f137])).
% 3.55/0.87  fof(f1060,plain,(
% 3.55/0.87    r2_hidden(sK1,sK3) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_15 | ~spl6_23)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1059,f132])).
% 3.55/0.87  fof(f1059,plain,(
% 3.55/0.87    r2_hidden(sK1,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_15 | ~spl6_23)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1058,f127])).
% 3.55/0.87  fof(f1058,plain,(
% 3.55/0.87    r2_hidden(sK1,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_15 | ~spl6_23)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1057,f122])).
% 3.55/0.87  fof(f1057,plain,(
% 3.55/0.87    r2_hidden(sK1,sK3) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_15 | ~spl6_23)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1045,f326])).
% 3.55/0.87  fof(f326,plain,(
% 3.55/0.87    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_23),
% 3.55/0.87    inference(avatar_component_clause,[],[f325])).
% 3.55/0.87  fof(f1045,plain,(
% 3.55/0.87    r2_hidden(sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_15),
% 3.55/0.87    inference(resolution,[],[f202,f76])).
% 3.55/0.87  fof(f76,plain,(
% 3.55/0.87    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f50])).
% 3.55/0.87  fof(f202,plain,(
% 3.55/0.87    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_15),
% 3.55/0.87    inference(avatar_component_clause,[],[f200])).
% 3.55/0.87  fof(f1056,plain,(
% 3.55/0.87    spl6_26 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_15 | ~spl6_23),
% 3.55/0.87    inference(avatar_split_clause,[],[f1055,f325,f200,f135,f130,f125,f120,f352])).
% 3.55/0.87  fof(f1055,plain,(
% 3.55/0.87    v3_pre_topc(sK3,sK0) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_15 | ~spl6_23)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1054,f137])).
% 3.55/0.87  fof(f1054,plain,(
% 3.55/0.87    v3_pre_topc(sK3,sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_15 | ~spl6_23)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1053,f132])).
% 3.55/0.87  fof(f1053,plain,(
% 3.55/0.87    v3_pre_topc(sK3,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_15 | ~spl6_23)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1052,f127])).
% 3.55/0.87  fof(f1052,plain,(
% 3.55/0.87    v3_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_15 | ~spl6_23)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1051,f122])).
% 3.55/0.87  fof(f1051,plain,(
% 3.55/0.87    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_15 | ~spl6_23)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1044,f326])).
% 3.55/0.87  fof(f1044,plain,(
% 3.55/0.87    v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_15),
% 3.55/0.87    inference(resolution,[],[f202,f77])).
% 3.55/0.87  fof(f1015,plain,(
% 3.55/0.87    ~spl6_12 | spl6_1 | ~spl6_3 | ~spl6_17),
% 3.55/0.87    inference(avatar_split_clause,[],[f1012,f223,f115,f105,f170])).
% 3.55/0.87  fof(f170,plain,(
% 3.55/0.87    spl6_12 <=> v1_xboole_0(sK2)),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 3.55/0.87  fof(f105,plain,(
% 3.55/0.87    spl6_1 <=> m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.55/0.87  fof(f115,plain,(
% 3.55/0.87    spl6_3 <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.55/0.87  fof(f223,plain,(
% 3.55/0.87    spl6_17 <=> ! [X7,X6] : (~r2_hidden(X6,X7) | ~v1_xboole_0(X7))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 3.55/0.87  fof(f1012,plain,(
% 3.55/0.87    ~v1_xboole_0(sK2) | (spl6_1 | ~spl6_3 | ~spl6_17)),
% 3.55/0.87    inference(subsumption_resolution,[],[f1007,f117])).
% 3.55/0.87  fof(f117,plain,(
% 3.55/0.87    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_3),
% 3.55/0.87    inference(avatar_component_clause,[],[f115])).
% 3.55/0.87  fof(f1007,plain,(
% 3.55/0.87    ~m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~v1_xboole_0(sK2) | (spl6_1 | ~spl6_17)),
% 3.55/0.87    inference(superposition,[],[f107,f524])).
% 3.55/0.87  fof(f524,plain,(
% 3.55/0.87    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = X6 | ~v1_xboole_0(X6)) ) | ~spl6_17),
% 3.55/0.87    inference(resolution,[],[f255,f224])).
% 3.55/0.87  fof(f224,plain,(
% 3.55/0.87    ( ! [X6,X7] : (~r2_hidden(X6,X7) | ~v1_xboole_0(X7)) ) | ~spl6_17),
% 3.55/0.87    inference(avatar_component_clause,[],[f223])).
% 3.55/0.87  fof(f255,plain,(
% 3.55/0.87    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) )),
% 3.55/0.87    inference(factoring,[],[f69])).
% 3.55/0.87  fof(f69,plain,(
% 3.55/0.87    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 3.55/0.87    inference(cnf_transformation,[],[f48])).
% 3.55/0.87  fof(f107,plain,(
% 3.55/0.87    ~m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_1),
% 3.55/0.87    inference(avatar_component_clause,[],[f105])).
% 3.55/0.87  fof(f833,plain,(
% 3.55/0.87    ~spl6_41 | ~spl6_42 | ~spl6_43 | spl6_1 | ~spl6_5 | ~spl6_6 | spl6_7),
% 3.55/0.87    inference(avatar_split_clause,[],[f820,f135,f130,f125,f105,f830,f826,f822])).
% 3.55/0.87  fof(f820,plain,(
% 3.55/0.87    ~r2_hidden(sK1,k3_xboole_0(sK2,sK3)) | ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) | (spl6_1 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 3.55/0.87    inference(subsumption_resolution,[],[f819,f137])).
% 3.55/0.87  fof(f819,plain,(
% 3.55/0.87    ~r2_hidden(sK1,k3_xboole_0(sK2,sK3)) | ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) | (spl6_1 | ~spl6_5 | ~spl6_6)),
% 3.55/0.87    inference(subsumption_resolution,[],[f818,f132])).
% 3.55/0.87  fof(f818,plain,(
% 3.55/0.87    ~r2_hidden(sK1,k3_xboole_0(sK2,sK3)) | ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) | (spl6_1 | ~spl6_5)),
% 3.55/0.87    inference(subsumption_resolution,[],[f814,f127])).
% 3.55/0.87  fof(f814,plain,(
% 3.55/0.87    ~r2_hidden(sK1,k3_xboole_0(sK2,sK3)) | ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(k3_xboole_0(sK2,sK3),sK0) | spl6_1),
% 3.55/0.87    inference(resolution,[],[f381,f107])).
% 3.55/0.87  fof(f381,plain,(
% 3.55/0.87    ( ! [X14,X15,X13] : (m1_subset_1(X13,u1_struct_0(k9_yellow_6(X14,X15))) | ~r2_hidden(X15,X13) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X14))) | ~l1_pre_topc(X14) | ~v2_pre_topc(X14) | v2_struct_0(X14) | ~v3_pre_topc(X13,X14)) )),
% 3.55/0.87    inference(resolution,[],[f376,f82])).
% 3.55/0.87  fof(f82,plain,(
% 3.55/0.87    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f31])).
% 3.55/0.87  fof(f31,plain,(
% 3.55/0.87    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.55/0.87    inference(ennf_transformation,[],[f11])).
% 3.55/0.87  fof(f11,axiom,(
% 3.55/0.87    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 3.55/0.87  fof(f376,plain,(
% 3.55/0.87    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.87    inference(subsumption_resolution,[],[f78,f79])).
% 3.55/0.87  fof(f79,plain,(
% 3.55/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f30])).
% 3.55/0.87  fof(f30,plain,(
% 3.55/0.87    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.55/0.87    inference(flattening,[],[f29])).
% 3.55/0.87  fof(f29,plain,(
% 3.55/0.87    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.55/0.87    inference(ennf_transformation,[],[f13])).
% 3.55/0.87  fof(f13,axiom,(
% 3.55/0.87    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 3.55/0.87  fof(f78,plain,(
% 3.55/0.87    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f50])).
% 3.55/0.87  fof(f663,plain,(
% 3.55/0.87    spl6_33 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_19),
% 3.55/0.87    inference(avatar_split_clause,[],[f662,f284,f135,f130,f125,f120,f494])).
% 3.55/0.87  fof(f284,plain,(
% 3.55/0.87    spl6_19 <=> m1_connsp_2(sK3,sK0,sK1)),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 3.55/0.87  fof(f662,plain,(
% 3.55/0.87    r1_tarski(sK3,u1_struct_0(sK0)) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_19)),
% 3.55/0.87    inference(subsumption_resolution,[],[f661,f137])).
% 3.55/0.87  fof(f661,plain,(
% 3.55/0.87    v2_struct_0(sK0) | r1_tarski(sK3,u1_struct_0(sK0)) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_19)),
% 3.55/0.87    inference(subsumption_resolution,[],[f660,f132])).
% 3.55/0.87  fof(f660,plain,(
% 3.55/0.87    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r1_tarski(sK3,u1_struct_0(sK0)) | (~spl6_4 | ~spl6_5 | ~spl6_19)),
% 3.55/0.87    inference(subsumption_resolution,[],[f659,f127])).
% 3.55/0.87  fof(f659,plain,(
% 3.55/0.87    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r1_tarski(sK3,u1_struct_0(sK0)) | (~spl6_4 | ~spl6_19)),
% 3.55/0.87    inference(subsumption_resolution,[],[f657,f122])).
% 3.55/0.87  fof(f657,plain,(
% 3.55/0.87    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r1_tarski(sK3,u1_struct_0(sK0)) | ~spl6_19),
% 3.55/0.87    inference(resolution,[],[f269,f286])).
% 3.55/0.87  fof(f286,plain,(
% 3.55/0.87    m1_connsp_2(sK3,sK0,sK1) | ~spl6_19),
% 3.55/0.87    inference(avatar_component_clause,[],[f284])).
% 3.55/0.87  fof(f269,plain,(
% 3.55/0.87    ( ! [X10,X8,X9] : (~m1_connsp_2(X8,X9,X10) | ~m1_subset_1(X10,u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9) | r1_tarski(X8,u1_struct_0(X9))) )),
% 3.55/0.87    inference(resolution,[],[f83,f80])).
% 3.55/0.87  fof(f80,plain,(
% 3.55/0.87    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f51])).
% 3.55/0.87  fof(f83,plain,(
% 3.55/0.87    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f33])).
% 3.55/0.87  fof(f33,plain,(
% 3.55/0.87    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/0.87    inference(flattening,[],[f32])).
% 3.55/0.87  fof(f32,plain,(
% 3.55/0.87    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/0.87    inference(ennf_transformation,[],[f16])).
% 3.55/0.87  fof(f16,axiom,(
% 3.55/0.87    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 3.55/0.87  fof(f452,plain,(
% 3.55/0.87    ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_19 | spl6_23),
% 3.55/0.87    inference(avatar_contradiction_clause,[],[f447])).
% 3.55/0.87  fof(f447,plain,(
% 3.55/0.87    $false | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_19 | spl6_23)),
% 3.55/0.87    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f286,f327,f83])).
% 3.55/0.87  fof(f327,plain,(
% 3.55/0.87    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_23),
% 3.55/0.87    inference(avatar_component_clause,[],[f325])).
% 3.55/0.87  fof(f403,plain,(
% 3.55/0.87    spl6_29 | ~spl6_21),
% 3.55/0.87    inference(avatar_split_clause,[],[f389,f312,f400])).
% 3.55/0.87  fof(f389,plain,(
% 3.55/0.87    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl6_21),
% 3.55/0.87    inference(resolution,[],[f313,f80])).
% 3.55/0.87  fof(f375,plain,(
% 3.55/0.87    spl6_10 | spl6_15 | ~spl6_2),
% 3.55/0.87    inference(avatar_split_clause,[],[f187,f110,f200,f161])).
% 3.55/0.87  fof(f161,plain,(
% 3.55/0.87    spl6_10 <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 3.55/0.87  fof(f110,plain,(
% 3.55/0.87    spl6_2 <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.55/0.87  fof(f187,plain,(
% 3.55/0.87    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_2),
% 3.55/0.87    inference(resolution,[],[f88,f112])).
% 3.55/0.87  fof(f112,plain,(
% 3.55/0.87    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_2),
% 3.55/0.87    inference(avatar_component_clause,[],[f110])).
% 3.55/0.87  fof(f88,plain,(
% 3.55/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f56])).
% 3.55/0.87  fof(f56,plain,(
% 3.55/0.87    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.55/0.87    inference(nnf_transformation,[],[f36])).
% 3.55/0.87  fof(f36,plain,(
% 3.55/0.87    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.55/0.87    inference(ennf_transformation,[],[f7])).
% 3.55/0.87  fof(f7,axiom,(
% 3.55/0.87    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 3.55/0.87  fof(f374,plain,(
% 3.55/0.87    spl6_10 | spl6_16 | ~spl6_3),
% 3.55/0.87    inference(avatar_split_clause,[],[f188,f115,f206,f161])).
% 3.55/0.87  fof(f188,plain,(
% 3.55/0.87    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_3),
% 3.55/0.87    inference(resolution,[],[f88,f117])).
% 3.55/0.87  fof(f365,plain,(
% 3.55/0.87    ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_20 | spl6_21),
% 3.55/0.87    inference(avatar_contradiction_clause,[],[f361])).
% 3.55/0.87  fof(f361,plain,(
% 3.55/0.87    $false | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_20 | spl6_21)),
% 3.55/0.87    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f295,f314,f83])).
% 3.55/0.87  fof(f314,plain,(
% 3.55/0.87    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_21),
% 3.55/0.87    inference(avatar_component_clause,[],[f312])).
% 3.55/0.87  fof(f295,plain,(
% 3.55/0.87    m1_connsp_2(sK2,sK0,sK1) | ~spl6_20),
% 3.55/0.87    inference(avatar_component_clause,[],[f293])).
% 3.55/0.87  fof(f293,plain,(
% 3.55/0.87    spl6_20 <=> m1_connsp_2(sK2,sK0,sK1)),
% 3.55/0.87    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 3.55/0.87  fof(f319,plain,(
% 3.55/0.87    ~spl6_21 | spl6_22 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_16),
% 3.55/0.87    inference(avatar_split_clause,[],[f310,f206,f135,f130,f125,f120,f316,f312])).
% 3.55/0.87  fof(f310,plain,(
% 3.55/0.87    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_16)),
% 3.55/0.87    inference(subsumption_resolution,[],[f309,f137])).
% 3.55/0.87  fof(f309,plain,(
% 3.55/0.87    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_16)),
% 3.55/0.87    inference(subsumption_resolution,[],[f308,f132])).
% 3.55/0.87  fof(f308,plain,(
% 3.55/0.87    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_16)),
% 3.55/0.87    inference(subsumption_resolution,[],[f307,f127])).
% 3.55/0.87  fof(f307,plain,(
% 3.55/0.87    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_16)),
% 3.55/0.87    inference(subsumption_resolution,[],[f302,f122])).
% 3.55/0.87  fof(f302,plain,(
% 3.55/0.87    r2_hidden(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_16),
% 3.55/0.87    inference(resolution,[],[f76,f208])).
% 3.55/0.87  fof(f296,plain,(
% 3.55/0.87    spl6_20 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7),
% 3.55/0.87    inference(avatar_split_clause,[],[f291,f135,f130,f125,f120,f115,f293])).
% 3.55/0.87  fof(f291,plain,(
% 3.55/0.87    m1_connsp_2(sK2,sK0,sK1) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 3.55/0.87    inference(subsumption_resolution,[],[f290,f137])).
% 3.55/0.87  fof(f290,plain,(
% 3.55/0.87    m1_connsp_2(sK2,sK0,sK1) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 3.55/0.87    inference(subsumption_resolution,[],[f289,f132])).
% 3.55/0.87  fof(f289,plain,(
% 3.55/0.87    m1_connsp_2(sK2,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_4 | ~spl6_5)),
% 3.55/0.87    inference(subsumption_resolution,[],[f288,f127])).
% 3.55/0.87  fof(f288,plain,(
% 3.55/0.87    m1_connsp_2(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_4)),
% 3.55/0.87    inference(subsumption_resolution,[],[f277,f122])).
% 3.55/0.87  fof(f277,plain,(
% 3.55/0.87    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_3),
% 3.55/0.87    inference(resolution,[],[f75,f117])).
% 3.55/0.87  fof(f75,plain,(
% 3.55/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f26])).
% 3.55/0.87  fof(f26,plain,(
% 3.55/0.87    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.55/0.87    inference(flattening,[],[f25])).
% 3.55/0.87  fof(f25,plain,(
% 3.55/0.87    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.55/0.87    inference(ennf_transformation,[],[f18])).
% 3.55/0.87  fof(f18,axiom,(
% 3.55/0.87    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).
% 3.55/0.87  fof(f287,plain,(
% 3.55/0.87    spl6_19 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7),
% 3.55/0.87    inference(avatar_split_clause,[],[f282,f135,f130,f125,f120,f110,f284])).
% 3.55/0.87  fof(f282,plain,(
% 3.55/0.87    m1_connsp_2(sK3,sK0,sK1) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 3.55/0.87    inference(subsumption_resolution,[],[f281,f137])).
% 3.55/0.87  fof(f281,plain,(
% 3.55/0.87    m1_connsp_2(sK3,sK0,sK1) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 3.55/0.87    inference(subsumption_resolution,[],[f280,f132])).
% 3.55/0.87  fof(f280,plain,(
% 3.55/0.87    m1_connsp_2(sK3,sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_4 | ~spl6_5)),
% 3.55/0.87    inference(subsumption_resolution,[],[f279,f127])).
% 3.55/0.87  fof(f279,plain,(
% 3.55/0.87    m1_connsp_2(sK3,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_4)),
% 3.55/0.87    inference(subsumption_resolution,[],[f276,f122])).
% 3.55/0.87  fof(f276,plain,(
% 3.55/0.87    m1_connsp_2(sK3,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_2),
% 3.55/0.87    inference(resolution,[],[f75,f112])).
% 3.55/0.87  fof(f250,plain,(
% 3.55/0.87    spl6_17),
% 3.55/0.87    inference(avatar_split_clause,[],[f219,f223])).
% 3.55/0.87  fof(f219,plain,(
% 3.55/0.87    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 3.55/0.87    inference(resolution,[],[f84,f139])).
% 3.55/0.87  fof(f139,plain,(
% 3.55/0.87    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 3.55/0.87    inference(forward_demodulation,[],[f97,f96])).
% 3.55/0.87  fof(f96,plain,(
% 3.55/0.87    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.55/0.87    inference(cnf_transformation,[],[f8])).
% 3.55/0.87  fof(f8,axiom,(
% 3.55/0.87    ! [X0] : k2_subset_1(X0) = X0),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 3.55/0.87  fof(f97,plain,(
% 3.55/0.87    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.55/0.87    inference(cnf_transformation,[],[f9])).
% 3.55/0.87  fof(f9,axiom,(
% 3.55/0.87    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 3.55/0.87  fof(f84,plain,(
% 3.55/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f34])).
% 3.55/0.87  fof(f34,plain,(
% 3.55/0.87    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.55/0.87    inference(ennf_transformation,[],[f14])).
% 3.55/0.87  fof(f14,axiom,(
% 3.55/0.87    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.55/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 3.55/0.87  fof(f173,plain,(
% 3.55/0.87    ~spl6_10 | spl6_12 | ~spl6_3),
% 3.55/0.87    inference(avatar_split_clause,[],[f148,f115,f170,f161])).
% 3.55/0.87  fof(f148,plain,(
% 3.55/0.87    v1_xboole_0(sK2) | ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_3),
% 3.55/0.87    inference(resolution,[],[f90,f117])).
% 3.55/0.87  fof(f90,plain,(
% 3.55/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 3.55/0.87    inference(cnf_transformation,[],[f56])).
% 3.55/0.88  fof(f138,plain,(
% 3.55/0.88    ~spl6_7),
% 3.55/0.88    inference(avatar_split_clause,[],[f59,f135])).
% 3.55/0.88  fof(f59,plain,(
% 3.55/0.88    ~v2_struct_0(sK0)),
% 3.55/0.88    inference(cnf_transformation,[],[f43])).
% 3.55/0.88  fof(f43,plain,(
% 3.55/0.88    (((~m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.55/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f42,f41,f40,f39])).
% 3.55/0.88  fof(f39,plain,(
% 3.55/0.88    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.55/0.88    introduced(choice_axiom,[])).
% 3.55/0.88  fof(f40,plain,(
% 3.55/0.88    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 3.55/0.88    introduced(choice_axiom,[])).
% 3.55/0.88  fof(f41,plain,(
% 3.55/0.88    ? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) & m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 3.55/0.88    introduced(choice_axiom,[])).
% 3.55/0.88  fof(f42,plain,(
% 3.55/0.88    ? [X3] : (~m1_subset_1(k3_xboole_0(sK2,X3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK0,sK1)))) => (~m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) & m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))))),
% 3.55/0.88    introduced(choice_axiom,[])).
% 3.55/0.88  fof(f22,plain,(
% 3.55/0.88    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.55/0.88    inference(flattening,[],[f21])).
% 3.55/0.88  fof(f21,plain,(
% 3.55/0.88    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.55/0.88    inference(ennf_transformation,[],[f20])).
% 3.55/0.88  fof(f20,negated_conjecture,(
% 3.55/0.88    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.55/0.88    inference(negated_conjecture,[],[f19])).
% 3.55/0.88  fof(f19,conjecture,(
% 3.55/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.55/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).
% 3.55/0.88  fof(f133,plain,(
% 3.55/0.88    spl6_6),
% 3.55/0.88    inference(avatar_split_clause,[],[f60,f130])).
% 3.55/0.88  fof(f60,plain,(
% 3.55/0.88    v2_pre_topc(sK0)),
% 3.55/0.88    inference(cnf_transformation,[],[f43])).
% 3.55/0.88  fof(f128,plain,(
% 3.55/0.88    spl6_5),
% 3.55/0.88    inference(avatar_split_clause,[],[f61,f125])).
% 3.55/0.88  fof(f61,plain,(
% 3.55/0.88    l1_pre_topc(sK0)),
% 3.55/0.88    inference(cnf_transformation,[],[f43])).
% 3.55/0.88  fof(f123,plain,(
% 3.55/0.88    spl6_4),
% 3.55/0.88    inference(avatar_split_clause,[],[f62,f120])).
% 3.55/0.88  fof(f62,plain,(
% 3.55/0.88    m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.55/0.88    inference(cnf_transformation,[],[f43])).
% 3.55/0.88  fof(f118,plain,(
% 3.55/0.88    spl6_3),
% 3.55/0.88    inference(avatar_split_clause,[],[f63,f115])).
% 3.55/0.88  fof(f63,plain,(
% 3.55/0.88    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.55/0.88    inference(cnf_transformation,[],[f43])).
% 3.55/0.88  fof(f113,plain,(
% 3.55/0.88    spl6_2),
% 3.55/0.88    inference(avatar_split_clause,[],[f64,f110])).
% 3.55/0.88  fof(f64,plain,(
% 3.55/0.88    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.55/0.88    inference(cnf_transformation,[],[f43])).
% 3.55/0.88  fof(f108,plain,(
% 3.55/0.88    ~spl6_1),
% 3.55/0.88    inference(avatar_split_clause,[],[f65,f105])).
% 3.55/0.88  fof(f65,plain,(
% 3.55/0.88    ~m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.55/0.88    inference(cnf_transformation,[],[f43])).
% 3.55/0.88  % SZS output end Proof for theBenchmark
% 3.55/0.88  % (3588)------------------------------
% 3.55/0.88  % (3588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.88  % (3588)Termination reason: Refutation
% 3.55/0.88  
% 3.55/0.88  % (3588)Memory used [KB]: 7036
% 3.55/0.88  % (3588)Time elapsed: 0.279 s
% 3.55/0.88  % (3588)------------------------------
% 3.55/0.88  % (3588)------------------------------
% 3.55/0.88  % (3555)Success in time 0.512 s
%------------------------------------------------------------------------------
