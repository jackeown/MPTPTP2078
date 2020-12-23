%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 256 expanded)
%              Number of leaves         :   28 ( 121 expanded)
%              Depth                    :    8
%              Number of atoms          :  443 ( 996 expanded)
%              Number of equality atoms :   19 (  63 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f87,f92,f101,f108,f118,f129,f134,f142,f147,f152,f157,f163,f177,f181,f186,f207])).

fof(f207,plain,
    ( ~ spl6_16
    | spl6_19 ),
    inference(avatar_split_clause,[],[f206,f174,f160])).

fof(f160,plain,
    ( spl6_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f174,plain,
    ( spl6_19
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f206,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_19 ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_19 ),
    inference(resolution,[],[f191,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_subset_1)).

% (20050)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f191,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k8_subset_1(X0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) )
    | spl6_19 ),
    inference(superposition,[],[f176,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k8_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

fof(f176,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f174])).

fof(f186,plain,
    ( ~ spl6_10
    | ~ spl6_12
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_12
    | spl6_18 ),
    inference(unit_resulting_resolution,[],[f141,f128,f172,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f39])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f172,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl6_18
  <=> r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f128,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_10
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f141,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl6_12
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f181,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f71,f76,f151,f146,f156,f162,f168,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

fof(f168,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl6_17
  <=> v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f162,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f156,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f146,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_13
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f151,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_14
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f76,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f71,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f177,plain,
    ( spl6_1
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | spl6_8 ),
    inference(avatar_split_clause,[],[f109,f105,f69,f74,f79,f174,f170,f166,f64])).

fof(f64,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f79,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f105,plain,
    ( spl6_8
  <=> r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f109,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)
    | v2_struct_0(sK0)
    | spl6_8 ),
    inference(resolution,[],[f107,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ v3_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f107,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f163,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | spl6_16
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f135,f131,f160,f69,f74,f79,f89,f64])).

fof(f89,plain,
    ( spl6_6
  <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f131,plain,
    ( spl6_11
  <=> sK2 = sK4(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f135,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_11 ),
    inference(superposition,[],[f35,f133])).

fof(f133,plain,
    ( sK2 = sK4(sK0,sK1,sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

fof(f157,plain,
    ( spl6_1
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | spl6_15
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f119,f115,f154,f69,f74,f79,f84,f64])).

fof(f84,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f115,plain,
    ( spl6_9
  <=> sK3 = sK4(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f119,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_9 ),
    inference(superposition,[],[f35,f117])).

fof(f117,plain,
    ( sK3 = sK4(sK0,sK1,sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f152,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | spl6_14
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f136,f131,f149,f69,f74,f79,f89,f64])).

fof(f136,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_11 ),
    inference(superposition,[],[f38,f133])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f147,plain,
    ( spl6_1
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | spl6_13
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f120,f115,f144,f69,f74,f79,f84,f64])).

fof(f120,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_9 ),
    inference(superposition,[],[f38,f117])).

fof(f142,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | spl6_12
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f137,f131,f89,f139,f69,f74,f79,f64])).

fof(f137,plain,
    ( r2_hidden(sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f96,f133])).

fof(f96,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,sK4(sK0,sK1,sK2))
    | ~ spl6_6 ),
    inference(resolution,[],[f91,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,
    ( m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f134,plain,
    ( spl6_11
    | spl6_1
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f95,f89,f69,f74,f79,f64,f131])).

fof(f95,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK2 = sK4(sK0,sK1,sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f91,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | sK4(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f129,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | spl6_10
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f124,f115,f84,f126,f69,f74,f79,f64])).

fof(f124,plain,
    ( r2_hidden(sK1,sK3)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f94,f117])).

fof(f94,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,sK4(sK0,sK1,sK3))
    | ~ spl6_5 ),
    inference(resolution,[],[f86,f37])).

fof(f86,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f118,plain,
    ( spl6_9
    | spl6_1
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f93,f84,f69,f74,f79,f64,f115])).

fof(f93,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK3 = sK4(sK0,sK1,sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f86,f36])).

fof(f108,plain,
    ( ~ spl6_8
    | spl6_7 ),
    inference(avatar_split_clause,[],[f102,f98,f105])).

fof(f98,plain,
    ( spl6_7
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

% (20048)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f102,plain,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_7 ),
    inference(resolution,[],[f100,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f100,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f101,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f51,f98])).

fof(f51,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(definition_unfolding,[],[f26,f39])).

fof(f26,plain,(
    ~ m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f92,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f27,f89])).

fof(f27,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f87,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f25,f84])).

fof(f25,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f28,f79])).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (20051)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (20070)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (20053)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (20062)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (20070)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (20060)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (20049)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f87,f92,f101,f108,f118,f129,f134,f142,f147,f152,f157,f163,f177,f181,f186,f207])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    ~spl6_16 | spl6_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f206,f174,f160])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    spl6_16 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    spl6_19 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_19),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f202])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_19),
% 0.22/0.53    inference(resolution,[],[f191,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k8_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_subset_1)).
% 0.22/0.53  % (20050)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(k8_subset_1(X0,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | spl6_19),
% 0.22/0.53    inference(superposition,[],[f176,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k8_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f42,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_subset_1)).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f174])).
% 0.22/0.53  fof(f186,plain,(
% 0.22/0.53    ~spl6_10 | ~spl6_12 | spl6_18),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f183])).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    $false | (~spl6_10 | ~spl6_12 | spl6_18)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f141,f128,f172,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 0.22/0.53    inference(definition_unfolding,[],[f50,f39])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    ~r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) | spl6_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f170])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    spl6_18 <=> r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    r2_hidden(sK1,sK3) | ~spl6_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f126])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    spl6_10 <=> r2_hidden(sK1,sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    r2_hidden(sK1,sK2) | ~spl6_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f139])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    spl6_12 <=> r2_hidden(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ~spl6_2 | ~spl6_3 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_17),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    $false | (~spl6_2 | ~spl6_3 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_17)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f71,f76,f151,f146,f156,f162,f168,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f43,f39])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_xboole_0(X1,X2),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    ~v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) | spl6_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f166])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    spl6_17 <=> v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f160])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f154])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    spl6_15 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    v3_pre_topc(sK3,sK0) | ~spl6_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f144])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    spl6_13 <=> v3_pre_topc(sK3,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    v3_pre_topc(sK2,sK0) | ~spl6_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f149])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    spl6_14 <=> v3_pre_topc(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    l1_pre_topc(sK0) | ~spl6_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl6_3 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    v2_pre_topc(sK0) | ~spl6_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    spl6_2 <=> v2_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    spl6_1 | ~spl6_17 | ~spl6_18 | ~spl6_19 | ~spl6_4 | ~spl6_3 | ~spl6_2 | spl6_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f109,f105,f69,f74,f79,f174,f170,f166,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    spl6_1 <=> v2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl6_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl6_8 <=> r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) | ~v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) | v2_struct_0(sK0) | spl6_8),
% 0.22/0.53    inference(resolution,[],[f107,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ~r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f105])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    spl6_1 | ~spl6_6 | ~spl6_4 | ~spl6_3 | ~spl6_2 | spl6_16 | ~spl6_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f135,f131,f160,f69,f74,f79,f89,f64])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl6_6 <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    spl6_11 <=> sK2 = sK4(sK0,sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | v2_struct_0(sK0) | ~spl6_11),
% 0.22/0.53    inference(superposition,[],[f35,f133])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    sK2 = sK4(sK0,sK1,sK2) | ~spl6_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f131])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    spl6_1 | ~spl6_5 | ~spl6_4 | ~spl6_3 | ~spl6_2 | spl6_15 | ~spl6_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f119,f115,f154,f69,f74,f79,f84,f64])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    spl6_5 <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    spl6_9 <=> sK3 = sK4(sK0,sK1,sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | v2_struct_0(sK0) | ~spl6_9),
% 0.22/0.53    inference(superposition,[],[f35,f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    sK3 = sK4(sK0,sK1,sK3) | ~spl6_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f115])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    spl6_1 | ~spl6_6 | ~spl6_4 | ~spl6_3 | ~spl6_2 | spl6_14 | ~spl6_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f136,f131,f149,f69,f74,f79,f89,f64])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    v3_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | v2_struct_0(sK0) | ~spl6_11),
% 0.22/0.53    inference(superposition,[],[f38,f133])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v3_pre_topc(sK4(X0,X1,X2),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    spl6_1 | ~spl6_5 | ~spl6_4 | ~spl6_3 | ~spl6_2 | spl6_13 | ~spl6_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f120,f115,f144,f69,f74,f79,f84,f64])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    v3_pre_topc(sK3,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | v2_struct_0(sK0) | ~spl6_9),
% 0.22/0.53    inference(superposition,[],[f38,f117])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    spl6_1 | ~spl6_4 | ~spl6_3 | ~spl6_2 | spl6_12 | ~spl6_6 | ~spl6_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f137,f131,f89,f139,f69,f74,f79,f64])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    r2_hidden(sK1,sK2) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_11)),
% 0.22/0.53    inference(forward_demodulation,[],[f96,f133])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,sK4(sK0,sK1,sK2)) | ~spl6_6),
% 0.22/0.53    inference(resolution,[],[f91,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,sK4(X0,X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    spl6_11 | spl6_1 | ~spl6_4 | ~spl6_3 | ~spl6_2 | ~spl6_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f95,f89,f69,f74,f79,f64,f131])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | sK2 = sK4(sK0,sK1,sK2) | ~spl6_6),
% 0.22/0.53    inference(resolution,[],[f91,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | sK4(X0,X1,X2) = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    spl6_1 | ~spl6_4 | ~spl6_3 | ~spl6_2 | spl6_10 | ~spl6_5 | ~spl6_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f124,f115,f84,f126,f69,f74,f79,f64])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    r2_hidden(sK1,sK3) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_9)),
% 0.22/0.53    inference(forward_demodulation,[],[f94,f117])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,sK4(sK0,sK1,sK3)) | ~spl6_5),
% 0.22/0.53    inference(resolution,[],[f86,f37])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f84])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    spl6_9 | spl6_1 | ~spl6_4 | ~spl6_3 | ~spl6_2 | ~spl6_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f93,f84,f69,f74,f79,f64,f115])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | sK3 = sK4(sK0,sK1,sK3) | ~spl6_5),
% 0.22/0.53    inference(resolution,[],[f86,f36])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ~spl6_8 | spl6_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f102,f98,f105])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    spl6_7 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.53  % (20048)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ~r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_7),
% 0.22/0.53    inference(resolution,[],[f100,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f98])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ~spl6_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f51,f98])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    inference(definition_unfolding,[],[f26,f39])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ~m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f10])).
% 0.22/0.53  fof(f10,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    spl6_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f89])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl6_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f25,f84])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f79])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f74])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    spl6_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f69])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ~spl6_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f64])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (20070)------------------------------
% 0.22/0.53  % (20070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20070)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (20070)Memory used [KB]: 10874
% 0.22/0.53  % (20070)Time elapsed: 0.114 s
% 0.22/0.53  % (20070)------------------------------
% 0.22/0.53  % (20070)------------------------------
% 0.22/0.54  % (20047)Success in time 0.167 s
%------------------------------------------------------------------------------
