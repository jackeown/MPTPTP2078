%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 161 expanded)
%              Number of leaves         :   28 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  286 ( 460 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f91,f104,f110,f119,f138,f151,f166,f173,f177,f277,f444])).

fof(f444,plain,
    ( ~ spl5_1
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_29 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f65,f118,f41,f94,f40,f276,f165,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f165,plain,
    ( m1_subset_1(k1_tarski(sK3(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl5_16
  <=> m1_subset_1(k1_tarski(sK3(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f276,plain,
    ( v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl5_29
  <=> v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f57,f42])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f57,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

% (26753)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f118,plain,
    ( v3_tex_2(k1_xboole_0,sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f116])).

% (26755)Refutation not found, incomplete strategy% (26755)------------------------------
% (26755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26755)Termination reason: Refutation not found, incomplete strategy

% (26755)Memory used [KB]: 10618
% (26755)Time elapsed: 0.113 s
% (26755)------------------------------
% (26755)------------------------------
fof(f116,plain,
    ( spl5_10
  <=> v3_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f65,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f277,plain,
    ( spl5_3
    | ~ spl5_15
    | ~ spl5_1
    | ~ spl5_2
    | spl5_29
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f271,f135,f274,f68,f63,f159,f73])).

fof(f73,plain,
    ( spl5_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f159,plain,
    ( spl5_15
  <=> m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f68,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f135,plain,
    ( spl5_12
  <=> k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f271,plain,
    ( v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl5_12 ),
    inference(superposition,[],[f50,f137])).

fof(f137,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f177,plain,
    ( spl5_7
    | spl5_17 ),
    inference(avatar_split_clause,[],[f175,f170,f97])).

fof(f97,plain,
    ( spl5_7
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f170,plain,
    ( spl5_17
  <=> r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f175,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | spl5_17 ),
    inference(resolution,[],[f172,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f172,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f173,plain,
    ( ~ spl5_17
    | spl5_15 ),
    inference(avatar_split_clause,[],[f168,f159,f170])).

fof(f168,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl5_15 ),
    inference(resolution,[],[f161,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f161,plain,
    ( ~ m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f166,plain,
    ( spl5_7
    | ~ spl5_15
    | spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f157,f135,f163,f159,f97])).

fof(f157,plain,
    ( m1_subset_1(k1_tarski(sK3(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(superposition,[],[f60,f137])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f151,plain,
    ( ~ spl5_1
    | spl5_8 ),
    inference(avatar_split_clause,[],[f149,f101,f63])).

fof(f101,plain,
    ( spl5_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f149,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_8 ),
    inference(resolution,[],[f103,f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f103,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f138,plain,
    ( spl5_7
    | spl5_12
    | spl5_7 ),
    inference(avatar_split_clause,[],[f132,f97,f135,f97])).

fof(f132,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl5_7 ),
    inference(resolution,[],[f131,f52])).

fof(f131,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK0))
        | k6_domain_1(u1_struct_0(sK0),X2) = k1_tarski(X2) )
    | spl5_7 ),
    inference(resolution,[],[f129,f58])).

fof(f129,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k6_domain_1(u1_struct_0(sK0),X3) = k1_tarski(X3) )
    | spl5_7 ),
    inference(resolution,[],[f59,f99])).

fof(f99,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f119,plain,
    ( spl5_10
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f112,f107,f78,f116])).

fof(f78,plain,
    ( spl5_4
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f107,plain,
    ( spl5_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f112,plain,
    ( v3_tex_2(k1_xboole_0,sK0)
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f80,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f80,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f110,plain,
    ( spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f105,f88,f107])).

fof(f88,plain,
    ( spl5_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f105,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_6 ),
    inference(resolution,[],[f56,f92])).

fof(f92,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f53,f90])).

fof(f90,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f104,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | spl5_3 ),
    inference(avatar_split_clause,[],[f95,f73,f101,f97])).

fof(f95,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_3 ),
    inference(resolution,[],[f51,f75])).

fof(f75,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f51,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f91,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

% (26770)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(f81,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f36,f78])).

fof(f36,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f37,f73])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f38,f68])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f39,f63])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (26746)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.48  % (26766)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.49  % (26764)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.49  % (26749)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (26754)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (26748)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (26768)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % (26750)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (26750)Refutation not found, incomplete strategy% (26750)------------------------------
% 0.21/0.50  % (26750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26750)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26750)Memory used [KB]: 10618
% 0.21/0.50  % (26750)Time elapsed: 0.088 s
% 0.21/0.50  % (26750)------------------------------
% 0.21/0.50  % (26750)------------------------------
% 0.21/0.50  % (26767)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (26759)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (26745)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (26762)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.50  % (26747)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (26752)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (26769)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (26758)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (26751)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (26760)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (26759)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (26765)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (26757)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (26755)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (26757)Refutation not found, incomplete strategy% (26757)------------------------------
% 0.21/0.51  % (26757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26757)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26757)Memory used [KB]: 6140
% 0.21/0.51  % (26757)Time elapsed: 0.113 s
% 0.21/0.51  % (26757)------------------------------
% 0.21/0.51  % (26757)------------------------------
% 0.21/0.51  % (26756)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f445,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f91,f104,f110,f119,f138,f151,f166,f173,f177,f277,f444])).
% 0.21/0.52  fof(f444,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_10 | ~spl5_16 | ~spl5_29),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f443])).
% 0.21/0.52  fof(f443,plain,(
% 0.21/0.52    $false | (~spl5_1 | ~spl5_10 | ~spl5_16 | ~spl5_29)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f65,f118,f41,f94,f40,f276,f165,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X2,X0) | ~r1_tarski(X1,X2) | X1 = X2 | ~v3_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    m1_subset_1(k1_tarski(sK3(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f163])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl5_16 <=> m1_subset_1(k1_tarski(sK3(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0) | ~spl5_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f274])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    spl5_29 <=> v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.21/0.52    inference(superposition,[],[f57,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.52  % (26753)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    v3_tex_2(k1_xboole_0,sK0) | ~spl5_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f116])).
% 0.21/0.52  % (26755)Refutation not found, incomplete strategy% (26755)------------------------------
% 0.21/0.52  % (26755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26755)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26755)Memory used [KB]: 10618
% 0.21/0.52  % (26755)Time elapsed: 0.113 s
% 0.21/0.52  % (26755)------------------------------
% 0.21/0.52  % (26755)------------------------------
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl5_10 <=> v3_tex_2(k1_xboole_0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    l1_pre_topc(sK0) | ~spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl5_1 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f277,plain,(
% 0.21/0.52    spl5_3 | ~spl5_15 | ~spl5_1 | ~spl5_2 | spl5_29 | ~spl5_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f271,f135,f274,f68,f63,f159,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl5_3 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    spl5_15 <=> m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl5_2 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    spl5_12 <=> k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.52  fof(f271,plain,(
% 0.21/0.52    v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl5_12),
% 0.21/0.52    inference(superposition,[],[f50,f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0))) | ~spl5_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f135])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    spl5_7 | spl5_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f175,f170,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl5_7 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl5_17 <=> r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    v1_xboole_0(u1_struct_0(sK0)) | spl5_17),
% 0.21/0.52    inference(resolution,[],[f172,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    ~r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) | spl5_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f170])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ~spl5_17 | spl5_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f168,f159,f170])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    ~r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) | spl5_15),
% 0.21/0.52    inference(resolution,[],[f161,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) | spl5_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f159])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    spl5_7 | ~spl5_15 | spl5_16 | ~spl5_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f157,f135,f163,f159,f97])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    m1_subset_1(k1_tarski(sK3(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_12),
% 0.21/0.52    inference(superposition,[],[f60,f137])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ~spl5_1 | spl5_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f149,f101,f63])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl5_8 <=> l1_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | spl5_8),
% 0.21/0.52    inference(resolution,[],[f103,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ~l1_struct_0(sK0) | spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f101])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    spl5_7 | spl5_12 | spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f132,f97,f135,f97])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | spl5_7),
% 0.21/0.52    inference(resolution,[],[f131,f52])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),X2) = k1_tarski(X2)) ) | spl5_7),
% 0.21/0.52    inference(resolution,[],[f129,f58])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),X3) = k1_tarski(X3)) ) | spl5_7),
% 0.21/0.52    inference(resolution,[],[f59,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f97])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    spl5_10 | ~spl5_4 | ~spl5_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f112,f107,f78,f116])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl5_4 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    spl5_9 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    v3_tex_2(k1_xboole_0,sK0) | (~spl5_4 | ~spl5_9)),
% 0.21/0.52    inference(backward_demodulation,[],[f80,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f107])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    v3_tex_2(sK1,sK0) | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl5_9 | ~spl5_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f105,f88,f107])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl5_6 <=> v1_xboole_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl5_6),
% 0.21/0.52    inference(resolution,[],[f56,f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl5_6),
% 0.21/0.52    inference(resolution,[],[f53,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f88])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ~spl5_7 | ~spl5_8 | spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f95,f73,f101,f97])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ~l1_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0)) | spl5_3),
% 0.21/0.52    inference(resolution,[],[f51,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ~v2_struct_0(sK0) | spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl5_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f88])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    v1_xboole_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  % (26770)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl5_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f78])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    v3_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ~spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f37,f73])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f38,f68])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f39,f63])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (26759)------------------------------
% 0.21/0.52  % (26759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26759)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (26759)Memory used [KB]: 6396
% 0.21/0.52  % (26759)Time elapsed: 0.093 s
% 0.21/0.52  % (26759)------------------------------
% 0.21/0.52  % (26759)------------------------------
% 0.21/0.52  % (26741)Success in time 0.162 s
%------------------------------------------------------------------------------
