%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 289 expanded)
%              Number of leaves         :   42 ( 135 expanded)
%              Depth                    :    7
%              Number of atoms          :  525 (1084 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f111,f112,f137,f181,f223,f239,f248,f255,f260,f270,f279,f281,f282,f286,f292,f293,f314,f322,f327,f379,f390,f391])).

fof(f391,plain,
    ( sK1 != k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | v2_tex_2(sK1,sK0)
    | ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f390,plain,
    ( spl6_31
    | spl6_40
    | ~ spl6_17
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f385,f319,f194,f387,f324])).

fof(f324,plain,
    ( spl6_31
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f387,plain,
    ( spl6_40
  <=> sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f194,plain,
    ( spl6_17
  <=> sK1 = k1_tarski(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f319,plain,
    ( spl6_30
  <=> m1_subset_1(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f385,plain,
    ( sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_17
    | ~ spl6_30 ),
    inference(forward_demodulation,[],[f372,f196])).

fof(f196,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f194])).

fof(f372,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | ~ spl6_30 ),
    inference(resolution,[],[f321,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f321,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f319])).

fof(f379,plain,
    ( spl6_38
    | spl6_4
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f370,f319,f84,f74,f89,f376])).

fof(f376,plain,
    ( spl6_38
  <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f89,plain,
    ( spl6_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f74,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f84,plain,
    ( spl6_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f370,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(sK1)),sK0)
    | ~ spl6_30 ),
    inference(resolution,[],[f321,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

% (8350)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f27,plain,(
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

fof(f327,plain,
    ( ~ spl6_31
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f317,f311,f324])).

fof(f311,plain,
    ( spl6_29
  <=> r2_hidden(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f317,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_29 ),
    inference(resolution,[],[f313,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f313,plain,
    ( r2_hidden(sK2(sK1),u1_struct_0(sK0))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f311])).

fof(f322,plain,
    ( spl6_30
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f316,f311,f319])).

fof(f316,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ spl6_29 ),
    inference(resolution,[],[f313,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f61,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f314,plain,
    ( spl6_29
    | ~ spl6_11
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f308,f156,f134,f311])).

fof(f134,plain,
    ( spl6_11
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f156,plain,
    ( spl6_14
  <=> r2_hidden(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f308,plain,
    ( r2_hidden(sK2(sK1),u1_struct_0(sK0))
    | ~ spl6_11
    | ~ spl6_14 ),
    inference(resolution,[],[f294,f136])).

fof(f136,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r2_hidden(sK2(sK1),X0) )
    | ~ spl6_14 ),
    inference(resolution,[],[f158,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f158,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f293,plain,
    ( spl6_6
    | spl6_14
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f289,f141,f156,f99])).

fof(f99,plain,
    ( spl6_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f141,plain,
    ( spl6_12
  <=> m1_subset_1(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f289,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_12 ),
    inference(resolution,[],[f143,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f143,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f292,plain,
    ( spl6_6
    | spl6_17
    | ~ spl6_12
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f291,f178,f141,f194,f99])).

fof(f178,plain,
    ( spl6_15
  <=> sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f291,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ spl6_12
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f288,f180])).

fof(f180,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f178])).

fof(f288,plain,
    ( v1_xboole_0(sK1)
    | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | ~ spl6_12 ),
    inference(resolution,[],[f143,f67])).

fof(f286,plain,
    ( spl6_6
    | spl6_12
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f285,f108,f141,f99])).

fof(f108,plain,
    ( spl6_8
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f285,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f109,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f109,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f282,plain,
    ( sK1 != u1_struct_0(sK3(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f281,plain,
    ( spl6_26
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f280,f257,f267])).

fof(f267,plain,
    ( spl6_26
  <=> l1_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f257,plain,
    ( spl6_24
  <=> l1_pre_topc(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f280,plain,
    ( l1_struct_0(sK3(sK0,sK1))
    | ~ spl6_24 ),
    inference(resolution,[],[f259,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f259,plain,
    ( l1_pre_topc(sK3(sK0,sK1))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f257])).

fof(f279,plain,
    ( spl6_27
    | ~ spl6_7
    | spl6_4
    | spl6_6
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f272,f94,f84,f74,f99,f89,f104,f276])).

fof(f276,plain,
    ( spl6_27
  <=> sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f104,plain,
    ( spl6_7
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f94,plain,
    ( spl6_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f272,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1))
    | ~ spl6_5 ),
    inference(resolution,[],[f58,f96])).

fof(f96,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK3(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f270,plain,
    ( spl6_25
    | ~ spl6_26
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f261,f252,f267,f263])).

fof(f263,plain,
    ( spl6_25
  <=> v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f252,plain,
    ( spl6_23
  <=> v7_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f261,plain,
    ( ~ l1_struct_0(sK3(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1)))
    | ~ spl6_23 ),
    inference(resolution,[],[f254,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f254,plain,
    ( v7_struct_0(sK3(sK0,sK1))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f252])).

fof(f260,plain,
    ( spl6_24
    | ~ spl6_1
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f250,f245,f74,f257])).

fof(f245,plain,
    ( spl6_22
  <=> m1_pre_topc(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f250,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3(sK0,sK1))
    | ~ spl6_22 ),
    inference(resolution,[],[f247,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f247,plain,
    ( m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f245])).

fof(f255,plain,
    ( ~ spl6_21
    | spl6_23
    | spl6_20
    | spl6_4
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f249,f245,f79,f74,f89,f220,f252,f236])).

fof(f236,plain,
    ( spl6_21
  <=> v1_tdlat_3(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f220,plain,
    ( spl6_20
  <=> v2_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f79,plain,
    ( spl6_2
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f249,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1))
    | ~ v1_tdlat_3(sK3(sK0,sK1))
    | ~ spl6_22 ),
    inference(resolution,[],[f247,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(global_subsumption,[],[f51,f53])).

% (8349)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f53,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f248,plain,
    ( spl6_22
    | ~ spl6_7
    | spl6_4
    | spl6_6
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f241,f94,f84,f74,f99,f89,f104,f245])).

fof(f241,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f57,f96])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f239,plain,
    ( spl6_21
    | ~ spl6_7
    | spl6_4
    | spl6_6
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f232,f94,f84,f74,f99,f89,f104,f236])).

fof(f232,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK3(sK0,sK1))
    | ~ spl6_5 ),
    inference(resolution,[],[f56,f96])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f223,plain,
    ( ~ spl6_20
    | ~ spl6_7
    | spl6_4
    | spl6_6
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f217,f94,f84,f74,f99,f89,f104,f220])).

fof(f217,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK3(sK0,sK1))
    | ~ spl6_5 ),
    inference(resolution,[],[f55,f96])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_struct_0(sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f181,plain,
    ( spl6_6
    | spl6_15
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f176,f108,f178,f99])).

fof(f176,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f48,f109])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f137,plain,
    ( spl6_11
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f131,f94,f134])).

fof(f131,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_5 ),
    inference(resolution,[],[f72,f96])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f112,plain,
    ( spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f39,f108,f104])).

fof(f39,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f111,plain,
    ( ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f40,f108,f104])).

fof(f40,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f41,f99])).

fof(f41,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f42,f94])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f92,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f43,f89])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f44,f84])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f45,f79])).

fof(f45,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f19])).

% (8332)Refutation not found, incomplete strategy% (8332)------------------------------
% (8332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8332)Termination reason: Refutation not found, incomplete strategy

% (8332)Memory used [KB]: 10746
% (8332)Time elapsed: 0.119 s
% (8332)------------------------------
% (8332)------------------------------
fof(f77,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f46,f74])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (8331)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.49  % (8346)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.49  % (8332)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (8343)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (8346)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (8338)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (8335)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (8334)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (8359)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (8333)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (8357)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (8337)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (8339)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f392,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f111,f112,f137,f181,f223,f239,f248,f255,f260,f270,f279,f281,f282,f286,f292,f293,f314,f322,f327,f379,f390,f391])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    sK1 != k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | v2_tex_2(sK1,sK0) | ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(sK1)),sK0)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f390,plain,(
% 0.21/0.51    spl6_31 | spl6_40 | ~spl6_17 | ~spl6_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f385,f319,f194,f387,f324])).
% 0.21/0.51  fof(f324,plain,(
% 0.21/0.51    spl6_31 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.51  fof(f387,plain,(
% 0.21/0.51    spl6_40 <=> sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    spl6_17 <=> sK1 = k1_tarski(sK2(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    spl6_30 <=> m1_subset_1(sK2(sK1),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.52  fof(f385,plain,(
% 0.21/0.52    sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl6_17 | ~spl6_30)),
% 0.21/0.52    inference(forward_demodulation,[],[f372,f196])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    sK1 = k1_tarski(sK2(sK1)) | ~spl6_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f194])).
% 0.21/0.52  fof(f372,plain,(
% 0.21/0.52    v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | ~spl6_30),
% 0.21/0.52    inference(resolution,[],[f321,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.52  fof(f321,plain,(
% 0.21/0.52    m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | ~spl6_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f319])).
% 0.21/0.52  fof(f379,plain,(
% 0.21/0.52    spl6_38 | spl6_4 | ~spl6_1 | ~spl6_3 | ~spl6_30),
% 0.21/0.52    inference(avatar_split_clause,[],[f370,f319,f84,f74,f89,f376])).
% 0.21/0.52  fof(f376,plain,(
% 0.21/0.52    spl6_38 <=> v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(sK1)),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    spl6_4 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl6_1 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl6_3 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.52  fof(f370,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK2(sK1)),sK0) | ~spl6_30),
% 0.21/0.52    inference(resolution,[],[f321,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  % (8350)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.21/0.52  fof(f327,plain,(
% 0.21/0.52    ~spl6_31 | ~spl6_29),
% 0.21/0.52    inference(avatar_split_clause,[],[f317,f311,f324])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    spl6_29 <=> r2_hidden(sK2(sK1),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.52  fof(f317,plain,(
% 0.21/0.52    ~v1_xboole_0(u1_struct_0(sK0)) | ~spl6_29),
% 0.21/0.52    inference(resolution,[],[f313,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    r2_hidden(sK2(sK1),u1_struct_0(sK0)) | ~spl6_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f311])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    spl6_30 | ~spl6_29),
% 0.21/0.52    inference(avatar_split_clause,[],[f316,f311,f319])).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | ~spl6_29),
% 0.21/0.52    inference(resolution,[],[f313,f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.52    inference(global_subsumption,[],[f61,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.52  fof(f314,plain,(
% 0.21/0.52    spl6_29 | ~spl6_11 | ~spl6_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f308,f156,f134,f311])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl6_11 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    spl6_14 <=> r2_hidden(sK2(sK1),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.52  fof(f308,plain,(
% 0.21/0.52    r2_hidden(sK2(sK1),u1_struct_0(sK0)) | (~spl6_11 | ~spl6_14)),
% 0.21/0.52    inference(resolution,[],[f294,f136])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl6_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f134])).
% 0.21/0.52  fof(f294,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK2(sK1),X0)) ) | ~spl6_14),
% 0.21/0.52    inference(resolution,[],[f158,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    r2_hidden(sK2(sK1),sK1) | ~spl6_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f156])).
% 0.21/0.52  fof(f293,plain,(
% 0.21/0.52    spl6_6 | spl6_14 | ~spl6_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f289,f141,f156,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl6_6 <=> v1_xboole_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    spl6_12 <=> m1_subset_1(sK2(sK1),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    r2_hidden(sK2(sK1),sK1) | v1_xboole_0(sK1) | ~spl6_12),
% 0.21/0.52    inference(resolution,[],[f143,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    m1_subset_1(sK2(sK1),sK1) | ~spl6_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f141])).
% 0.21/0.52  fof(f292,plain,(
% 0.21/0.52    spl6_6 | spl6_17 | ~spl6_12 | ~spl6_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f291,f178,f141,f194,f99])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    spl6_15 <=> sK1 = k6_domain_1(sK1,sK2(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    sK1 = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1) | (~spl6_12 | ~spl6_15)),
% 0.21/0.52    inference(forward_demodulation,[],[f288,f180])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~spl6_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f178])).
% 0.21/0.52  fof(f288,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | ~spl6_12),
% 0.21/0.52    inference(resolution,[],[f143,f67])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    spl6_6 | spl6_12 | ~spl6_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f285,f108,f141,f99])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    spl6_8 <=> v1_zfmisc_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    m1_subset_1(sK2(sK1),sK1) | v1_xboole_0(sK1) | ~spl6_8),
% 0.21/0.52    inference(resolution,[],[f109,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_zfmisc_1(X0) | m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    v1_zfmisc_1(sK1) | ~spl6_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f108])).
% 0.21/0.52  fof(f282,plain,(
% 0.21/0.52    sK1 != u1_struct_0(sK3(sK0,sK1)) | v1_zfmisc_1(sK1) | ~v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1)))),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    spl6_26 | ~spl6_24),
% 0.21/0.52    inference(avatar_split_clause,[],[f280,f257,f267])).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    spl6_26 <=> l1_struct_0(sK3(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    spl6_24 <=> l1_pre_topc(sK3(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    l1_struct_0(sK3(sK0,sK1)) | ~spl6_24),
% 0.21/0.52    inference(resolution,[],[f259,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    l1_pre_topc(sK3(sK0,sK1)) | ~spl6_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f257])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    spl6_27 | ~spl6_7 | spl6_4 | spl6_6 | ~spl6_1 | ~spl6_3 | ~spl6_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f272,f94,f84,f74,f99,f89,f104,f276])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    spl6_27 <=> sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl6_7 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl6_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK3(sK0,sK1)) | ~spl6_5),
% 0.21/0.52    inference(resolution,[],[f58,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f94])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | u1_struct_0(sK3(X0,X1)) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 0.21/0.52  fof(f270,plain,(
% 0.21/0.52    spl6_25 | ~spl6_26 | ~spl6_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f261,f252,f267,f263])).
% 0.21/0.52  fof(f263,plain,(
% 0.21/0.52    spl6_25 <=> v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    spl6_23 <=> v7_struct_0(sK3(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    ~l1_struct_0(sK3(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK3(sK0,sK1))) | ~spl6_23),
% 0.21/0.52    inference(resolution,[],[f254,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    v7_struct_0(sK3(sK0,sK1)) | ~spl6_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f252])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    spl6_24 | ~spl6_1 | ~spl6_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f250,f245,f74,f257])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    spl6_22 <=> m1_pre_topc(sK3(sK0,sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | l1_pre_topc(sK3(sK0,sK1)) | ~spl6_22),
% 0.21/0.52    inference(resolution,[],[f247,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    m1_pre_topc(sK3(sK0,sK1),sK0) | ~spl6_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f245])).
% 0.21/0.52  fof(f255,plain,(
% 0.21/0.52    ~spl6_21 | spl6_23 | spl6_20 | spl6_4 | ~spl6_1 | ~spl6_2 | ~spl6_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f249,f245,f79,f74,f89,f220,f252,f236])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    spl6_21 <=> v1_tdlat_3(sK3(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    spl6_20 <=> v2_struct_0(sK3(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl6_2 <=> v2_tdlat_3(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f249,plain,(
% 0.21/0.52    ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1)) | ~v1_tdlat_3(sK3(sK0,sK1)) | ~spl6_22),
% 0.21/0.52    inference(resolution,[],[f247,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.21/0.52    inference(global_subsumption,[],[f51,f53])).
% 0.21/0.52  % (8349)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    spl6_22 | ~spl6_7 | spl6_4 | spl6_6 | ~spl6_1 | ~spl6_3 | ~spl6_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f241,f94,f84,f74,f99,f89,f104,f245])).
% 0.21/0.52  fof(f241,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK3(sK0,sK1),sK0) | ~spl6_5),
% 0.21/0.52    inference(resolution,[],[f57,f96])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK3(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    spl6_21 | ~spl6_7 | spl6_4 | spl6_6 | ~spl6_1 | ~spl6_3 | ~spl6_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f232,f94,f84,f74,f99,f89,f104,f236])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK3(sK0,sK1)) | ~spl6_5),
% 0.21/0.52    inference(resolution,[],[f56,f96])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | v1_tdlat_3(sK3(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    ~spl6_20 | ~spl6_7 | spl6_4 | spl6_6 | ~spl6_1 | ~spl6_3 | ~spl6_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f217,f94,f84,f74,f99,f89,f104,f220])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK3(sK0,sK1)) | ~spl6_5),
% 0.21/0.52    inference(resolution,[],[f55,f96])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | ~v2_struct_0(sK3(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    spl6_6 | spl6_15 | ~spl6_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f176,f108,f178,f99])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    sK1 = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1) | ~spl6_8),
% 0.21/0.52    inference(resolution,[],[f48,f109])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl6_11 | ~spl6_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f131,f94,f134])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl6_5),
% 0.21/0.52    inference(resolution,[],[f72,f96])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    spl6_7 | spl6_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f39,f108,f104])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ~spl6_7 | ~spl6_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f108,f104])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ~spl6_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f99])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl6_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f94])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ~spl6_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f89])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl6_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f44,f84])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl6_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f45,f79])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    v2_tdlat_3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  % (8332)Refutation not found, incomplete strategy% (8332)------------------------------
% 0.21/0.52  % (8332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8332)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8332)Memory used [KB]: 10746
% 0.21/0.52  % (8332)Time elapsed: 0.119 s
% 0.21/0.52  % (8332)------------------------------
% 0.21/0.52  % (8332)------------------------------
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl6_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f46,f74])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (8346)------------------------------
% 0.21/0.52  % (8346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8346)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (8346)Memory used [KB]: 11001
% 0.21/0.52  % (8346)Time elapsed: 0.107 s
% 0.21/0.52  % (8346)------------------------------
% 0.21/0.52  % (8346)------------------------------
% 0.21/0.52  % (8352)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (8329)Success in time 0.164 s
%------------------------------------------------------------------------------
