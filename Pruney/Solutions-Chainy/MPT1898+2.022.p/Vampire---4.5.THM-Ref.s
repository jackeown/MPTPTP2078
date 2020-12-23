%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 180 expanded)
%              Number of leaves         :   20 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  260 ( 576 expanded)
%              Number of equality atoms :   13 (  39 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f123,f137,f143,f149,f157])).

fof(f157,plain,
    ( ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f150,f146,f140])).

fof(f140,plain,
    ( spl4_12
  <=> v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f146,plain,
    ( spl4_13
  <=> m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f150,plain,
    ( ~ v3_tex_2(sK1(sK0,k1_xboole_0),sK0)
    | ~ spl4_13 ),
    inference(resolution,[],[f148,f20])).

fof(f20,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

fof(f148,plain,
    ( m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f149,plain,
    ( spl4_13
    | ~ spl4_3
    | spl4_4
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f144,f134,f65,f50,f45,f60,f55,f146])).

fof(f55,plain,
    ( spl4_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f60,plain,
    ( spl4_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f45,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f50,plain,
    ( spl4_2
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f65,plain,
    ( spl4_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f134,plain,
    ( spl4_11
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f144,plain,
    ( ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(resolution,[],[f125,f136])).

fof(f136,plain,
    ( v2_tex_2(k1_xboole_0,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f125,plain,
    ( ! [X2] :
        ( ~ v2_tex_2(k1_xboole_0,X2)
        | ~ v3_tdlat_3(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | m1_subset_1(sK1(X2,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X2))) )
    | ~ spl4_5 ),
    inference(resolution,[],[f26,f104])).

fof(f104,plain,
    ( ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ spl4_5 ),
    inference(resolution,[],[f83,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f83,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl4_5 ),
    inference(superposition,[],[f40,f78])).

fof(f78,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)
    | ~ spl4_5 ),
    inference(resolution,[],[f75,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ sP3(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f32,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP3(X1) ) ),
    inference(general_splitting,[],[f39,f42_D])).

fof(f42,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP3(X1) ) ),
    inference(cnf_transformation,[],[f42_D])).

fof(f42_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP3(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f75,plain,
    ( ! [X0] : sP3(k6_subset_1(k1_xboole_0,X0))
    | ~ spl4_5 ),
    inference(resolution,[],[f74,f67])).

fof(f67,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | sP3(k6_subset_1(X0,X1)) ) ),
    inference(resolution,[],[f42,f33])).

fof(f33,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

fof(f143,plain,
    ( spl4_12
    | ~ spl4_3
    | spl4_4
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f138,f134,f65,f50,f45,f60,f55,f140])).

fof(f138,plain,
    ( ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_tex_2(sK1(sK0,k1_xboole_0),sK0)
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(resolution,[],[f112,f136])).

fof(f112,plain,
    ( ! [X2] :
        ( ~ v2_tex_2(k1_xboole_0,X2)
        | ~ v3_tdlat_3(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | v3_tex_2(sK1(X2,k1_xboole_0),X2) )
    | ~ spl4_5 ),
    inference(resolution,[],[f104,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f137,plain,
    ( ~ spl4_3
    | spl4_4
    | spl4_11
    | ~ spl4_1
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f132,f121,f45,f134,f60,f55])).

fof(f121,plain,
    ( spl4_10
  <=> ! [X4] :
        ( ~ v2_pre_topc(X4)
        | v2_tex_2(k1_xboole_0,X4)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f132,plain,
    ( v2_tex_2(k1_xboole_0,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_10 ),
    inference(resolution,[],[f122,f47])).

fof(f47,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f122,plain,
    ( ! [X4] :
        ( ~ l1_pre_topc(X4)
        | v2_tex_2(k1_xboole_0,X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( ~ spl4_5
    | spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f114,f65,f121,f65])).

fof(f114,plain,
    ( ! [X4] :
        ( ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ v1_xboole_0(k1_xboole_0)
        | v2_struct_0(X4)
        | v2_tex_2(k1_xboole_0,X4) )
    | ~ spl4_5 ),
    inference(resolution,[],[f104,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
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
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f68,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f63,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f21,f60])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:29:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (16196)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (16194)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (16199)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (16202)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (16196)Refutation not found, incomplete strategy% (16196)------------------------------
% 0.21/0.51  % (16196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16196)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16196)Memory used [KB]: 10618
% 0.21/0.51  % (16196)Time elapsed: 0.100 s
% 0.21/0.51  % (16196)------------------------------
% 0.21/0.51  % (16196)------------------------------
% 0.21/0.52  % (16198)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (16210)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (16200)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (16202)Refutation not found, incomplete strategy% (16202)------------------------------
% 0.21/0.52  % (16202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16202)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16202)Memory used [KB]: 10618
% 0.21/0.52  % (16202)Time elapsed: 0.119 s
% 0.21/0.52  % (16202)------------------------------
% 0.21/0.52  % (16202)------------------------------
% 0.21/0.52  % (16210)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f123,f137,f143,f149,f157])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    ~spl4_12 | ~spl4_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f150,f146,f140])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl4_12 <=> v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    spl4_13 <=> m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~v3_tex_2(sK1(sK0,k1_xboole_0),sK0) | ~spl4_13),
% 0.21/0.52    inference(resolution,[],[f148,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X1,sK0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f146])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl4_13 | ~spl4_3 | spl4_4 | ~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f144,f134,f65,f50,f45,f60,f55,f146])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl4_3 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    spl4_4 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    spl4_1 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl4_2 <=> v3_tdlat_3(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl4_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl4_11 <=> v2_tex_2(k1_xboole_0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_5 | ~spl4_11)),
% 0.21/0.52    inference(resolution,[],[f125,f136])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    v2_tex_2(k1_xboole_0,sK0) | ~spl4_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f134])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X2] : (~v2_tex_2(k1_xboole_0,X2) | ~v3_tdlat_3(X2) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(X2) | m1_subset_1(sK1(X2,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X2)))) ) | ~spl4_5),
% 0.21/0.52    inference(resolution,[],[f26,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) ) | ~spl4_5),
% 0.21/0.52    inference(resolution,[],[f83,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_5),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) ) | ~spl4_5),
% 0.21/0.52    inference(superposition,[],[f40,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) ) | ~spl4_5),
% 0.21/0.52    inference(resolution,[],[f75,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (~sP3(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(resolution,[],[f32,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP3(X1)) )),
% 0.21/0.52    inference(general_splitting,[],[f39,f42_D])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP3(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f42_D])).
% 0.21/0.52  fof(f42_D,plain,(
% 0.21/0.52    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP3(X1)) )),
% 0.21/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (sP3(k6_subset_1(k1_xboole_0,X0))) ) | ~spl4_5),
% 0.21/0.52    inference(resolution,[],[f74,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0) | ~spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | sP3(k6_subset_1(X0,X1))) )),
% 0.21/0.52    inference(resolution,[],[f42,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f38,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    spl4_12 | ~spl4_3 | spl4_4 | ~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f138,f134,f65,f50,f45,f60,f55,f140])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | v3_tex_2(sK1(sK0,k1_xboole_0),sK0) | (~spl4_5 | ~spl4_11)),
% 0.21/0.52    inference(resolution,[],[f112,f136])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X2] : (~v2_tex_2(k1_xboole_0,X2) | ~v3_tdlat_3(X2) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(X2) | v3_tex_2(sK1(X2,k1_xboole_0),X2)) ) | ~spl4_5),
% 0.21/0.52    inference(resolution,[],[f104,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | v3_tex_2(sK1(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ~spl4_3 | spl4_4 | spl4_11 | ~spl4_1 | ~spl4_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f132,f121,f45,f134,f60,f55])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl4_10 <=> ! [X4] : (~v2_pre_topc(X4) | v2_tex_2(k1_xboole_0,X4) | v2_struct_0(X4) | ~l1_pre_topc(X4))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    v2_tex_2(k1_xboole_0,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | (~spl4_1 | ~spl4_10)),
% 0.21/0.52    inference(resolution,[],[f122,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    l1_pre_topc(sK0) | ~spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f45])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ( ! [X4] : (~l1_pre_topc(X4) | v2_tex_2(k1_xboole_0,X4) | v2_struct_0(X4) | ~v2_pre_topc(X4)) ) | ~spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f121])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ~spl4_5 | spl4_10 | ~spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f114,f65,f121,f65])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X4] : (~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v1_xboole_0(k1_xboole_0) | v2_struct_0(X4) | v2_tex_2(k1_xboole_0,X4)) ) | ~spl4_5),
% 0.21/0.52    inference(resolution,[],[f104,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f25,f65])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f21,f60])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f22,f55])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f23,f50])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    v3_tdlat_3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f24,f45])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (16210)------------------------------
% 0.21/0.52  % (16210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16210)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (16210)Memory used [KB]: 10746
% 0.21/0.52  % (16210)Time elapsed: 0.117 s
% 0.21/0.52  % (16210)------------------------------
% 0.21/0.52  % (16210)------------------------------
% 0.21/0.52  % (16209)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (16190)Success in time 0.165 s
%------------------------------------------------------------------------------
