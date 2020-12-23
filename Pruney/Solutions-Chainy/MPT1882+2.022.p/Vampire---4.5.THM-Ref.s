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
% DateTime   : Thu Dec  3 13:22:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 454 expanded)
%              Number of leaves         :   14 (  94 expanded)
%              Depth                    :   23
%              Number of atoms          :  507 (2522 expanded)
%              Number of equality atoms :   38 (  61 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f59,f115,f126,f142,f172])).

% (7247)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f172,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f170,f29])).

fof(f29,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

% (7252)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

fof(f170,plain,
    ( v1_xboole_0(sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f169,f56])).

fof(f56,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f169,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f167,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f167,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f166,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f80,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_zfmisc_1(X0)
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f79,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_zfmisc_1(X0)
      | v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f62,f33])).

fof(f33,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f166,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f165,f53])).

fof(f53,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f165,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f164,f30])).

fof(f164,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f163,f152])).

fof(f152,plain,
    ( sK1 != sK2(sK0,sK1)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f151,f30])).

fof(f151,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f150,f29])).

fof(f150,plain,
    ( v1_xboole_0(sK1)
    | sK1 != sK2(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f146,f56])).

fof(f146,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | sK1 != sK2(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1 ),
    inference(resolution,[],[f53,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v3_tex_2(X0,sK0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | sK2(sK0,X0) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(sK0,X0) != X0
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f81,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(sK0,X0) != X0
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f40,f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | sK2(X0,X1) != X1
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f163,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f161,f74])).

fof(f74,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK2(sK0,X0))
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

% (7246)Refutation not found, incomplete strategy% (7246)------------------------------
% (7246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f161,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2(sK0,sK1))
        | sK2(sK0,sK1) = X0 )
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | sK2(sK0,sK1) = X0
        | ~ r1_tarski(X0,sK2(sK0,sK1)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f48,f156])).

fof(f156,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(sK2(sK0,sK1),X0)
    | ~ spl4_4 ),
    inference(resolution,[],[f155,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ( ( r2_hidden(X3,X1)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_mcart_1)).

fof(f155,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k6_subset_1(sK2(sK0,sK1),X1))
    | ~ spl4_4 ),
    inference(resolution,[],[f154,f47])).

fof(f47,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

% (7256)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK0,sK1)))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f114,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f114,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_4
  <=> v1_xboole_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k6_subset_1(X1,X0)
        & X0 != X1
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_tex_2)).

fof(f142,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f140,f57])).

fof(f57,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f140,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f139,f30])).

fof(f139,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f52,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v3_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f69,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f42,f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | v1_zfmisc_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f68,f34])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f67,f31])).

fof(f67,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f61,f33])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f60,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f45,f36])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f126,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f124,f29])).

fof(f124,plain,
    ( v1_xboole_0(sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f123,f56])).

fof(f123,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f121,f30])).

fof(f121,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f120,f81])).

fof(f120,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f119,f53])).

fof(f119,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f118,f30])).

fof(f118,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f117,f29])).

fof(f117,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f116,f91])).

% (7257)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (7246)Termination reason: Refutation not found, incomplete strategy
fof(f91,plain,
    ( sK1 != sK2(sK0,sK1)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f90,f30])).

% (7246)Memory used [KB]: 10618
fof(f90,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f89,f29])).

% (7246)Time elapsed: 0.074 s
% (7246)------------------------------
% (7246)------------------------------
fof(f89,plain,
    ( v1_xboole_0(sK1)
    | sK1 != sK2(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f86,f56])).

fof(f86,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | sK1 != sK2(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1 ),
    inference(resolution,[],[f85,f53])).

fof(f116,plain,
    ( sK1 = sK2(sK0,sK1)
    | v1_xboole_0(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f110,f74])).

% (7261)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f110,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2(sK0,sK1))
        | sK2(sK0,sK1) = X0
        | v1_xboole_0(X0) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_3
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | sK2(sK0,sK1) = X0
        | ~ r1_tarski(X0,sK2(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f115,plain,
    ( spl4_3
    | spl4_4
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f107,f55,f51,f112,f109])).

fof(f107,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK2(sK0,sK1))
        | v1_xboole_0(X0)
        | ~ r1_tarski(X0,sK2(sK0,sK1))
        | sK2(sK0,sK1) = X0 )
    | spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f106,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f106,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f105,f29])).

fof(f105,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f104,f56])).

fof(f104,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f101,f30])).

fof(f101,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | spl4_1 ),
    inference(resolution,[],[f99,f53])).

fof(f99,plain,(
    ! [X0] :
      ( v3_tex_2(X0,sK0)
      | v1_zfmisc_1(sK2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( v3_tex_2(X0,sK0)
      | v1_zfmisc_1(sK2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f94,f81])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0)
      | v1_zfmisc_1(sK2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f73,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f37,f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X0,sK0)
      | v1_zfmisc_1(sK2(sK0,X0))
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f72,f69])).

fof(f72,plain,(
    ! [X0] :
      ( v2_tex_2(sK2(sK0,X0),sK0)
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f38,f34])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(sK2(X0,X1),X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f27,f55,f51])).

fof(f27,plain,
    ( v1_zfmisc_1(sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f28,f55,f51])).

fof(f28,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:59:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (7243)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (7245)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (7262)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (7241)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (7254)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (7241)Refutation not found, incomplete strategy% (7241)------------------------------
% 0.21/0.51  % (7241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7259)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (7240)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (7246)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (7255)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (7240)Refutation not found, incomplete strategy% (7240)------------------------------
% 0.21/0.51  % (7240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7240)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7240)Memory used [KB]: 10618
% 0.21/0.51  % (7240)Time elapsed: 0.095 s
% 0.21/0.51  % (7240)------------------------------
% 0.21/0.51  % (7240)------------------------------
% 0.21/0.51  % (7265)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (7253)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (7264)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (7251)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (7262)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f58,f59,f115,f126,f142,f172])).
% 0.21/0.52  % (7247)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    $false | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f170,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  % (7252)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f169,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    v1_zfmisc_1(sK1) | ~spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl4_2 <=> v1_zfmisc_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f167,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.52    inference(resolution,[],[f166,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0] : (v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f80,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v2_tex_2(X0,sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f79,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v2_tex_2(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f62,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    v2_tdlat_3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f44,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f165,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ~v3_tex_2(sK1,sK0) | spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl4_1 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f164,f30])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f163,f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    sK1 != sK2(sK0,sK1) | (spl4_1 | ~spl4_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f151,f30])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    sK1 != sK2(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f150,f29])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | sK1 != sK2(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f146,f56])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | sK1 != sK2(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_1),
% 0.21/0.52    inference(resolution,[],[f53,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X0] : (v3_tex_2(X0,sK0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | sK2(sK0,X0) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(sK0,X0) != X0 | v3_tex_2(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f81,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(sK0,X0) != X0 | v3_tex_2(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f40,f34])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | sK2(X0,X1) != X1 | v3_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    sK1 = sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f161,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,sK2(sK0,X0)) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f39,f34])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1)) | v3_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  % (7246)Refutation not found, incomplete strategy% (7246)------------------------------
% 0.21/0.52  % (7246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,sK2(sK0,sK1)) | sK2(sK0,sK1) = X0) ) | ~spl4_4),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | sK2(sK0,sK1) = X0 | ~r1_tarski(X0,sK2(sK0,sK1))) ) | ~spl4_4),
% 0.21/0.52    inference(superposition,[],[f48,f156])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k6_subset_1(sK2(sK0,sK1),X0)) ) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f155,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.52    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ((r2_hidden(X3,X1) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_mcart_1)).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k6_subset_1(sK2(sK0,sK1),X1))) ) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f154,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  % (7256)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK2(sK0,sK1))) | ~r2_hidden(X1,X0)) ) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f114,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    v1_xboole_0(sK2(sK0,sK1)) | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    spl4_4 <=> v1_xboole_0(sK2(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(k1_xboole_0 = k6_subset_1(X1,X0) & X0 != X1 & r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_tex_2)).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    ~spl4_1 | spl4_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f141])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    $false | (~spl4_1 | spl4_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f140,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f55])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    v1_zfmisc_1(sK1) | ~spl4_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f139,f30])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK1) | ~spl4_1),
% 0.21/0.52    inference(resolution,[],[f52,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0] : (~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0] : (v1_zfmisc_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f69,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f42,f34])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_tex_2(X0,sK0) | v1_zfmisc_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f68,f34])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f67,f31])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f61,f33])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f60,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f45,f36])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    v3_tex_2(sK1,sK0) | ~spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    $false | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f124,f29])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f123,f56])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f121,f30])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.52    inference(resolution,[],[f120,f81])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f119,f53])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f118,f30])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f117,f29])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f116,f91])).
% 0.21/0.52  % (7257)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (7246)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    sK1 != sK2(sK0,sK1) | (spl4_1 | ~spl4_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f90,f30])).
% 0.21/0.52  
% 0.21/0.52  % (7246)Memory used [KB]: 10618
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    sK1 != sK2(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f89,f29])).
% 0.21/0.52  % (7246)Time elapsed: 0.074 s
% 0.21/0.52  % (7246)------------------------------
% 0.21/0.52  % (7246)------------------------------
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | sK1 != sK2(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f86,f56])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | sK1 != sK2(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_1),
% 0.21/0.52    inference(resolution,[],[f85,f53])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    sK1 = sK2(sK0,sK1) | v1_xboole_0(sK1) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0) | ~spl4_3),
% 0.21/0.52    inference(resolution,[],[f110,f74])).
% 0.21/0.52  % (7261)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,sK2(sK0,sK1)) | sK2(sK0,sK1) = X0 | v1_xboole_0(X0)) ) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    spl4_3 <=> ! [X0] : (v1_xboole_0(X0) | sK2(sK0,sK1) = X0 | ~r1_tarski(X0,sK2(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    spl4_3 | spl4_4 | spl4_1 | ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f107,f55,f51,f112,f109])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X0] : (v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(X0) | ~r1_tarski(X0,sK2(sK0,sK1)) | sK2(sK0,sK1) = X0) ) | (spl4_1 | ~spl4_2)),
% 0.21/0.52    inference(resolution,[],[f106,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    v1_zfmisc_1(sK2(sK0,sK1)) | (spl4_1 | ~spl4_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f105,f29])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK1) | (spl4_1 | ~spl4_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f104,f56])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    v1_zfmisc_1(sK2(sK0,sK1)) | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | spl4_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f101,f30])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    v1_zfmisc_1(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | spl4_1),
% 0.21/0.52    inference(resolution,[],[f99,f53])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X0] : (v3_tex_2(X0,sK0) | v1_zfmisc_1(sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X0] : (v3_tex_2(X0,sK0) | v1_zfmisc_1(sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(resolution,[],[f94,f81])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0) | v1_zfmisc_1(sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f73,f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f37,f34])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0) | v1_zfmisc_1(sK2(sK0,X0)) | ~v2_tex_2(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f72,f69])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0] : (v2_tex_2(sK2(sK0,X0),sK0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f38,f34])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_tex_2(sK2(X0,X1),X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl4_1 | spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f27,f55,f51])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ~spl4_1 | ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f28,f55,f51])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (7262)------------------------------
% 0.21/0.52  % (7262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7262)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (7262)Memory used [KB]: 10746
% 0.21/0.52  % (7262)Time elapsed: 0.066 s
% 0.21/0.52  % (7262)------------------------------
% 0.21/0.52  % (7262)------------------------------
% 0.21/0.52  % (7241)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7241)Memory used [KB]: 10618
% 0.21/0.52  % (7241)Time elapsed: 0.094 s
% 0.21/0.52  % (7241)------------------------------
% 0.21/0.52  % (7241)------------------------------
% 0.21/0.52  % (7239)Success in time 0.157 s
%------------------------------------------------------------------------------
