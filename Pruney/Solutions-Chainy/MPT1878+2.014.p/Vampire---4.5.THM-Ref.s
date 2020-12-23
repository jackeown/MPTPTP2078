%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 177 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  307 ( 505 expanded)
%              Number of equality atoms :   35 (  57 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f532,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f101,f106,f117,f210,f226,f260,f364,f385,f391,f396,f476,f485,f531])).

fof(f531,plain,
    ( ~ spl4_1
    | ~ spl4_19
    | ~ spl4_39
    | ~ spl4_46 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_19
    | ~ spl4_39
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f75,f225,f107,f44,f363,f407,f45,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f407,plain,
    ( m1_subset_1(k1_tarski(sK3(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl4_46
  <=> m1_subset_1(k1_tarski(sK3(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f363,plain,
    ( v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl4_39
  <=> v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f59,f46])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f59,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f225,plain,
    ( v3_tex_2(k1_xboole_0,sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl4_19
  <=> v3_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f75,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f485,plain,
    ( spl4_22
    | spl4_55 ),
    inference(avatar_split_clause,[],[f483,f473,f253])).

fof(f253,plain,
    ( spl4_22
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f473,plain,
    ( spl4_55
  <=> r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f483,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | spl4_55 ),
    inference(resolution,[],[f475,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f475,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl4_55 ),
    inference(avatar_component_clause,[],[f473])).

fof(f476,plain,
    ( ~ spl4_55
    | spl4_46 ),
    inference(avatar_split_clause,[],[f470,f406,f473])).

fof(f470,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl4_46 ),
    inference(resolution,[],[f408,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f408,plain,
    ( ~ m1_subset_1(k1_tarski(sK3(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_46 ),
    inference(avatar_component_clause,[],[f406])).

fof(f396,plain,
    ( ~ spl4_1
    | spl4_9 ),
    inference(avatar_split_clause,[],[f394,f114,f73])).

fof(f114,plain,
    ( spl4_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f394,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_9 ),
    inference(resolution,[],[f116,f47])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f116,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f391,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f385,plain,
    ( spl4_22
    | spl4_38 ),
    inference(avatar_split_clause,[],[f383,f357,f253])).

fof(f357,plain,
    ( spl4_38
  <=> m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f383,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | spl4_38 ),
    inference(resolution,[],[f359,f118])).

fof(f118,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f58,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f359,plain,
    ( ~ m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f357])).

fof(f364,plain,
    ( spl4_3
    | ~ spl4_38
    | ~ spl4_1
    | ~ spl4_2
    | spl4_39
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f353,f257,f361,f78,f73,f357,f83])).

fof(f83,plain,
    ( spl4_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f78,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f257,plain,
    ( spl4_23
  <=> k1_tarski(sK3(u1_struct_0(sK0))) = k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f353,plain,
    ( v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_23 ),
    inference(superposition,[],[f54,f259])).

fof(f259,plain,
    ( k1_tarski(sK3(u1_struct_0(sK0))) = k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0)))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f257])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
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
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f260,plain,
    ( spl4_22
    | spl4_23
    | spl4_8 ),
    inference(avatar_split_clause,[],[f251,f110,f257,f253])).

fof(f110,plain,
    ( spl4_8
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

% (31944)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f251,plain,
    ( k1_tarski(sK3(u1_struct_0(sK0))) = k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | spl4_8 ),
    inference(resolution,[],[f195,f118])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0) )
    | spl4_8 ),
    inference(resolution,[],[f62,f112])).

fof(f112,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

% (31938)Refutation not found, incomplete strategy% (31938)------------------------------
% (31938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31938)Termination reason: Refutation not found, incomplete strategy

% (31938)Memory used [KB]: 6140
% (31938)Time elapsed: 0.117 s
% (31938)------------------------------
% (31938)------------------------------
fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f226,plain,
    ( spl4_19
    | ~ spl4_4
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f211,f207,f88,f223])).

fof(f88,plain,
    ( spl4_4
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f207,plain,
    ( spl4_18
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f211,plain,
    ( v3_tex_2(k1_xboole_0,sK0)
    | ~ spl4_4
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f90,f209])).

fof(f209,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f207])).

fof(f90,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f210,plain,
    ( spl4_18
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f204,f98,f207])).

fof(f98,plain,
    ( spl4_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f204,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6 ),
    inference(resolution,[],[f156,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0 )
    | ~ spl4_6 ),
    inference(resolution,[],[f155,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | k1_xboole_0 = X0 )
    | ~ spl4_6 ),
    inference(resolution,[],[f152,f58])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f69,f100])).

fof(f100,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f117,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | spl4_3 ),
    inference(avatar_split_clause,[],[f108,f83,f114,f110])).

fof(f108,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_3 ),
    inference(resolution,[],[f55,f85])).

fof(f85,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f55,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f106,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f43,f103])).

fof(f103,plain,
    ( spl4_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f101,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f37,f98])).

fof(f37,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f91,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f88])).

fof(f39,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f40,f83])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f78])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f42,f73])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:38:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (31940)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  % (31941)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (31933)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (31937)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (31934)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (31955)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (31935)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (31949)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (31934)Refutation not found, incomplete strategy% (31934)------------------------------
% 0.21/0.51  % (31934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31934)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31934)Memory used [KB]: 10618
% 0.21/0.51  % (31934)Time elapsed: 0.095 s
% 0.21/0.51  % (31934)------------------------------
% 0.21/0.51  % (31934)------------------------------
% 0.21/0.51  % (31940)Refutation not found, incomplete strategy% (31940)------------------------------
% 0.21/0.51  % (31940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31940)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31940)Memory used [KB]: 1663
% 0.21/0.51  % (31940)Time elapsed: 0.096 s
% 0.21/0.51  % (31940)------------------------------
% 0.21/0.51  % (31940)------------------------------
% 0.21/0.51  % (31939)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (31933)Refutation not found, incomplete strategy% (31933)------------------------------
% 0.21/0.51  % (31933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31933)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31933)Memory used [KB]: 10618
% 0.21/0.51  % (31933)Time elapsed: 0.105 s
% 0.21/0.51  % (31933)------------------------------
% 0.21/0.51  % (31933)------------------------------
% 0.21/0.51  % (31950)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (31948)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (31946)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (31952)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (31943)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (31942)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (31947)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (31938)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (31948)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f532,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f101,f106,f117,f210,f226,f260,f364,f385,f391,f396,f476,f485,f531])).
% 0.21/0.53  fof(f531,plain,(
% 0.21/0.53    ~spl4_1 | ~spl4_19 | ~spl4_39 | ~spl4_46),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f529])).
% 0.21/0.53  fof(f529,plain,(
% 0.21/0.53    $false | (~spl4_1 | ~spl4_19 | ~spl4_39 | ~spl4_46)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f75,f225,f107,f44,f363,f407,f45,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X2,X0) | ~r1_tarski(X1,X2) | X1 = X2 | ~v3_tex_2(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.53  fof(f407,plain,(
% 0.21/0.53    m1_subset_1(k1_tarski(sK3(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_46),
% 0.21/0.53    inference(avatar_component_clause,[],[f406])).
% 0.21/0.53  fof(f406,plain,(
% 0.21/0.53    spl4_46 <=> m1_subset_1(k1_tarski(sK3(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.21/0.53  fof(f363,plain,(
% 0.21/0.53    v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0) | ~spl4_39),
% 0.21/0.53    inference(avatar_component_clause,[],[f361])).
% 0.21/0.53  fof(f361,plain,(
% 0.21/0.53    spl4_39 <=> v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.21/0.53    inference(superposition,[],[f59,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    v3_tex_2(k1_xboole_0,sK0) | ~spl4_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f223])).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    spl4_19 <=> v3_tex_2(k1_xboole_0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    l1_pre_topc(sK0) | ~spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl4_1 <=> l1_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f485,plain,(
% 0.21/0.53    spl4_22 | spl4_55),
% 0.21/0.53    inference(avatar_split_clause,[],[f483,f473,f253])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    spl4_22 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.53  fof(f473,plain,(
% 0.21/0.53    spl4_55 <=> r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.21/0.53  fof(f483,plain,(
% 0.21/0.53    k1_xboole_0 = u1_struct_0(sK0) | spl4_55),
% 0.21/0.53    inference(resolution,[],[f475,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.53  fof(f475,plain,(
% 0.21/0.53    ~r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) | spl4_55),
% 0.21/0.53    inference(avatar_component_clause,[],[f473])).
% 0.21/0.53  fof(f476,plain,(
% 0.21/0.53    ~spl4_55 | spl4_46),
% 0.21/0.53    inference(avatar_split_clause,[],[f470,f406,f473])).
% 0.21/0.53  fof(f470,plain,(
% 0.21/0.53    ~r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) | spl4_46),
% 0.21/0.53    inference(resolution,[],[f408,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.53  fof(f408,plain,(
% 0.21/0.53    ~m1_subset_1(k1_tarski(sK3(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_46),
% 0.21/0.53    inference(avatar_component_clause,[],[f406])).
% 0.21/0.53  fof(f396,plain,(
% 0.21/0.53    ~spl4_1 | spl4_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f394,f114,f73])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    spl4_9 <=> l1_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.53  fof(f394,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | spl4_9),
% 0.21/0.53    inference(resolution,[],[f116,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ~l1_struct_0(sK0) | spl4_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f114])).
% 0.21/0.53  fof(f391,plain,(
% 0.21/0.53    k1_xboole_0 != u1_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f385,plain,(
% 0.21/0.53    spl4_22 | spl4_38),
% 0.21/0.53    inference(avatar_split_clause,[],[f383,f357,f253])).
% 0.21/0.53  fof(f357,plain,(
% 0.21/0.53    spl4_38 <=> m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.53  fof(f383,plain,(
% 0.21/0.53    k1_xboole_0 = u1_struct_0(sK0) | spl4_38),
% 0.21/0.53    inference(resolution,[],[f359,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(resolution,[],[f58,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.53  fof(f359,plain,(
% 0.21/0.53    ~m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) | spl4_38),
% 0.21/0.53    inference(avatar_component_clause,[],[f357])).
% 0.21/0.53  fof(f364,plain,(
% 0.21/0.53    spl4_3 | ~spl4_38 | ~spl4_1 | ~spl4_2 | spl4_39 | ~spl4_23),
% 0.21/0.53    inference(avatar_split_clause,[],[f353,f257,f361,f78,f73,f357,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl4_3 <=> v2_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    spl4_2 <=> v2_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    spl4_23 <=> k1_tarski(sK3(u1_struct_0(sK0))) = k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.53  fof(f353,plain,(
% 0.21/0.53    v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl4_23),
% 0.21/0.53    inference(superposition,[],[f54,f259])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    k1_tarski(sK3(u1_struct_0(sK0))) = k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) | ~spl4_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f257])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    spl4_22 | spl4_23 | spl4_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f251,f110,f257,f253])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl4_8 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.53  % (31944)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    k1_tarski(sK3(u1_struct_0(sK0))) = k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) | k1_xboole_0 = u1_struct_0(sK0) | spl4_8),
% 0.21/0.53    inference(resolution,[],[f195,f118])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0)) ) | spl4_8),
% 0.21/0.53    inference(resolution,[],[f62,f112])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f110])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  % (31938)Refutation not found, incomplete strategy% (31938)------------------------------
% 0.21/0.53  % (31938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31938)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31938)Memory used [KB]: 6140
% 0.21/0.53  % (31938)Time elapsed: 0.117 s
% 0.21/0.53  % (31938)------------------------------
% 0.21/0.53  % (31938)------------------------------
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    spl4_19 | ~spl4_4 | ~spl4_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f211,f207,f88,f223])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    spl4_4 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    spl4_18 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    v3_tex_2(k1_xboole_0,sK0) | (~spl4_4 | ~spl4_18)),
% 0.21/0.53    inference(backward_demodulation,[],[f90,f209])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl4_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f207])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    v3_tex_2(sK1,sK0) | ~spl4_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f88])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    spl4_18 | ~spl4_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f204,f98,f207])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    spl4_6 <=> v1_xboole_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl4_6),
% 0.21/0.53    inference(resolution,[],[f156,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0) ) | ~spl4_6),
% 0.21/0.53    inference(resolution,[],[f155,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | k1_xboole_0 = X0) ) | ~spl4_6),
% 0.21/0.53    inference(resolution,[],[f152,f58])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) ) | ~spl4_6),
% 0.21/0.53    inference(resolution,[],[f69,f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    v1_xboole_0(sK1) | ~spl4_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f98])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ~spl4_8 | ~spl4_9 | spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f108,f83,f114,f110])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ~l1_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0)) | spl4_3),
% 0.21/0.53    inference(resolution,[],[f55,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ~v2_struct_0(sK0) | spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f83])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    spl4_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f43,f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    spl4_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl4_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f98])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    v1_xboole_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f18])).
% 0.21/0.53  fof(f18,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl4_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f39,f88])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    v3_tex_2(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ~spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f40,f83])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f78])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    spl4_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f42,f73])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (31948)------------------------------
% 0.21/0.53  % (31948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31948)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (31948)Memory used [KB]: 6524
% 0.21/0.53  % (31948)Time elapsed: 0.117 s
% 0.21/0.53  % (31948)------------------------------
% 0.21/0.53  % (31948)------------------------------
% 0.21/0.53  % (31945)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (31953)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (31954)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (31951)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (31957)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (31959)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (31936)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.55  % (31932)Success in time 0.179 s
%------------------------------------------------------------------------------
