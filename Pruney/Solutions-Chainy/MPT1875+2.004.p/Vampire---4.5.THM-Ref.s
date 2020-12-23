%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:32 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 252 expanded)
%              Number of leaves         :   34 ( 104 expanded)
%              Depth                    :   13
%              Number of atoms          :  477 ( 868 expanded)
%              Number of equality atoms :   45 (  61 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f515,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f171,f178,f180,f193,f213,f233,f256,f293,f299,f306,f370,f514])).

fof(f514,plain,
    ( ~ spl6_1
    | ~ spl6_6
    | spl6_4
    | spl6_5
    | ~ spl6_15
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f513,f368,f175,f100,f95,f105,f80])).

fof(f80,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f105,plain,
    ( spl6_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f95,plain,
    ( spl6_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f100,plain,
    ( spl6_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f175,plain,
    ( spl6_15
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f368,plain,
    ( spl6_39
  <=> ! [X10] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10)))
        | v2_tex_2(sK1,X10)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(sK2(sK0,sK1),X10)
        | ~ l1_pre_topc(X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f513,plain,
    ( v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_15
    | ~ spl6_39 ),
    inference(resolution,[],[f369,f177])).

fof(f177,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f369,plain,
    ( ! [X10] :
        ( ~ m1_pre_topc(sK2(sK0,sK1),X10)
        | v2_tex_2(sK1,X10)
        | v2_struct_0(X10)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f368])).

fof(f370,plain,
    ( ~ spl6_26
    | spl6_13
    | spl6_39
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f321,f296,f368,f164,f303])).

fof(f303,plain,
    ( spl6_26
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f164,plain,
    ( spl6_13
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f296,plain,
    ( spl6_25
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f321,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10)
        | v2_struct_0(sK2(sK0,sK1))
        | ~ m1_pre_topc(sK2(sK0,sK1),X10)
        | v2_struct_0(X10)
        | ~ v1_tdlat_3(sK2(sK0,sK1))
        | v2_tex_2(sK1,X10) )
    | ~ spl6_25 ),
    inference(superposition,[],[f74,f298])).

fof(f298,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f296])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f306,plain,
    ( spl6_26
    | spl6_4
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f300,f175,f85,f80,f95,f303])).

fof(f85,plain,
    ( spl6_2
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f300,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl6_15 ),
    inference(resolution,[],[f177,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_tdlat_3(X1) ) ),
    inference(global_subsumption,[],[f48,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v1_tdlat_3(X1) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

% (21263)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (21264)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (21253)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (21254)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (21251)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (21236)Refutation not found, incomplete strategy% (21236)------------------------------
% (21236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21236)Termination reason: Refutation not found, incomplete strategy

% (21236)Memory used [KB]: 10874
% (21236)Time elapsed: 0.127 s
% (21236)------------------------------
% (21236)------------------------------
fof(f25,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f299,plain,
    ( spl6_25
    | spl6_4
    | spl6_14
    | ~ spl6_1
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f182,f105,f80,f168,f95,f296])).

fof(f168,plain,
    ( spl6_14
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f182,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl6_6 ),
    inference(resolution,[],[f52,f107])).

fof(f107,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f293,plain,
    ( ~ spl6_6
    | ~ spl6_9
    | spl6_22 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_9
    | spl6_22 ),
    inference(trivial_inequality_removal,[],[f290])).

fof(f290,plain,
    ( sK1 != sK1
    | ~ spl6_6
    | ~ spl6_9
    | spl6_22 ),
    inference(superposition,[],[f255,f288])).

fof(f288,plain,
    ( ! [X0] : sK1 = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f156,f270])).

fof(f270,plain,
    ( ! [X2,X3] : sK1 = k9_subset_1(X2,X3,sK1)
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f195,f237])).

fof(f237,plain,
    ( ! [X1] : sK1 = k3_xboole_0(X1,sK1)
    | ~ spl6_9 ),
    inference(superposition,[],[f185,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f185,plain,
    ( ! [X1] : sK1 = k3_xboole_0(sK1,X1)
    | ~ spl6_9 ),
    inference(resolution,[],[f181,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f181,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl6_9 ),
    inference(resolution,[],[f136,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f66,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f72,f77_D])).

fof(f77,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f77_D])).

fof(f77_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f136,plain,
    ( sP5(sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_9
  <=> sP5(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f195,plain,
    ( ! [X2,X3] : k9_subset_1(X2,X3,sK1) = k3_xboole_0(X3,sK1)
    | ~ spl6_9 ),
    inference(resolution,[],[f186,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f186,plain,
    ( ! [X2] : m1_subset_1(sK1,k1_zfmisc_1(X2))
    | ~ spl6_9 ),
    inference(resolution,[],[f181,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f156,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl6_6 ),
    inference(resolution,[],[f71,f107])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f255,plain,
    ( sK1 != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl6_22
  <=> sK1 = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f256,plain,
    ( spl6_5
    | spl6_4
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_22
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f251,f206,f105,f253,f90,f80,f95,f100])).

fof(f90,plain,
    ( spl6_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f206,plain,
    ( spl6_17
  <=> sK1 = sK3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f251,plain,
    ( sK1 != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0)
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f248,f208])).

fof(f208,plain,
    ( sK1 = sK3(sK0,sK1)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f206])).

fof(f248,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK3(sK0,sK1)))
    | v2_tex_2(sK1,sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f58,f107])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(f233,plain,
    ( ~ spl6_9
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl6_9
    | spl6_18 ),
    inference(resolution,[],[f212,f181])).

fof(f212,plain,
    ( ~ r1_tarski(sK1,sK3(sK0,sK1))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl6_18
  <=> r1_tarski(sK1,sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f213,plain,
    ( spl6_17
    | ~ spl6_18
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f202,f190,f210,f206])).

fof(f190,plain,
    ( spl6_16
  <=> r1_tarski(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f202,plain,
    ( ~ r1_tarski(sK1,sK3(sK0,sK1))
    | sK1 = sK3(sK0,sK1)
    | ~ spl6_16 ),
    inference(resolution,[],[f192,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f192,plain,
    ( r1_tarski(sK3(sK0,sK1),sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f193,plain,
    ( spl6_5
    | spl6_16
    | spl6_4
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f187,f105,f90,f80,f95,f190,f100])).

fof(f187,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_tarski(sK3(sK0,sK1),sK1)
    | v2_tex_2(sK1,sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f57,f107])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | r1_tarski(sK3(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f180,plain,
    ( spl6_9
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f179,f168,f134])).

fof(f179,plain,
    ( sP5(sK1)
    | ~ spl6_14 ),
    inference(resolution,[],[f170,f132])).

fof(f132,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sP5(X0) ) ),
    inference(resolution,[],[f77,f110])).

fof(f110,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f47,f46])).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f170,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f168])).

fof(f178,plain,
    ( spl6_15
    | spl6_4
    | spl6_14
    | ~ spl6_1
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f172,f105,f80,f168,f95,f175])).

fof(f172,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f51,f107])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f171,plain,
    ( ~ spl6_13
    | spl6_4
    | spl6_14
    | ~ spl6_1
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f161,f105,f80,f168,f95,f164])).

fof(f161,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl6_6 ),
    inference(resolution,[],[f50,f107])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f108,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f40,f105])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f103,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f41,f100])).

fof(f41,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f42,f95])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f93,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f44,f85])).

fof(f44,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f45,f80])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:16:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (21259)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.50  % (21234)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (21242)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (21250)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (21239)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (21242)Refutation not found, incomplete strategy% (21242)------------------------------
% 0.21/0.51  % (21242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21245)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (21240)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (21245)Refutation not found, incomplete strategy% (21245)------------------------------
% 0.21/0.51  % (21245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21245)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21245)Memory used [KB]: 10618
% 0.21/0.51  % (21245)Time elapsed: 0.104 s
% 0.21/0.51  % (21245)------------------------------
% 0.21/0.51  % (21245)------------------------------
% 1.20/0.52  % (21238)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.20/0.52  % (21250)Refutation found. Thanks to Tanya!
% 1.20/0.52  % SZS status Theorem for theBenchmark
% 1.20/0.52  % (21256)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.20/0.52  % (21241)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.20/0.52  % (21234)Refutation not found, incomplete strategy% (21234)------------------------------
% 1.20/0.52  % (21234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (21234)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (21234)Memory used [KB]: 1663
% 1.20/0.52  % (21234)Time elapsed: 0.002 s
% 1.20/0.52  % (21234)------------------------------
% 1.20/0.52  % (21234)------------------------------
% 1.20/0.52  % (21237)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.20/0.52  % (21236)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.52  % (21257)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.20/0.52  % (21235)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.20/0.53  % (21248)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.20/0.53  % (21261)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.20/0.53  % (21249)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.20/0.53  % (21246)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.53  % (21238)Refutation not found, incomplete strategy% (21238)------------------------------
% 1.20/0.53  % (21238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (21238)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (21238)Memory used [KB]: 6268
% 1.20/0.53  % (21238)Time elapsed: 0.116 s
% 1.20/0.53  % (21238)------------------------------
% 1.20/0.53  % (21238)------------------------------
% 1.20/0.53  % (21260)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.20/0.53  % (21242)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (21242)Memory used [KB]: 11001
% 1.20/0.53  % (21242)Time elapsed: 0.102 s
% 1.20/0.53  % (21242)------------------------------
% 1.20/0.53  % (21242)------------------------------
% 1.20/0.53  % SZS output start Proof for theBenchmark
% 1.20/0.53  fof(f515,plain,(
% 1.20/0.53    $false),
% 1.20/0.53    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f171,f178,f180,f193,f213,f233,f256,f293,f299,f306,f370,f514])).
% 1.20/0.53  fof(f514,plain,(
% 1.20/0.53    ~spl6_1 | ~spl6_6 | spl6_4 | spl6_5 | ~spl6_15 | ~spl6_39),
% 1.20/0.53    inference(avatar_split_clause,[],[f513,f368,f175,f100,f95,f105,f80])).
% 1.20/0.53  fof(f80,plain,(
% 1.20/0.53    spl6_1 <=> l1_pre_topc(sK0)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.20/0.53  fof(f105,plain,(
% 1.20/0.53    spl6_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.20/0.53  fof(f95,plain,(
% 1.20/0.53    spl6_4 <=> v2_struct_0(sK0)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.20/0.53  fof(f100,plain,(
% 1.20/0.53    spl6_5 <=> v2_tex_2(sK1,sK0)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.20/0.53  fof(f175,plain,(
% 1.20/0.53    spl6_15 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.20/0.53  fof(f368,plain,(
% 1.20/0.53    spl6_39 <=> ! [X10] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10))) | v2_tex_2(sK1,X10) | v2_struct_0(X10) | ~m1_pre_topc(sK2(sK0,sK1),X10) | ~l1_pre_topc(X10))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.20/0.53  fof(f513,plain,(
% 1.20/0.53    v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl6_15 | ~spl6_39)),
% 1.20/0.53    inference(resolution,[],[f369,f177])).
% 1.20/0.53  fof(f177,plain,(
% 1.20/0.53    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl6_15),
% 1.20/0.53    inference(avatar_component_clause,[],[f175])).
% 1.20/0.53  fof(f369,plain,(
% 1.20/0.53    ( ! [X10] : (~m1_pre_topc(sK2(sK0,sK1),X10) | v2_tex_2(sK1,X10) | v2_struct_0(X10) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10))) | ~l1_pre_topc(X10)) ) | ~spl6_39),
% 1.20/0.53    inference(avatar_component_clause,[],[f368])).
% 1.20/0.53  fof(f370,plain,(
% 1.20/0.53    ~spl6_26 | spl6_13 | spl6_39 | ~spl6_25),
% 1.20/0.53    inference(avatar_split_clause,[],[f321,f296,f368,f164,f303])).
% 1.20/0.53  fof(f303,plain,(
% 1.20/0.53    spl6_26 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.20/0.53  fof(f164,plain,(
% 1.20/0.53    spl6_13 <=> v2_struct_0(sK2(sK0,sK1))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.20/0.53  fof(f296,plain,(
% 1.20/0.53    spl6_25 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 1.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.20/0.53  fof(f321,plain,(
% 1.20/0.53    ( ! [X10] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10))) | ~l1_pre_topc(X10) | v2_struct_0(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X10) | v2_struct_0(X10) | ~v1_tdlat_3(sK2(sK0,sK1)) | v2_tex_2(sK1,X10)) ) | ~spl6_25),
% 1.20/0.53    inference(superposition,[],[f74,f298])).
% 1.20/0.53  fof(f298,plain,(
% 1.20/0.53    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl6_25),
% 1.20/0.53    inference(avatar_component_clause,[],[f296])).
% 1.35/0.53  fof(f74,plain,(
% 1.35/0.53    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 1.35/0.53    inference(equality_resolution,[],[f53])).
% 1.35/0.53  fof(f53,plain,(
% 1.35/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f30])).
% 1.35/0.53  fof(f30,plain,(
% 1.35/0.53    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.53    inference(flattening,[],[f29])).
% 1.35/0.53  fof(f29,plain,(
% 1.35/0.53    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.53    inference(ennf_transformation,[],[f15])).
% 1.35/0.53  fof(f15,axiom,(
% 1.35/0.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 1.35/0.53  fof(f306,plain,(
% 1.35/0.53    spl6_26 | spl6_4 | ~spl6_1 | ~spl6_2 | ~spl6_15),
% 1.35/0.53    inference(avatar_split_clause,[],[f300,f175,f85,f80,f95,f303])).
% 1.35/0.53  fof(f85,plain,(
% 1.35/0.53    spl6_2 <=> v1_tdlat_3(sK0)),
% 1.35/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.35/0.53  fof(f300,plain,(
% 1.35/0.53    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_tdlat_3(sK2(sK0,sK1)) | ~spl6_15),
% 1.35/0.53    inference(resolution,[],[f177,f109])).
% 1.35/0.53  fof(f109,plain,(
% 1.35/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_tdlat_3(X1)) )),
% 1.35/0.53    inference(global_subsumption,[],[f48,f59])).
% 1.35/0.53  fof(f59,plain,(
% 1.35/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_tdlat_3(X1)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f34])).
% 1.35/0.53  fof(f34,plain,(
% 1.35/0.53    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.53    inference(flattening,[],[f33])).
% 1.35/0.53  fof(f33,plain,(
% 1.35/0.53    ! [X0] : (! [X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.53    inference(ennf_transformation,[],[f21])).
% 1.35/0.53  fof(f21,plain,(
% 1.35/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v1_tdlat_3(X1)))),
% 1.35/0.53    inference(pure_predicate_removal,[],[f20])).
% 1.35/0.53  fof(f20,plain,(
% 1.35/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 1.35/0.53    inference(pure_predicate_removal,[],[f13])).
% 1.35/0.53  fof(f13,axiom,(
% 1.35/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 1.35/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 1.35/0.53  fof(f48,plain,(
% 1.35/0.53    ( ! [X0] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 1.35/0.53    inference(cnf_transformation,[],[f25])).
% 1.35/0.53  % (21263)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.53  % (21264)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.53  % (21253)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.53  % (21254)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.54  % (21251)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.54  % (21236)Refutation not found, incomplete strategy% (21236)------------------------------
% 1.35/0.54  % (21236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (21236)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (21236)Memory used [KB]: 10874
% 1.35/0.54  % (21236)Time elapsed: 0.127 s
% 1.35/0.54  % (21236)------------------------------
% 1.35/0.54  % (21236)------------------------------
% 1.35/0.54  fof(f25,plain,(
% 1.35/0.54    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.35/0.54    inference(flattening,[],[f24])).
% 1.35/0.54  fof(f24,plain,(
% 1.35/0.54    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.35/0.54    inference(ennf_transformation,[],[f12])).
% 1.35/0.54  fof(f12,axiom,(
% 1.35/0.54    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 1.35/0.54  fof(f299,plain,(
% 1.35/0.54    spl6_25 | spl6_4 | spl6_14 | ~spl6_1 | ~spl6_6),
% 1.35/0.54    inference(avatar_split_clause,[],[f182,f105,f80,f168,f95,f296])).
% 1.35/0.54  fof(f168,plain,(
% 1.35/0.54    spl6_14 <=> v1_xboole_0(sK1)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.35/0.54  fof(f182,plain,(
% 1.35/0.54    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl6_6),
% 1.35/0.54    inference(resolution,[],[f52,f107])).
% 1.35/0.54  fof(f107,plain,(
% 1.35/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_6),
% 1.35/0.54    inference(avatar_component_clause,[],[f105])).
% 1.35/0.54  fof(f52,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 1.35/0.54    inference(cnf_transformation,[],[f28])).
% 1.35/0.54  fof(f28,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f27])).
% 1.35/0.54  fof(f27,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f19])).
% 1.35/0.54  fof(f19,plain,(
% 1.35/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 1.35/0.54    inference(pure_predicate_removal,[],[f14])).
% 1.35/0.54  fof(f14,axiom,(
% 1.35/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 1.35/0.54  fof(f293,plain,(
% 1.35/0.54    ~spl6_6 | ~spl6_9 | spl6_22),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f292])).
% 1.35/0.54  fof(f292,plain,(
% 1.35/0.54    $false | (~spl6_6 | ~spl6_9 | spl6_22)),
% 1.35/0.54    inference(trivial_inequality_removal,[],[f290])).
% 1.35/0.54  fof(f290,plain,(
% 1.35/0.54    sK1 != sK1 | (~spl6_6 | ~spl6_9 | spl6_22)),
% 1.35/0.54    inference(superposition,[],[f255,f288])).
% 1.35/0.54  fof(f288,plain,(
% 1.35/0.54    ( ! [X0] : (sK1 = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | (~spl6_6 | ~spl6_9)),
% 1.35/0.54    inference(forward_demodulation,[],[f156,f270])).
% 1.35/0.54  fof(f270,plain,(
% 1.35/0.54    ( ! [X2,X3] : (sK1 = k9_subset_1(X2,X3,sK1)) ) | ~spl6_9),
% 1.35/0.54    inference(forward_demodulation,[],[f195,f237])).
% 1.35/0.54  fof(f237,plain,(
% 1.35/0.54    ( ! [X1] : (sK1 = k3_xboole_0(X1,sK1)) ) | ~spl6_9),
% 1.35/0.54    inference(superposition,[],[f185,f60])).
% 1.35/0.54  fof(f60,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f1])).
% 1.35/0.54  fof(f1,axiom,(
% 1.35/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.35/0.54  fof(f185,plain,(
% 1.35/0.54    ( ! [X1] : (sK1 = k3_xboole_0(sK1,X1)) ) | ~spl6_9),
% 1.35/0.54    inference(resolution,[],[f181,f61])).
% 1.35/0.54  fof(f61,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.35/0.54    inference(cnf_transformation,[],[f35])).
% 1.35/0.54  fof(f35,plain,(
% 1.35/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.35/0.54    inference(ennf_transformation,[],[f4])).
% 1.35/0.54  fof(f4,axiom,(
% 1.35/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.35/0.54  fof(f181,plain,(
% 1.35/0.54    ( ! [X0] : (r1_tarski(sK1,X0)) ) | ~spl6_9),
% 1.35/0.54    inference(resolution,[],[f136,f128])).
% 1.35/0.54  fof(f128,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~sP5(X0) | r1_tarski(X0,X1)) )),
% 1.35/0.54    inference(resolution,[],[f66,f78])).
% 1.35/0.54  fof(f78,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP5(X1)) )),
% 1.35/0.54    inference(general_splitting,[],[f72,f77_D])).
% 1.35/0.54  fof(f77,plain,(
% 1.35/0.54    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP5(X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f77_D])).
% 1.35/0.54  fof(f77_D,plain,(
% 1.35/0.54    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP5(X1)) )),
% 1.35/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.35/0.54  fof(f72,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f39])).
% 1.35/0.54  fof(f39,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.35/0.54    inference(ennf_transformation,[],[f10])).
% 1.35/0.54  fof(f10,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.35/0.54  fof(f66,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f36])).
% 1.35/0.54  fof(f36,plain,(
% 1.35/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f2])).
% 1.35/0.54  fof(f2,axiom,(
% 1.35/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.35/0.54  fof(f136,plain,(
% 1.35/0.54    sP5(sK1) | ~spl6_9),
% 1.35/0.54    inference(avatar_component_clause,[],[f134])).
% 1.35/0.54  fof(f134,plain,(
% 1.35/0.54    spl6_9 <=> sP5(sK1)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.35/0.54  fof(f195,plain,(
% 1.35/0.54    ( ! [X2,X3] : (k9_subset_1(X2,X3,sK1) = k3_xboole_0(X3,sK1)) ) | ~spl6_9),
% 1.35/0.54    inference(resolution,[],[f186,f70])).
% 1.35/0.54  fof(f70,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f37])).
% 1.35/0.54  fof(f37,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f8])).
% 1.35/0.54  fof(f8,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.35/0.54  fof(f186,plain,(
% 1.35/0.54    ( ! [X2] : (m1_subset_1(sK1,k1_zfmisc_1(X2))) ) | ~spl6_9),
% 1.35/0.54    inference(resolution,[],[f181,f68])).
% 1.35/0.54  fof(f68,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f9])).
% 1.35/0.54  fof(f9,axiom,(
% 1.35/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.35/0.54  fof(f156,plain,(
% 1.35/0.54    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl6_6),
% 1.35/0.54    inference(resolution,[],[f71,f107])).
% 1.35/0.54  fof(f71,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f38])).
% 1.35/0.54  fof(f38,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f5])).
% 1.35/0.54  fof(f5,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 1.35/0.54  fof(f255,plain,(
% 1.35/0.54    sK1 != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1)) | spl6_22),
% 1.35/0.54    inference(avatar_component_clause,[],[f253])).
% 1.35/0.54  fof(f253,plain,(
% 1.35/0.54    spl6_22 <=> sK1 = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.35/0.54  fof(f256,plain,(
% 1.35/0.54    spl6_5 | spl6_4 | ~spl6_1 | ~spl6_3 | ~spl6_22 | ~spl6_6 | ~spl6_17),
% 1.35/0.54    inference(avatar_split_clause,[],[f251,f206,f105,f253,f90,f80,f95,f100])).
% 1.35/0.54  fof(f90,plain,(
% 1.35/0.54    spl6_3 <=> v2_pre_topc(sK0)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.35/0.54  fof(f206,plain,(
% 1.35/0.54    spl6_17 <=> sK1 = sK3(sK0,sK1)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.35/0.54  fof(f251,plain,(
% 1.35/0.54    sK1 != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0) | (~spl6_6 | ~spl6_17)),
% 1.35/0.54    inference(forward_demodulation,[],[f248,f208])).
% 1.35/0.54  fof(f208,plain,(
% 1.35/0.54    sK1 = sK3(sK0,sK1) | ~spl6_17),
% 1.35/0.54    inference(avatar_component_clause,[],[f206])).
% 1.35/0.54  fof(f248,plain,(
% 1.35/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | sK3(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK3(sK0,sK1))) | v2_tex_2(sK1,sK0) | ~spl6_6),
% 1.35/0.54    inference(resolution,[],[f58,f107])).
% 1.35/0.54  fof(f58,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) | v2_tex_2(X1,X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f32])).
% 1.35/0.54  fof(f32,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f31])).
% 1.35/0.54  fof(f31,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f16])).
% 1.35/0.54  fof(f16,axiom,(
% 1.35/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 1.35/0.54  fof(f233,plain,(
% 1.35/0.54    ~spl6_9 | spl6_18),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f232])).
% 1.35/0.54  fof(f232,plain,(
% 1.35/0.54    $false | (~spl6_9 | spl6_18)),
% 1.35/0.54    inference(resolution,[],[f212,f181])).
% 1.35/0.54  fof(f212,plain,(
% 1.35/0.54    ~r1_tarski(sK1,sK3(sK0,sK1)) | spl6_18),
% 1.35/0.54    inference(avatar_component_clause,[],[f210])).
% 1.35/0.54  fof(f210,plain,(
% 1.35/0.54    spl6_18 <=> r1_tarski(sK1,sK3(sK0,sK1))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.35/0.54  fof(f213,plain,(
% 1.35/0.54    spl6_17 | ~spl6_18 | ~spl6_16),
% 1.35/0.54    inference(avatar_split_clause,[],[f202,f190,f210,f206])).
% 1.35/0.54  fof(f190,plain,(
% 1.35/0.54    spl6_16 <=> r1_tarski(sK3(sK0,sK1),sK1)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.35/0.54  fof(f202,plain,(
% 1.35/0.54    ~r1_tarski(sK1,sK3(sK0,sK1)) | sK1 = sK3(sK0,sK1) | ~spl6_16),
% 1.35/0.54    inference(resolution,[],[f192,f64])).
% 1.35/0.54  fof(f64,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.35/0.54    inference(cnf_transformation,[],[f3])).
% 1.35/0.54  fof(f3,axiom,(
% 1.35/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.35/0.54  fof(f192,plain,(
% 1.35/0.54    r1_tarski(sK3(sK0,sK1),sK1) | ~spl6_16),
% 1.35/0.54    inference(avatar_component_clause,[],[f190])).
% 1.35/0.54  fof(f193,plain,(
% 1.35/0.54    spl6_5 | spl6_16 | spl6_4 | ~spl6_1 | ~spl6_3 | ~spl6_6),
% 1.35/0.54    inference(avatar_split_clause,[],[f187,f105,f90,f80,f95,f190,f100])).
% 1.35/0.54  fof(f187,plain,(
% 1.35/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | r1_tarski(sK3(sK0,sK1),sK1) | v2_tex_2(sK1,sK0) | ~spl6_6),
% 1.35/0.54    inference(resolution,[],[f57,f107])).
% 1.35/0.54  fof(f57,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | r1_tarski(sK3(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f32])).
% 1.35/0.54  fof(f180,plain,(
% 1.35/0.54    spl6_9 | ~spl6_14),
% 1.35/0.54    inference(avatar_split_clause,[],[f179,f168,f134])).
% 1.35/0.54  fof(f179,plain,(
% 1.35/0.54    sP5(sK1) | ~spl6_14),
% 1.35/0.54    inference(resolution,[],[f170,f132])).
% 1.35/0.54  fof(f132,plain,(
% 1.35/0.54    ( ! [X0] : (~v1_xboole_0(X0) | sP5(X0)) )),
% 1.35/0.54    inference(resolution,[],[f77,f110])).
% 1.35/0.54  fof(f110,plain,(
% 1.35/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.35/0.54    inference(forward_demodulation,[],[f47,f46])).
% 1.35/0.54  fof(f46,plain,(
% 1.35/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.35/0.54    inference(cnf_transformation,[],[f6])).
% 1.35/0.54  fof(f6,axiom,(
% 1.35/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.35/0.54  fof(f47,plain,(
% 1.35/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f7])).
% 1.35/0.54  fof(f7,axiom,(
% 1.35/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.35/0.54  fof(f170,plain,(
% 1.35/0.54    v1_xboole_0(sK1) | ~spl6_14),
% 1.35/0.54    inference(avatar_component_clause,[],[f168])).
% 1.35/0.54  fof(f178,plain,(
% 1.35/0.54    spl6_15 | spl6_4 | spl6_14 | ~spl6_1 | ~spl6_6),
% 1.35/0.54    inference(avatar_split_clause,[],[f172,f105,f80,f168,f95,f175])).
% 1.35/0.54  fof(f172,plain,(
% 1.35/0.54    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl6_6),
% 1.35/0.54    inference(resolution,[],[f51,f107])).
% 1.35/0.54  fof(f51,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f28])).
% 1.35/0.54  fof(f171,plain,(
% 1.35/0.54    ~spl6_13 | spl6_4 | spl6_14 | ~spl6_1 | ~spl6_6),
% 1.35/0.54    inference(avatar_split_clause,[],[f161,f105,f80,f168,f95,f164])).
% 1.35/0.54  fof(f161,plain,(
% 1.35/0.54    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_struct_0(sK2(sK0,sK1)) | ~spl6_6),
% 1.35/0.54    inference(resolution,[],[f50,f107])).
% 1.35/0.54  fof(f50,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_struct_0(sK2(X0,X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f28])).
% 1.35/0.54  fof(f108,plain,(
% 1.35/0.54    spl6_6),
% 1.35/0.54    inference(avatar_split_clause,[],[f40,f105])).
% 1.35/0.54  fof(f40,plain,(
% 1.35/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.35/0.54    inference(cnf_transformation,[],[f23])).
% 1.35/0.54  fof(f23,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f22])).
% 1.35/0.54  fof(f22,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f18])).
% 1.35/0.54  fof(f18,negated_conjecture,(
% 1.35/0.54    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.35/0.54    inference(negated_conjecture,[],[f17])).
% 1.35/0.54  fof(f17,conjecture,(
% 1.35/0.54    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 1.35/0.54  fof(f103,plain,(
% 1.35/0.54    ~spl6_5),
% 1.35/0.54    inference(avatar_split_clause,[],[f41,f100])).
% 1.35/0.54  fof(f41,plain,(
% 1.35/0.54    ~v2_tex_2(sK1,sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f23])).
% 1.35/0.54  fof(f98,plain,(
% 1.35/0.54    ~spl6_4),
% 1.35/0.54    inference(avatar_split_clause,[],[f42,f95])).
% 1.35/0.54  fof(f42,plain,(
% 1.35/0.54    ~v2_struct_0(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f23])).
% 1.35/0.54  fof(f93,plain,(
% 1.35/0.54    spl6_3),
% 1.35/0.54    inference(avatar_split_clause,[],[f43,f90])).
% 1.35/0.54  fof(f43,plain,(
% 1.35/0.54    v2_pre_topc(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f23])).
% 1.35/0.54  fof(f88,plain,(
% 1.35/0.54    spl6_2),
% 1.35/0.54    inference(avatar_split_clause,[],[f44,f85])).
% 1.35/0.54  fof(f44,plain,(
% 1.35/0.54    v1_tdlat_3(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f23])).
% 1.35/0.54  fof(f83,plain,(
% 1.35/0.54    spl6_1),
% 1.35/0.54    inference(avatar_split_clause,[],[f45,f80])).
% 1.35/0.54  fof(f45,plain,(
% 1.35/0.54    l1_pre_topc(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f23])).
% 1.35/0.54  % SZS output end Proof for theBenchmark
% 1.35/0.54  % (21250)------------------------------
% 1.35/0.54  % (21250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (21250)Termination reason: Refutation
% 1.35/0.54  
% 1.35/0.54  % (21250)Memory used [KB]: 11001
% 1.35/0.54  % (21250)Time elapsed: 0.113 s
% 1.35/0.54  % (21250)------------------------------
% 1.35/0.54  % (21250)------------------------------
% 1.35/0.54  % (21232)Success in time 0.181 s
%------------------------------------------------------------------------------
