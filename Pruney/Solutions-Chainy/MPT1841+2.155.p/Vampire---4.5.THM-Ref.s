%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 161 expanded)
%              Number of leaves         :   27 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  250 ( 424 expanded)
%              Number of equality atoms :   50 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30773)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f89,f94,f101,f107,f115,f132,f144])).

fof(f144,plain,(
    ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl2_12 ),
    inference(resolution,[],[f131,f82])).

fof(f82,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(global_subsumption,[],[f41,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f80,f77])).

fof(f77,plain,(
    ! [X0] : k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(forward_demodulation,[],[f76,f42])).

fof(f42,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f76,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f74,f41])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f73,f45])).

% (30752)Termination reason: Refutation not found, incomplete strategy
fof(f73,plain,(
    ! [X0] :
      ( ~ l1_struct_0(k2_yellow_1(X0))
      | ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0) ) ),
    inference(superposition,[],[f46,f42])).

% (30752)Memory used [KB]: 10746
fof(f46,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

% (30752)Time elapsed: 0.124 s
% (30752)------------------------------
% (30752)------------------------------
fof(f24,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f41,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f131,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl2_12
  <=> v1_subset_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f132,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f121,f113,f62,f130])).

% (30751)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f62,plain,
    ( spl2_2
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f113,plain,
    ( spl2_9
  <=> sK0 = k6_domain_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f121,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f63,f114])).

fof(f114,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f63,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f115,plain,
    ( spl2_8
    | spl2_9
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f110,f92,f66,f113,f105])).

fof(f105,plain,
    ( spl2_8
  <=> k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f66,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f92,plain,
    ( spl2_6
  <=> ! [X0] :
        ( v1_xboole_0(k6_domain_1(sK0,X0))
        | ~ m1_subset_1(X0,sK0)
        | sK0 = k6_domain_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f110,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | k1_xboole_0 = k6_domain_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f109,f67])).

fof(f67,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | sK0 = k6_domain_1(sK0,X0)
        | k1_xboole_0 = k6_domain_1(sK0,X0) )
    | ~ spl2_6 ),
    inference(resolution,[],[f93,f48])).

% (30766)Refutation not found, incomplete strategy% (30766)------------------------------
% (30766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f93,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_domain_1(sK0,X0))
        | ~ m1_subset_1(X0,sK0)
        | sK0 = k6_domain_1(sK0,X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f107,plain,
    ( ~ spl2_8
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f102,f99,f105])).

fof(f99,plain,
    ( spl2_7
  <=> k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f102,plain,
    ( k1_xboole_0 != k6_domain_1(sK0,sK1)
    | ~ spl2_7 ),
    inference(superposition,[],[f75,f100])).

fof(f100,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f55,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f55,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f101,plain,
    ( spl2_7
    | ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f97,f70,f66,f99])).

fof(f70,plain,
    ( spl2_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f97,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | ~ spl2_3
    | spl2_4 ),
    inference(resolution,[],[f95,f67])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k1_enumset1(X0,X0,X0) = k6_domain_1(sK0,X0) )
    | spl2_4 ),
    inference(resolution,[],[f56,f71])).

fof(f71,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f94,plain,
    ( spl2_4
    | spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f90,f87,f92,f70])).

fof(f87,plain,
    ( spl2_5
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_xboole_0(X0)
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f90,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_domain_1(sK0,X0))
        | sK0 = k6_domain_1(sK0,X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl2_5 ),
    inference(resolution,[],[f88,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_domain_1(X1,X0),X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_xboole_0(X0)
        | sK0 = X0 )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( spl2_4
    | spl2_5
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f84,f58,f87,f70])).

fof(f58,plain,
    ( spl2_1
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | sK0 = X0
        | v1_xboole_0(sK0)
        | v1_xboole_0(X0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f44,f59])).

fof(f59,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f72,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f68,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f37,f62])).

fof(f37,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f38,f58])).

fof(f38,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (30765)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (30748)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (30755)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (30755)Refutation not found, incomplete strategy% (30755)------------------------------
% 0.21/0.50  % (30755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30755)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30755)Memory used [KB]: 10618
% 0.21/0.50  % (30755)Time elapsed: 0.111 s
% 0.21/0.50  % (30755)------------------------------
% 0.21/0.50  % (30755)------------------------------
% 0.21/0.50  % (30757)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (30744)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (30754)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (30766)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (30747)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (30744)Refutation not found, incomplete strategy% (30744)------------------------------
% 0.21/0.51  % (30744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30758)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (30749)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (30748)Refutation not found, incomplete strategy% (30748)------------------------------
% 0.21/0.52  % (30748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30748)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30748)Memory used [KB]: 6268
% 0.21/0.52  % (30748)Time elapsed: 0.113 s
% 0.21/0.52  % (30748)------------------------------
% 0.21/0.52  % (30748)------------------------------
% 0.21/0.52  % (30771)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (30753)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (30763)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (30744)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30744)Memory used [KB]: 1663
% 0.21/0.52  % (30744)Time elapsed: 0.117 s
% 0.21/0.52  % (30744)------------------------------
% 0.21/0.52  % (30744)------------------------------
% 0.21/0.52  % (30752)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (30767)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (30754)Refutation not found, incomplete strategy% (30754)------------------------------
% 0.21/0.52  % (30754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30754)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.53  % (30754)Memory used [KB]: 10618
% 0.21/0.53  % (30754)Time elapsed: 0.124 s
% 0.21/0.53  % (30754)------------------------------
% 0.21/0.53  % (30754)------------------------------
% 0.21/0.53  % (30752)Refutation not found, incomplete strategy% (30752)------------------------------
% 0.21/0.53  % (30752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30763)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (30750)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  % (30773)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f89,f94,f101,f107,f115,f132,f144])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ~spl2_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f142])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    $false | ~spl2_12),
% 0.21/0.53    inference(resolution,[],[f131,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.21/0.53    inference(global_subsumption,[],[f41,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_subset_1(X0,X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f80,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0] : (k2_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f76,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(resolution,[],[f74,f41])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_orders_2(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(resolution,[],[f47,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(resolution,[],[f73,f45])).
% 0.21/0.53  % (30752)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(k2_yellow_1(X0)) | ~v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0)) )),
% 0.21/0.53    inference(superposition,[],[f46,f42])).
% 0.21/0.53  
% 0.21/0.53  % (30752)Memory used [KB]: 10746
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  % (30752)Time elapsed: 0.124 s
% 0.21/0.53  % (30752)------------------------------
% 0.21/0.53  % (30752)------------------------------
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    v1_subset_1(sK0,sK0) | ~spl2_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f130])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    spl2_12 <=> v1_subset_1(sK0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    spl2_12 | ~spl2_2 | ~spl2_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f121,f113,f62,f130])).
% 0.21/0.53  % (30751)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    spl2_2 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl2_9 <=> sK0 = k6_domain_1(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    v1_subset_1(sK0,sK0) | (~spl2_2 | ~spl2_9)),
% 0.21/0.53    inference(superposition,[],[f63,f114])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    sK0 = k6_domain_1(sK0,sK1) | ~spl2_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f62])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    spl2_8 | spl2_9 | ~spl2_3 | ~spl2_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f110,f92,f66,f113,f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl2_8 <=> k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl2_6 <=> ! [X0] : (v1_xboole_0(k6_domain_1(sK0,X0)) | ~m1_subset_1(X0,sK0) | sK0 = k6_domain_1(sK0,X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    sK0 = k6_domain_1(sK0,sK1) | k1_xboole_0 = k6_domain_1(sK0,sK1) | (~spl2_3 | ~spl2_6)),
% 0.21/0.53    inference(resolution,[],[f109,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f66])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,sK0) | sK0 = k6_domain_1(sK0,X0) | k1_xboole_0 = k6_domain_1(sK0,X0)) ) | ~spl2_6),
% 0.21/0.53    inference(resolution,[],[f93,f48])).
% 0.21/0.53  % (30766)Refutation not found, incomplete strategy% (30766)------------------------------
% 0.21/0.53  % (30766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X0] : (v1_xboole_0(k6_domain_1(sK0,X0)) | ~m1_subset_1(X0,sK0) | sK0 = k6_domain_1(sK0,X0)) ) | ~spl2_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f92])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ~spl2_8 | ~spl2_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f102,f99,f105])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl2_7 <=> k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    k1_xboole_0 != k6_domain_1(sK0,sK1) | ~spl2_7),
% 0.21/0.53    inference(superposition,[],[f75,f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | ~spl2_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f99])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 0.21/0.53    inference(superposition,[],[f55,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f49,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl2_7 | ~spl2_3 | spl2_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f97,f70,f66,f99])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    spl2_4 <=> v1_xboole_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | (~spl2_3 | spl2_4)),
% 0.21/0.53    inference(resolution,[],[f95,f67])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,sK0) | k1_enumset1(X0,X0,X0) = k6_domain_1(sK0,X0)) ) | spl2_4),
% 0.21/0.53    inference(resolution,[],[f56,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ~v1_xboole_0(sK0) | spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f70])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f51,f54])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl2_4 | spl2_6 | ~spl2_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f90,f87,f92,f70])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl2_5 <=> ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X0] : (v1_xboole_0(k6_domain_1(sK0,X0)) | sK0 = k6_domain_1(sK0,X0) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0)) ) | ~spl2_5),
% 0.21/0.53    inference(resolution,[],[f88,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k6_domain_1(X1,X0),X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f52,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.53    inference(unused_predicate_definition_removal,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0) ) | ~spl2_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f87])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    spl2_4 | spl2_5 | ~spl2_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f84,f58,f87,f70])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    spl2_1 <=> v1_zfmisc_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) ) | ~spl2_1),
% 0.21/0.53    inference(resolution,[],[f44,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    v1_zfmisc_1(sK0) | ~spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f58])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ~spl2_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f70])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ~v1_xboole_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f33,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.53    inference(negated_conjecture,[],[f15])).
% 0.21/0.53  fof(f15,conjecture,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f66])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    m1_subset_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f62])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    spl2_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f38,f58])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    v1_zfmisc_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (30763)------------------------------
% 0.21/0.53  % (30763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30745)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (30763)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (30763)Memory used [KB]: 10746
% 0.21/0.53  % (30763)Time elapsed: 0.135 s
% 0.21/0.53  % (30763)------------------------------
% 0.21/0.53  % (30763)------------------------------
% 0.21/0.53  % (30761)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (30743)Success in time 0.175 s
%------------------------------------------------------------------------------
