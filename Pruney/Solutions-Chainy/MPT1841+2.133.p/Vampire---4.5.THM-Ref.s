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
% DateTime   : Thu Dec  3 13:20:27 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 209 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  301 ( 654 expanded)
%              Number of equality atoms :   55 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f141,f207,f210,f245,f261])).

% (21822)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f261,plain,(
    ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl3_9 ),
    inference(resolution,[],[f259,f51])).

fof(f51,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f259,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl3_9 ),
    inference(resolution,[],[f256,f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f256,plain,
    ( ~ l1_struct_0(k2_yellow_1(sK0))
    | ~ spl3_9 ),
    inference(resolution,[],[f247,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,X0)
      | ~ l1_struct_0(k2_yellow_1(X0)) ) ),
    inference(backward_demodulation,[],[f76,f80])).

fof(f80,plain,(
    ! [X0] : k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(forward_demodulation,[],[f79,f52])).

fof(f52,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f79,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f77,f51])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f57,f55])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0)
      | ~ l1_struct_0(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f56,f52])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f247,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f160,f203])).

fof(f203,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl3_9
  <=> sK0 = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f160,plain,(
    v1_subset_1(k2_tarski(sK1,sK1),sK0) ),
    inference(backward_demodulation,[],[f45,f159])).

fof(f159,plain,(
    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) ),
    inference(resolution,[],[f157,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k2_tarski(X0,X0) = k6_domain_1(sK0,X0) ) ),
    inference(resolution,[],[f73,f43])).

fof(f43,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f60,f49])).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f45,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f245,plain,(
    ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f242])).

fof(f242,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_10 ),
    inference(superposition,[],[f112,f214])).

fof(f214,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl3_10 ),
    inference(resolution,[],[f206,f74])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

% (21823)Refutation not found, incomplete strategy% (21823)------------------------------
% (21823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21823)Termination reason: Refutation not found, incomplete strategy

% (21823)Memory used [KB]: 10746
% (21823)Time elapsed: 0.112 s
% (21823)------------------------------
% (21823)------------------------------
fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f206,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k2_tarski(sK1,sK1))
        | k1_xboole_0 = X2 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl3_10
  <=> ! [X2] :
        ( ~ r1_tarski(X2,k2_tarski(sK1,sK1))
        | k1_xboole_0 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 != k2_tarski(X0,X0) ),
    inference(superposition,[],[f72,f71])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f72,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(X1,k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f58,f59,f49])).

fof(f58,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f210,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl3_5 ),
    inference(resolution,[],[f137,f43])).

fof(f137,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f207,plain,
    ( spl3_9
    | spl3_10
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f195,f139,f122,f205,f201])).

fof(f122,plain,
    ( spl3_4
  <=> r1_tarski(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f139,plain,
    ( spl3_6
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_xboole_0(X0)
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f195,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k2_tarski(sK1,sK1))
        | sK0 = k2_tarski(sK1,sK1)
        | k1_xboole_0 = X2 )
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f154,f163])).

fof(f163,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),sK0)
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f123,f159])).

fof(f123,plain,
    ( r1_tarski(k6_domain_1(sK0,sK1),sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f154,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X3,sK0)
        | ~ r1_tarski(X4,X3)
        | sK0 = X3
        | k1_xboole_0 = X4 )
    | ~ spl3_6 ),
    inference(resolution,[],[f151,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f64,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f151,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X1,X2)
        | sK0 = X0
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_6 ),
    inference(resolution,[],[f149,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

% (21839)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f149,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,X2)
        | ~ r1_tarski(X0,sK0)
        | sK0 = X0
        | ~ r1_tarski(X2,X0) )
    | ~ spl3_6 ),
    inference(resolution,[],[f143,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | sK0 = X0
        | ~ r1_tarski(X0,sK0)
        | ~ r2_hidden(X2,X1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f140,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f140,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ r1_tarski(X0,sK0)
        | sK0 = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,
    ( spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f133,f139,f135])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f54,f46])).

fof(f46,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f131,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f128,f44])).

% (21845)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f128,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | spl3_4 ),
    inference(resolution,[],[f124,f93])).

% (21815)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f93,plain,(
    ! [X0] :
      ( r1_tarski(k6_domain_1(sK0,X0),sK0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f92,f43])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r1_tarski(k6_domain_1(X1,X0),X1) ) ),
    inference(resolution,[],[f61,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f124,plain,
    ( ~ r1_tarski(k6_domain_1(sK0,sK1),sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (21825)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (21816)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (21825)Refutation not found, incomplete strategy% (21825)------------------------------
% 0.21/0.50  % (21825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21825)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21825)Memory used [KB]: 10618
% 0.21/0.50  % (21825)Time elapsed: 0.109 s
% 0.21/0.50  % (21825)------------------------------
% 0.21/0.50  % (21825)------------------------------
% 0.21/0.50  % (21818)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (21816)Refutation not found, incomplete strategy% (21816)------------------------------
% 0.21/0.51  % (21816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21816)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21816)Memory used [KB]: 10746
% 0.21/0.51  % (21816)Time elapsed: 0.110 s
% 0.21/0.51  % (21816)------------------------------
% 0.21/0.51  % (21816)------------------------------
% 0.21/0.51  % (21827)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21834)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.24/0.51  % (21830)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.52  % (21826)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.52  % (21836)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.24/0.52  % (21826)Refutation not found, incomplete strategy% (21826)------------------------------
% 1.24/0.52  % (21826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (21826)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (21826)Memory used [KB]: 10618
% 1.24/0.52  % (21826)Time elapsed: 0.111 s
% 1.24/0.52  % (21826)------------------------------
% 1.24/0.52  % (21826)------------------------------
% 1.24/0.52  % (21819)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.52  % (21814)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.52  % (21820)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.52  % (21823)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.52  % (21827)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % SZS output start Proof for theBenchmark
% 1.24/0.52  fof(f262,plain,(
% 1.24/0.52    $false),
% 1.24/0.52    inference(avatar_sat_refutation,[],[f131,f141,f207,f210,f245,f261])).
% 1.24/0.52  % (21822)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.52  fof(f261,plain,(
% 1.24/0.52    ~spl3_9),
% 1.24/0.52    inference(avatar_contradiction_clause,[],[f260])).
% 1.24/0.52  fof(f260,plain,(
% 1.24/0.52    $false | ~spl3_9),
% 1.24/0.52    inference(resolution,[],[f259,f51])).
% 1.24/0.52  fof(f51,plain,(
% 1.24/0.52    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f15])).
% 1.24/0.52  fof(f15,axiom,(
% 1.24/0.52    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 1.24/0.52  fof(f259,plain,(
% 1.24/0.52    ~l1_orders_2(k2_yellow_1(sK0)) | ~spl3_9),
% 1.24/0.52    inference(resolution,[],[f256,f55])).
% 1.24/0.52  fof(f55,plain,(
% 1.24/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f24])).
% 1.24/0.52  fof(f24,plain,(
% 1.24/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.24/0.52    inference(ennf_transformation,[],[f13])).
% 1.24/0.52  fof(f13,axiom,(
% 1.24/0.52    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.24/0.52  fof(f256,plain,(
% 1.24/0.52    ~l1_struct_0(k2_yellow_1(sK0)) | ~spl3_9),
% 1.24/0.52    inference(resolution,[],[f247,f81])).
% 1.24/0.52  fof(f81,plain,(
% 1.24/0.52    ( ! [X0] : (~v1_subset_1(X0,X0) | ~l1_struct_0(k2_yellow_1(X0))) )),
% 1.24/0.52    inference(backward_demodulation,[],[f76,f80])).
% 1.24/0.52  fof(f80,plain,(
% 1.24/0.52    ( ! [X0] : (k2_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.24/0.52    inference(forward_demodulation,[],[f79,f52])).
% 1.24/0.52  fof(f52,plain,(
% 1.24/0.52    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.24/0.52    inference(cnf_transformation,[],[f16])).
% 1.24/0.52  fof(f16,axiom,(
% 1.24/0.52    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 1.24/0.52  fof(f79,plain,(
% 1.24/0.52    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0))) )),
% 1.24/0.52    inference(resolution,[],[f77,f51])).
% 1.24/0.52  fof(f77,plain,(
% 1.24/0.52    ( ! [X0] : (~l1_orders_2(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.24/0.52    inference(resolution,[],[f57,f55])).
% 1.24/0.52  fof(f57,plain,(
% 1.24/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f26])).
% 1.24/0.52  fof(f26,plain,(
% 1.24/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.24/0.52    inference(ennf_transformation,[],[f10])).
% 1.24/0.52  fof(f10,axiom,(
% 1.24/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.24/0.52  fof(f76,plain,(
% 1.24/0.52    ( ! [X0] : (~v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0) | ~l1_struct_0(k2_yellow_1(X0))) )),
% 1.24/0.52    inference(superposition,[],[f56,f52])).
% 1.24/0.52  fof(f56,plain,(
% 1.24/0.52    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f25])).
% 1.24/0.52  fof(f25,plain,(
% 1.24/0.52    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 1.24/0.52    inference(ennf_transformation,[],[f11])).
% 1.24/0.52  fof(f11,axiom,(
% 1.24/0.52    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).
% 1.24/0.52  fof(f247,plain,(
% 1.24/0.52    v1_subset_1(sK0,sK0) | ~spl3_9),
% 1.24/0.52    inference(backward_demodulation,[],[f160,f203])).
% 1.24/0.52  fof(f203,plain,(
% 1.24/0.52    sK0 = k2_tarski(sK1,sK1) | ~spl3_9),
% 1.24/0.52    inference(avatar_component_clause,[],[f201])).
% 1.24/0.52  fof(f201,plain,(
% 1.24/0.52    spl3_9 <=> sK0 = k2_tarski(sK1,sK1)),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.24/0.52  fof(f160,plain,(
% 1.24/0.52    v1_subset_1(k2_tarski(sK1,sK1),sK0)),
% 1.24/0.52    inference(backward_demodulation,[],[f45,f159])).
% 1.24/0.52  fof(f159,plain,(
% 1.24/0.52    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)),
% 1.24/0.52    inference(resolution,[],[f157,f44])).
% 1.24/0.52  fof(f44,plain,(
% 1.24/0.52    m1_subset_1(sK1,sK0)),
% 1.24/0.52    inference(cnf_transformation,[],[f35])).
% 1.24/0.52  fof(f35,plain,(
% 1.24/0.52    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f34,f33])).
% 1.24/0.52  fof(f33,plain,(
% 1.24/0.52    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f34,plain,(
% 1.24/0.52    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f21,plain,(
% 1.24/0.52    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.24/0.52    inference(flattening,[],[f20])).
% 1.24/0.52  fof(f20,plain,(
% 1.24/0.52    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.24/0.52    inference(ennf_transformation,[],[f19])).
% 1.24/0.52  fof(f19,negated_conjecture,(
% 1.24/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.24/0.52    inference(negated_conjecture,[],[f18])).
% 1.24/0.52  fof(f18,conjecture,(
% 1.24/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 1.24/0.52  fof(f157,plain,(
% 1.24/0.52    ( ! [X0] : (~m1_subset_1(X0,sK0) | k2_tarski(X0,X0) = k6_domain_1(sK0,X0)) )),
% 1.24/0.52    inference(resolution,[],[f73,f43])).
% 1.24/0.52  fof(f43,plain,(
% 1.24/0.52    ~v1_xboole_0(sK0)),
% 1.24/0.52    inference(cnf_transformation,[],[f35])).
% 1.24/0.52  fof(f73,plain,(
% 1.24/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 1.24/0.52    inference(definition_unfolding,[],[f60,f49])).
% 1.24/0.52  fof(f49,plain,(
% 1.24/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f6])).
% 1.24/0.52  fof(f6,axiom,(
% 1.24/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.24/0.52  fof(f60,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f28])).
% 1.24/0.52  fof(f28,plain,(
% 1.24/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.24/0.52    inference(flattening,[],[f27])).
% 1.24/0.52  fof(f27,plain,(
% 1.24/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.24/0.52    inference(ennf_transformation,[],[f14])).
% 1.24/0.52  fof(f14,axiom,(
% 1.24/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.24/0.52  fof(f45,plain,(
% 1.24/0.52    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 1.24/0.52    inference(cnf_transformation,[],[f35])).
% 1.24/0.52  fof(f245,plain,(
% 1.24/0.52    ~spl3_10),
% 1.24/0.52    inference(avatar_contradiction_clause,[],[f244])).
% 1.24/0.52  fof(f244,plain,(
% 1.24/0.52    $false | ~spl3_10),
% 1.24/0.52    inference(trivial_inequality_removal,[],[f242])).
% 1.24/0.52  fof(f242,plain,(
% 1.24/0.52    k1_xboole_0 != k1_xboole_0 | ~spl3_10),
% 1.24/0.52    inference(superposition,[],[f112,f214])).
% 1.24/0.52  fof(f214,plain,(
% 1.24/0.52    k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl3_10),
% 1.24/0.52    inference(resolution,[],[f206,f74])).
% 1.24/0.52  fof(f74,plain,(
% 1.24/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.24/0.52    inference(equality_resolution,[],[f63])).
% 1.24/0.52  fof(f63,plain,(
% 1.24/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.24/0.52    inference(cnf_transformation,[],[f37])).
% 1.24/0.52  fof(f37,plain,(
% 1.24/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.52    inference(flattening,[],[f36])).
% 1.24/0.52  % (21823)Refutation not found, incomplete strategy% (21823)------------------------------
% 1.24/0.52  % (21823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (21823)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (21823)Memory used [KB]: 10746
% 1.24/0.52  % (21823)Time elapsed: 0.112 s
% 1.24/0.52  % (21823)------------------------------
% 1.24/0.52  % (21823)------------------------------
% 1.24/0.52  fof(f36,plain,(
% 1.24/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.52    inference(nnf_transformation,[],[f2])).
% 1.24/0.52  fof(f2,axiom,(
% 1.24/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.24/0.52  fof(f206,plain,(
% 1.24/0.52    ( ! [X2] : (~r1_tarski(X2,k2_tarski(sK1,sK1)) | k1_xboole_0 = X2) ) | ~spl3_10),
% 1.24/0.52    inference(avatar_component_clause,[],[f205])).
% 1.24/0.52  fof(f205,plain,(
% 1.24/0.52    spl3_10 <=> ! [X2] : (~r1_tarski(X2,k2_tarski(sK1,sK1)) | k1_xboole_0 = X2)),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.24/0.52  fof(f112,plain,(
% 1.24/0.52    ( ! [X0] : (k1_xboole_0 != k2_tarski(X0,X0)) )),
% 1.24/0.52    inference(superposition,[],[f72,f71])).
% 1.24/0.52  fof(f71,plain,(
% 1.24/0.52    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.24/0.52    inference(definition_unfolding,[],[f48,f59])).
% 1.24/0.52  fof(f59,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f5])).
% 1.24/0.52  fof(f5,axiom,(
% 1.24/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.24/0.52  fof(f48,plain,(
% 1.24/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.24/0.52    inference(cnf_transformation,[],[f3])).
% 1.24/0.52  fof(f3,axiom,(
% 1.24/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.24/0.52  fof(f72,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(X1,k2_tarski(X0,X0)))) )),
% 1.24/0.52    inference(definition_unfolding,[],[f58,f59,f49])).
% 1.24/0.52  fof(f58,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f7])).
% 1.24/0.52  fof(f7,axiom,(
% 1.24/0.52    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.24/0.52  fof(f210,plain,(
% 1.24/0.52    ~spl3_5),
% 1.24/0.52    inference(avatar_contradiction_clause,[],[f208])).
% 1.24/0.52  fof(f208,plain,(
% 1.24/0.52    $false | ~spl3_5),
% 1.24/0.52    inference(resolution,[],[f137,f43])).
% 1.24/0.52  fof(f137,plain,(
% 1.24/0.52    v1_xboole_0(sK0) | ~spl3_5),
% 1.24/0.52    inference(avatar_component_clause,[],[f135])).
% 1.24/0.52  fof(f135,plain,(
% 1.24/0.52    spl3_5 <=> v1_xboole_0(sK0)),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.24/0.52  fof(f207,plain,(
% 1.24/0.52    spl3_9 | spl3_10 | ~spl3_4 | ~spl3_6),
% 1.24/0.52    inference(avatar_split_clause,[],[f195,f139,f122,f205,f201])).
% 1.24/0.52  fof(f122,plain,(
% 1.24/0.52    spl3_4 <=> r1_tarski(k6_domain_1(sK0,sK1),sK0)),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.24/0.52  fof(f139,plain,(
% 1.24/0.52    spl3_6 <=> ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0)),
% 1.24/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.24/0.52  fof(f195,plain,(
% 1.24/0.52    ( ! [X2] : (~r1_tarski(X2,k2_tarski(sK1,sK1)) | sK0 = k2_tarski(sK1,sK1) | k1_xboole_0 = X2) ) | (~spl3_4 | ~spl3_6)),
% 1.24/0.52    inference(resolution,[],[f154,f163])).
% 1.24/0.52  fof(f163,plain,(
% 1.24/0.52    r1_tarski(k2_tarski(sK1,sK1),sK0) | ~spl3_4),
% 1.24/0.52    inference(backward_demodulation,[],[f123,f159])).
% 1.24/0.52  fof(f123,plain,(
% 1.24/0.52    r1_tarski(k6_domain_1(sK0,sK1),sK0) | ~spl3_4),
% 1.24/0.52    inference(avatar_component_clause,[],[f122])).
% 1.24/0.52  fof(f154,plain,(
% 1.24/0.52    ( ! [X4,X3] : (~r1_tarski(X3,sK0) | ~r1_tarski(X4,X3) | sK0 = X3 | k1_xboole_0 = X4) ) | ~spl3_6),
% 1.24/0.52    inference(resolution,[],[f151,f84])).
% 1.24/0.52  fof(f84,plain,(
% 1.24/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.24/0.52    inference(resolution,[],[f64,f47])).
% 1.24/0.52  fof(f47,plain,(
% 1.24/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f4])).
% 1.24/0.52  fof(f4,axiom,(
% 1.24/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.24/0.52  fof(f64,plain,(
% 1.24/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f37])).
% 1.24/0.52  fof(f151,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | sK0 = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,sK0)) ) | ~spl3_6),
% 1.24/0.52    inference(resolution,[],[f149,f66])).
% 1.24/0.52  fof(f66,plain,(
% 1.24/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f41])).
% 1.24/0.53  % (21839)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.53  fof(f41,plain,(
% 1.24/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 1.24/0.53  fof(f40,plain,(
% 1.24/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f39,plain,(
% 1.24/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.24/0.53    inference(rectify,[],[f38])).
% 1.24/0.53  fof(f38,plain,(
% 1.24/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.24/0.53    inference(nnf_transformation,[],[f31])).
% 1.24/0.53  fof(f31,plain,(
% 1.24/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.24/0.53    inference(ennf_transformation,[],[f1])).
% 1.24/0.53  fof(f1,axiom,(
% 1.24/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.24/0.53  fof(f149,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | ~r1_tarski(X0,sK0) | sK0 = X0 | ~r1_tarski(X2,X0)) ) | ~spl3_6),
% 1.24/0.53    inference(resolution,[],[f143,f69])).
% 1.24/0.53  fof(f69,plain,(
% 1.24/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f42])).
% 1.24/0.53  fof(f42,plain,(
% 1.24/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.24/0.53    inference(nnf_transformation,[],[f8])).
% 1.24/0.53  fof(f8,axiom,(
% 1.24/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.24/0.53  fof(f143,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | sK0 = X0 | ~r1_tarski(X0,sK0) | ~r2_hidden(X2,X1)) ) | ~spl3_6),
% 1.24/0.53    inference(resolution,[],[f140,f70])).
% 1.24/0.53  fof(f70,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f32])).
% 1.24/0.53  fof(f32,plain,(
% 1.24/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.24/0.53    inference(ennf_transformation,[],[f9])).
% 1.24/0.53  fof(f9,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.24/0.53  fof(f140,plain,(
% 1.24/0.53    ( ! [X0] : (v1_xboole_0(X0) | ~r1_tarski(X0,sK0) | sK0 = X0) ) | ~spl3_6),
% 1.24/0.53    inference(avatar_component_clause,[],[f139])).
% 1.24/0.53  fof(f141,plain,(
% 1.24/0.53    spl3_5 | spl3_6),
% 1.24/0.53    inference(avatar_split_clause,[],[f133,f139,f135])).
% 1.24/0.53  fof(f133,plain,(
% 1.24/0.53    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) )),
% 1.24/0.53    inference(resolution,[],[f54,f46])).
% 1.24/0.53  fof(f46,plain,(
% 1.24/0.53    v1_zfmisc_1(sK0)),
% 1.24/0.53    inference(cnf_transformation,[],[f35])).
% 1.24/0.53  fof(f54,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f23])).
% 1.24/0.53  fof(f23,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.24/0.53    inference(flattening,[],[f22])).
% 1.24/0.53  fof(f22,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.24/0.53    inference(ennf_transformation,[],[f17])).
% 1.24/0.53  fof(f17,axiom,(
% 1.24/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.24/0.53  fof(f131,plain,(
% 1.24/0.53    spl3_4),
% 1.24/0.53    inference(avatar_contradiction_clause,[],[f130])).
% 1.24/0.53  fof(f130,plain,(
% 1.24/0.53    $false | spl3_4),
% 1.24/0.53    inference(resolution,[],[f128,f44])).
% 1.24/0.53  % (21845)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.24/0.53  fof(f128,plain,(
% 1.24/0.53    ~m1_subset_1(sK1,sK0) | spl3_4),
% 1.24/0.53    inference(resolution,[],[f124,f93])).
% 1.24/0.53  % (21815)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.53  fof(f93,plain,(
% 1.24/0.53    ( ! [X0] : (r1_tarski(k6_domain_1(sK0,X0),sK0) | ~m1_subset_1(X0,sK0)) )),
% 1.24/0.53    inference(resolution,[],[f92,f43])).
% 1.24/0.53  fof(f92,plain,(
% 1.24/0.53    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r1_tarski(k6_domain_1(X1,X0),X1)) )),
% 1.24/0.53    inference(resolution,[],[f61,f68])).
% 1.24/0.53  fof(f68,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f42])).
% 1.24/0.53  fof(f61,plain,(
% 1.24/0.53    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f30])).
% 1.24/0.53  fof(f30,plain,(
% 1.24/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.24/0.53    inference(flattening,[],[f29])).
% 1.24/0.53  fof(f29,plain,(
% 1.24/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.24/0.53    inference(ennf_transformation,[],[f12])).
% 1.24/0.53  fof(f12,axiom,(
% 1.24/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.24/0.53  fof(f124,plain,(
% 1.24/0.53    ~r1_tarski(k6_domain_1(sK0,sK1),sK0) | spl3_4),
% 1.24/0.53    inference(avatar_component_clause,[],[f122])).
% 1.24/0.53  % SZS output end Proof for theBenchmark
% 1.24/0.53  % (21827)------------------------------
% 1.24/0.53  % (21827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (21827)Termination reason: Refutation
% 1.24/0.53  
% 1.24/0.53  % (21827)Memory used [KB]: 6268
% 1.24/0.53  % (21827)Time elapsed: 0.123 s
% 1.24/0.53  % (21827)------------------------------
% 1.24/0.53  % (21827)------------------------------
% 1.24/0.53  % (21811)Success in time 0.172 s
%------------------------------------------------------------------------------
