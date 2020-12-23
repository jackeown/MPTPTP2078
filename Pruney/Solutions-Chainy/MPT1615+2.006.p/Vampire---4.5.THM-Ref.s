%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:42 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 116 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  201 ( 343 expanded)
%              Number of equality atoms :   44 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f56,f60,f64,f76,f80,f84,f93,f101,f108,f114])).

fof(f114,plain,
    ( spl1_1
    | ~ spl1_14
    | ~ spl1_16 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl1_1
    | ~ spl1_14
    | ~ spl1_16 ),
    inference(subsumption_resolution,[],[f110,f35])).

fof(f35,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl1_1
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f110,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | ~ spl1_14
    | ~ spl1_16 ),
    inference(superposition,[],[f92,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl1_16
  <=> k1_xboole_0 = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f92,plain,
    ( ! [X0] : k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl1_14
  <=> ! [X0] : k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f108,plain,
    ( spl1_16
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_15 ),
    inference(avatar_split_clause,[],[f103,f99,f58,f53,f105])).

fof(f53,plain,
    ( spl1_5
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f58,plain,
    ( spl1_6
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f99,plain,
    ( spl1_15
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))
        | k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) = k3_tarski(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f103,plain,
    ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_15 ),
    inference(forward_demodulation,[],[f102,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f102,plain,
    ( k3_tarski(k1_xboole_0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0)
    | ~ spl1_6
    | ~ spl1_15 ),
    inference(resolution,[],[f100,f59])).

fof(f59,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))
        | k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) = k3_tarski(X0) )
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl1_15
    | ~ spl1_2
    | ~ spl1_3
    | spl1_4
    | ~ spl1_10
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f97,f82,f74,f48,f43,f38,f99])).

fof(f38,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f43,plain,
    ( spl1_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f48,plain,
    ( spl1_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f74,plain,
    ( spl1_10
  <=> ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f82,plain,
    ( spl1_12
  <=> ! [X1,X0] :
        ( k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))
        | k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) = k3_tarski(X0) )
    | ~ spl1_2
    | ~ spl1_3
    | spl1_4
    | ~ spl1_10
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f96,f75])).

fof(f75,plain,
    ( ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
        | k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) = k3_tarski(X0) )
    | ~ spl1_2
    | ~ spl1_3
    | spl1_4
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f95,f50])).

fof(f50,plain,
    ( ~ v2_struct_0(sK0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
        | k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) = k3_tarski(X0)
        | v2_struct_0(sK0) )
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f94,f45])).

fof(f45,plain,
    ( v2_pre_topc(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
        | k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) = k3_tarski(X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl1_2
    | ~ spl1_12 ),
    inference(resolution,[],[f83,f40])).

fof(f40,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
        | k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f93,plain,
    ( spl1_14
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f89,f78,f62,f91])).

fof(f62,plain,
    ( spl1_7
  <=> ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f78,plain,
    ( spl1_11
  <=> ! [X0] :
        ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f89,plain,
    ( ! [X0] : k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(resolution,[],[f79,f63])).

fof(f63,plain,
    ( ! [X0] : l1_orders_2(k2_yellow_1(X0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f84,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f30,f82])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
         => k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_1)).

fof(f80,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f29,f78])).

fof(f29,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f76,plain,(
    spl1_10 ),
    inference(avatar_split_clause,[],[f27,f74])).

fof(f27,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f64,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f60,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f56,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f51,plain,(
    ~ spl1_4 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).

fof(f46,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f22,f33])).

fof(f22,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:16:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.39  % (11552)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.12/0.39  % (11552)Refutation found. Thanks to Tanya!
% 0.12/0.39  % SZS status Theorem for theBenchmark
% 0.12/0.39  % SZS output start Proof for theBenchmark
% 0.12/0.39  fof(f115,plain,(
% 0.12/0.39    $false),
% 0.12/0.39    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f56,f60,f64,f76,f80,f84,f93,f101,f108,f114])).
% 0.12/0.39  fof(f114,plain,(
% 0.12/0.39    spl1_1 | ~spl1_14 | ~spl1_16),
% 0.12/0.39    inference(avatar_contradiction_clause,[],[f113])).
% 0.12/0.39  fof(f113,plain,(
% 0.12/0.39    $false | (spl1_1 | ~spl1_14 | ~spl1_16)),
% 0.12/0.39    inference(subsumption_resolution,[],[f110,f35])).
% 0.12/0.39  fof(f35,plain,(
% 0.12/0.39    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | spl1_1),
% 0.12/0.39    inference(avatar_component_clause,[],[f33])).
% 0.12/0.39  fof(f33,plain,(
% 0.12/0.39    spl1_1 <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.12/0.39  fof(f110,plain,(
% 0.12/0.39    k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | (~spl1_14 | ~spl1_16)),
% 0.12/0.39    inference(superposition,[],[f92,f107])).
% 0.12/0.39  fof(f107,plain,(
% 0.12/0.39    k1_xboole_0 = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0) | ~spl1_16),
% 0.12/0.39    inference(avatar_component_clause,[],[f105])).
% 0.12/0.39  fof(f105,plain,(
% 0.12/0.39    spl1_16 <=> k1_xboole_0 = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0)),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.12/0.39  fof(f92,plain,(
% 0.12/0.39    ( ! [X0] : (k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)) ) | ~spl1_14),
% 0.12/0.39    inference(avatar_component_clause,[],[f91])).
% 0.12/0.39  fof(f91,plain,(
% 0.12/0.39    spl1_14 <=> ! [X0] : k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.12/0.39  fof(f108,plain,(
% 0.12/0.39    spl1_16 | ~spl1_5 | ~spl1_6 | ~spl1_15),
% 0.12/0.39    inference(avatar_split_clause,[],[f103,f99,f58,f53,f105])).
% 0.12/0.39  fof(f53,plain,(
% 0.12/0.39    spl1_5 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.12/0.39  fof(f58,plain,(
% 0.12/0.39    spl1_6 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.12/0.39  fof(f99,plain,(
% 0.12/0.39    spl1_15 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) | k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) = k3_tarski(X0))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.12/0.39  fof(f103,plain,(
% 0.12/0.39    k1_xboole_0 = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0) | (~spl1_5 | ~spl1_6 | ~spl1_15)),
% 0.12/0.39    inference(forward_demodulation,[],[f102,f55])).
% 0.12/0.39  fof(f55,plain,(
% 0.12/0.39    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl1_5),
% 0.12/0.39    inference(avatar_component_clause,[],[f53])).
% 0.12/0.39  fof(f102,plain,(
% 0.12/0.39    k3_tarski(k1_xboole_0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0) | (~spl1_6 | ~spl1_15)),
% 0.12/0.39    inference(resolution,[],[f100,f59])).
% 0.12/0.39  fof(f59,plain,(
% 0.12/0.39    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl1_6),
% 0.12/0.39    inference(avatar_component_clause,[],[f58])).
% 0.12/0.39  fof(f100,plain,(
% 0.12/0.39    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) | k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) = k3_tarski(X0)) ) | ~spl1_15),
% 0.12/0.39    inference(avatar_component_clause,[],[f99])).
% 0.12/0.39  fof(f101,plain,(
% 0.12/0.39    spl1_15 | ~spl1_2 | ~spl1_3 | spl1_4 | ~spl1_10 | ~spl1_12),
% 0.12/0.39    inference(avatar_split_clause,[],[f97,f82,f74,f48,f43,f38,f99])).
% 0.12/0.39  fof(f38,plain,(
% 0.12/0.39    spl1_2 <=> l1_pre_topc(sK0)),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.12/0.39  fof(f43,plain,(
% 0.12/0.39    spl1_3 <=> v2_pre_topc(sK0)),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.12/0.39  fof(f48,plain,(
% 0.12/0.39    spl1_4 <=> v2_struct_0(sK0)),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.12/0.39  fof(f74,plain,(
% 0.12/0.39    spl1_10 <=> ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.12/0.39  fof(f82,plain,(
% 0.12/0.39    spl1_12 <=> ! [X1,X0] : (k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.12/0.39  fof(f97,plain,(
% 0.12/0.39    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) | k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) = k3_tarski(X0)) ) | (~spl1_2 | ~spl1_3 | spl1_4 | ~spl1_10 | ~spl1_12)),
% 0.12/0.39    inference(forward_demodulation,[],[f96,f75])).
% 0.12/0.39  fof(f75,plain,(
% 0.12/0.39    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) ) | ~spl1_10),
% 0.12/0.39    inference(avatar_component_clause,[],[f74])).
% 0.12/0.39  fof(f96,plain,(
% 0.12/0.39    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) = k3_tarski(X0)) ) | (~spl1_2 | ~spl1_3 | spl1_4 | ~spl1_12)),
% 0.12/0.39    inference(subsumption_resolution,[],[f95,f50])).
% 0.12/0.39  fof(f50,plain,(
% 0.12/0.39    ~v2_struct_0(sK0) | spl1_4),
% 0.12/0.39    inference(avatar_component_clause,[],[f48])).
% 0.12/0.39  fof(f95,plain,(
% 0.12/0.39    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) = k3_tarski(X0) | v2_struct_0(sK0)) ) | (~spl1_2 | ~spl1_3 | ~spl1_12)),
% 0.12/0.39    inference(subsumption_resolution,[],[f94,f45])).
% 0.12/0.39  fof(f45,plain,(
% 0.12/0.39    v2_pre_topc(sK0) | ~spl1_3),
% 0.12/0.39    inference(avatar_component_clause,[],[f43])).
% 0.12/0.39  fof(f94,plain,(
% 0.12/0.39    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) = k3_tarski(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl1_2 | ~spl1_12)),
% 0.12/0.39    inference(resolution,[],[f83,f40])).
% 0.12/0.39  fof(f40,plain,(
% 0.12/0.39    l1_pre_topc(sK0) | ~spl1_2),
% 0.12/0.39    inference(avatar_component_clause,[],[f38])).
% 0.12/0.39  fof(f83,plain,(
% 0.12/0.39    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl1_12),
% 0.12/0.39    inference(avatar_component_clause,[],[f82])).
% 0.12/0.39  fof(f93,plain,(
% 0.12/0.39    spl1_14 | ~spl1_7 | ~spl1_11),
% 0.12/0.39    inference(avatar_split_clause,[],[f89,f78,f62,f91])).
% 0.12/0.39  fof(f62,plain,(
% 0.12/0.39    spl1_7 <=> ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.12/0.39  fof(f78,plain,(
% 0.12/0.39    spl1_11 <=> ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.12/0.39  fof(f89,plain,(
% 0.12/0.39    ( ! [X0] : (k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)) ) | (~spl1_7 | ~spl1_11)),
% 0.12/0.39    inference(resolution,[],[f79,f63])).
% 0.12/0.39  fof(f63,plain,(
% 0.12/0.39    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) ) | ~spl1_7),
% 0.12/0.39    inference(avatar_component_clause,[],[f62])).
% 0.12/0.39  fof(f79,plain,(
% 0.12/0.39    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) ) | ~spl1_11),
% 0.12/0.39    inference(avatar_component_clause,[],[f78])).
% 0.12/0.39  fof(f84,plain,(
% 0.12/0.39    spl1_12),
% 0.12/0.39    inference(avatar_split_clause,[],[f30,f82])).
% 0.12/0.39  fof(f30,plain,(
% 0.12/0.39    ( ! [X0,X1] : (k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f14])).
% 0.12/0.39  fof(f14,plain,(
% 0.12/0.39    ! [X0] : (! [X1] : (k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.12/0.39    inference(flattening,[],[f13])).
% 0.12/0.39  fof(f13,plain,(
% 0.12/0.39    ! [X0] : (! [X1] : (k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.12/0.39    inference(ennf_transformation,[],[f7])).
% 0.12/0.39  fof(f7,axiom,(
% 0.12/0.39    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) => k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_1)).
% 0.12/0.39  fof(f80,plain,(
% 0.12/0.39    spl1_11),
% 0.12/0.39    inference(avatar_split_clause,[],[f29,f78])).
% 0.12/0.39  fof(f29,plain,(
% 0.12/0.39    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f12])).
% 0.12/0.39  fof(f12,plain,(
% 0.12/0.39    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.12/0.39    inference(ennf_transformation,[],[f4])).
% 0.12/0.39  fof(f4,axiom,(
% 0.12/0.39    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.12/0.39  fof(f76,plain,(
% 0.12/0.39    spl1_10),
% 0.12/0.39    inference(avatar_split_clause,[],[f27,f74])).
% 0.12/0.39  fof(f27,plain,(
% 0.12/0.39    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.12/0.39    inference(cnf_transformation,[],[f6])).
% 0.12/0.39  fof(f6,axiom,(
% 0.12/0.39    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.12/0.39  fof(f64,plain,(
% 0.12/0.39    spl1_7),
% 0.12/0.39    inference(avatar_split_clause,[],[f26,f62])).
% 0.12/0.39  fof(f26,plain,(
% 0.12/0.39    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.12/0.39    inference(cnf_transformation,[],[f5])).
% 0.12/0.39  fof(f5,axiom,(
% 0.12/0.39    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.12/0.39  fof(f60,plain,(
% 0.12/0.39    spl1_6),
% 0.12/0.39    inference(avatar_split_clause,[],[f24,f58])).
% 0.12/0.39  fof(f24,plain,(
% 0.12/0.39    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.12/0.39    inference(cnf_transformation,[],[f2])).
% 0.12/0.39  fof(f2,axiom,(
% 0.12/0.39    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.12/0.39  fof(f56,plain,(
% 0.12/0.39    spl1_5),
% 0.12/0.39    inference(avatar_split_clause,[],[f23,f53])).
% 0.12/0.39  fof(f23,plain,(
% 0.12/0.39    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.12/0.39    inference(cnf_transformation,[],[f1])).
% 0.12/0.39  fof(f1,axiom,(
% 0.12/0.39    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.12/0.39  fof(f51,plain,(
% 0.12/0.39    ~spl1_4),
% 0.12/0.39    inference(avatar_split_clause,[],[f19,f48])).
% 0.12/0.39  fof(f19,plain,(
% 0.12/0.39    ~v2_struct_0(sK0)),
% 0.12/0.39    inference(cnf_transformation,[],[f18])).
% 0.12/0.39  fof(f18,plain,(
% 0.12/0.39    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.12/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).
% 0.12/0.39  fof(f17,plain,(
% 0.12/0.39    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.12/0.39    introduced(choice_axiom,[])).
% 0.12/0.39  fof(f11,plain,(
% 0.12/0.39    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.12/0.39    inference(flattening,[],[f10])).
% 0.12/0.39  fof(f10,plain,(
% 0.12/0.39    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.12/0.39    inference(ennf_transformation,[],[f9])).
% 0.12/0.39  fof(f9,negated_conjecture,(
% 0.12/0.39    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.12/0.39    inference(negated_conjecture,[],[f8])).
% 0.12/0.39  fof(f8,conjecture,(
% 0.12/0.39    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).
% 0.12/0.39  fof(f46,plain,(
% 0.12/0.39    spl1_3),
% 0.12/0.39    inference(avatar_split_clause,[],[f20,f43])).
% 0.12/0.39  fof(f20,plain,(
% 0.12/0.39    v2_pre_topc(sK0)),
% 0.12/0.39    inference(cnf_transformation,[],[f18])).
% 0.12/0.39  fof(f41,plain,(
% 0.12/0.39    spl1_2),
% 0.12/0.39    inference(avatar_split_clause,[],[f21,f38])).
% 0.12/0.39  fof(f21,plain,(
% 0.12/0.39    l1_pre_topc(sK0)),
% 0.12/0.39    inference(cnf_transformation,[],[f18])).
% 0.12/0.39  fof(f36,plain,(
% 0.12/0.39    ~spl1_1),
% 0.12/0.39    inference(avatar_split_clause,[],[f22,f33])).
% 0.12/0.39  fof(f22,plain,(
% 0.12/0.39    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.12/0.39    inference(cnf_transformation,[],[f18])).
% 0.12/0.39  % SZS output end Proof for theBenchmark
% 0.12/0.39  % (11552)------------------------------
% 0.12/0.39  % (11552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.39  % (11552)Termination reason: Refutation
% 0.12/0.39  
% 0.12/0.39  % (11552)Memory used [KB]: 10618
% 0.12/0.39  % (11552)Time elapsed: 0.004 s
% 0.12/0.39  % (11552)------------------------------
% 0.12/0.39  % (11552)------------------------------
% 0.12/0.39  % (11546)Success in time 0.039 s
%------------------------------------------------------------------------------
