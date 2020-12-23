%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  75 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  148 ( 242 expanded)
%              Number of equality atoms :   23 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f45,f49,f53,f58,f63,f67])).

fof(f67,plain,
    ( spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f65,f35])).

fof(f35,plain,
    ( v2_pre_topc(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl1_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f65,plain,
    ( ~ v2_pre_topc(sK0)
    | spl1_1
    | ~ spl1_2
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f64,f25])).

fof(f25,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl1_1
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f64,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl1_2
    | ~ spl1_9 ),
    inference(resolution,[],[f62,f30])).

fof(f30,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f62,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl1_9
  <=> ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f63,plain,
    ( spl1_9
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f59,f56,f47,f61])).

fof(f47,plain,
    ( spl1_6
  <=> ! [X0] :
        ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f56,plain,
    ( spl1_8
  <=> ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
        | ~ r2_hidden(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f59,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(resolution,[],[f57,f48])).

fof(f48,plain,
    ( ! [X0] :
        ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f58,plain,
    ( spl1_8
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f54,f51,f43,f56])).

fof(f43,plain,
    ( spl1_5
  <=> ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
        | ~ r2_hidden(k1_xboole_0,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f51,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f54,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
        | ~ r2_hidden(k1_xboole_0,X0) )
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f44,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f44,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
        | ~ r2_hidden(k1_xboole_0,X0)
        | v1_xboole_0(X0) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f53,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f49,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

fof(f45,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f36,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f13])).

fof(f13,plain,
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

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).

fof(f31,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f17,f28])).

fof(f17,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f18,f23])).

fof(f18,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (13077)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.41  % (13078)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (13078)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f68,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f26,f31,f36,f45,f49,f53,f58,f63,f67])).
% 0.21/0.41  fof(f67,plain,(
% 0.21/0.41    spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_9),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f66])).
% 0.21/0.41  fof(f66,plain,(
% 0.21/0.41    $false | (spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_9)),
% 0.21/0.41    inference(subsumption_resolution,[],[f65,f35])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    v2_pre_topc(sK0) | ~spl1_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f33])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    spl1_3 <=> v2_pre_topc(sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.41  fof(f65,plain,(
% 0.21/0.41    ~v2_pre_topc(sK0) | (spl1_1 | ~spl1_2 | ~spl1_9)),
% 0.21/0.41    inference(subsumption_resolution,[],[f64,f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | spl1_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f23])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    spl1_1 <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.41  fof(f64,plain,(
% 0.21/0.41    k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | ~v2_pre_topc(sK0) | (~spl1_2 | ~spl1_9)),
% 0.21/0.41    inference(resolution,[],[f62,f30])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    l1_pre_topc(sK0) | ~spl1_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f28])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    spl1_2 <=> l1_pre_topc(sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.41  fof(f62,plain,(
% 0.21/0.41    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | ~v2_pre_topc(X0)) ) | ~spl1_9),
% 0.21/0.41    inference(avatar_component_clause,[],[f61])).
% 0.21/0.41  fof(f61,plain,(
% 0.21/0.41    spl1_9 <=> ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.41  fof(f63,plain,(
% 0.21/0.41    spl1_9 | ~spl1_6 | ~spl1_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f59,f56,f47,f61])).
% 0.21/0.41  fof(f47,plain,(
% 0.21/0.41    spl1_6 <=> ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.41  fof(f56,plain,(
% 0.21/0.41    spl1_8 <=> ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.41  fof(f59,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl1_6 | ~spl1_8)),
% 0.21/0.41    inference(resolution,[],[f57,f48])).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    ( ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl1_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f47])).
% 0.21/0.41  fof(f57,plain,(
% 0.21/0.41    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))) ) | ~spl1_8),
% 0.21/0.41    inference(avatar_component_clause,[],[f56])).
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    spl1_8 | ~spl1_5 | ~spl1_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f54,f51,f43,f56])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    spl1_5 <=> ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    spl1_7 <=> ! [X1,X0] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.41  fof(f54,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) ) | (~spl1_5 | ~spl1_7)),
% 0.21/0.41    inference(subsumption_resolution,[],[f44,f52])).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) ) | ~spl1_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f51])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) ) | ~spl1_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f43])).
% 0.21/0.41  fof(f53,plain,(
% 0.21/0.41    spl1_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f21,f51])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    spl1_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f20,f47])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.41    inference(flattening,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => r2_hidden(k1_xboole_0,u1_pre_topc(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl1_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f43])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.21/0.42    inference(flattening,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl1_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f33])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    v2_pre_topc(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl1_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f28])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    l1_pre_topc(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ~spl1_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f23])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (13078)------------------------------
% 0.21/0.42  % (13078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (13078)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (13078)Memory used [KB]: 10490
% 0.21/0.42  % (13078)Time elapsed: 0.006 s
% 0.21/0.42  % (13078)------------------------------
% 0.21/0.42  % (13078)------------------------------
% 0.21/0.42  % (13071)Success in time 0.063 s
%------------------------------------------------------------------------------
