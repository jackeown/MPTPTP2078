%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 (  83 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  121 ( 237 expanded)
%              Number of equality atoms :   26 (  79 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f38,f43,f54,f60,f66])).

fof(f66,plain,
    ( spl2_3
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl2_3
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f64,f32])).

fof(f32,plain,
    ( sK0 != sK1
    | spl2_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f64,plain,
    ( sK0 = sK1
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(resolution,[],[f55,f59])).

fof(f59,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK0 = X0 )
    | ~ spl2_6 ),
    inference(resolution,[],[f53,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f53,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f60,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f49,f40,f20,f57])).

fof(f20,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f40,plain,
    ( spl2_5
  <=> k1_xboole_0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f49,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f48,f22])).

fof(f22,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f48,plain,
    ( ~ v1_relat_1(sK1)
    | v1_xboole_0(sK1)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f47,f16])).

% (29214)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f16,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f47,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK1)
    | ~ spl2_5 ),
    inference(superposition,[],[f17,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f54,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f46,f35,f25,f51])).

fof(f25,plain,
    ( spl2_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f35,plain,
    ( spl2_4
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f46,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f45,f27])).

fof(f27,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f45,plain,
    ( ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f44,f16])).

fof(f44,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_4 ),
    inference(superposition,[],[f17,f37])).

% (29215)Refutation not found, incomplete strategy% (29215)------------------------------
% (29215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29215)Termination reason: Refutation not found, incomplete strategy

% (29215)Memory used [KB]: 10490
% (29215)Time elapsed: 0.053 s
% (29215)------------------------------
% (29215)------------------------------
fof(f37,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f43,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f13,f40])).

fof(f13,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k1_relat_1(X1)
                & k1_xboole_0 = k1_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k1_relat_1(X1)
              & k1_xboole_0 = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_relat_1)).

fof(f38,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f12,f35])).

fof(f12,plain,(
    k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f25])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f11,f20])).

fof(f11,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.44  % (29232)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.44  % (29232)Refutation not found, incomplete strategy% (29232)------------------------------
% 0.22/0.44  % (29232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (29232)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.44  
% 0.22/0.44  % (29232)Memory used [KB]: 1535
% 0.22/0.44  % (29232)Time elapsed: 0.028 s
% 0.22/0.44  % (29232)------------------------------
% 0.22/0.44  % (29232)------------------------------
% 0.22/0.46  % (29217)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (29215)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (29217)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f23,f28,f33,f38,f43,f54,f60,f66])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl2_3 | ~spl2_6 | ~spl2_7),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f65])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    $false | (spl2_3 | ~spl2_6 | ~spl2_7)),
% 0.22/0.47    inference(subsumption_resolution,[],[f64,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    sK0 != sK1 | spl2_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    spl2_3 <=> sK0 = sK1),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    sK0 = sK1 | (~spl2_6 | ~spl2_7)),
% 0.22/0.47    inference(resolution,[],[f55,f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    v1_xboole_0(sK1) | ~spl2_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f57])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    spl2_7 <=> v1_xboole_0(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(X0) | sK0 = X0) ) | ~spl2_6),
% 0.22/0.47    inference(resolution,[],[f53,f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    v1_xboole_0(sK0) | ~spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    spl2_6 <=> v1_xboole_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    spl2_7 | ~spl2_1 | ~spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f49,f40,f20,f57])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    spl2_1 <=> v1_relat_1(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    spl2_5 <=> k1_xboole_0 = k1_relat_1(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    v1_xboole_0(sK1) | (~spl2_1 | ~spl2_5)),
% 0.22/0.47    inference(subsumption_resolution,[],[f48,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    v1_relat_1(sK1) | ~spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f20])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ~v1_relat_1(sK1) | v1_xboole_0(sK1) | ~spl2_5),
% 0.22/0.47    inference(subsumption_resolution,[],[f47,f16])).
% 0.22/0.47  % (29214)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK1) | v1_xboole_0(sK1) | ~spl2_5),
% 0.22/0.47    inference(superposition,[],[f17,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    k1_xboole_0 = k1_relat_1(sK1) | ~spl2_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f40])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    spl2_6 | ~spl2_2 | ~spl2_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f46,f35,f25,f51])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    spl2_2 <=> v1_relat_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    spl2_4 <=> k1_xboole_0 = k1_relat_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    v1_xboole_0(sK0) | (~spl2_2 | ~spl2_4)),
% 0.22/0.47    inference(subsumption_resolution,[],[f45,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    v1_relat_1(sK0) | ~spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f25])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ~v1_relat_1(sK0) | v1_xboole_0(sK0) | ~spl2_4),
% 0.22/0.47    inference(subsumption_resolution,[],[f44,f16])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0) | v1_xboole_0(sK0) | ~spl2_4),
% 0.22/0.47    inference(superposition,[],[f17,f37])).
% 0.22/0.47  % (29215)Refutation not found, incomplete strategy% (29215)------------------------------
% 0.22/0.47  % (29215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (29215)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (29215)Memory used [KB]: 10490
% 0.22/0.47  % (29215)Time elapsed: 0.053 s
% 0.22/0.47  % (29215)------------------------------
% 0.22/0.47  % (29215)------------------------------
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    k1_xboole_0 = k1_relat_1(sK0) | ~spl2_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f35])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f13,f40])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    k1_xboole_0 = k1_relat_1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f6])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((X0 != X1 & (k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0)) => X0 = X1)))),
% 0.22/0.47    inference(negated_conjecture,[],[f4])).
% 0.22/0.47  fof(f4,conjecture,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0)) => X0 = X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_relat_1)).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl2_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f12,f35])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    k1_xboole_0 = k1_relat_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ~spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f14,f30])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    sK0 != sK1),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f15,f25])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    v1_relat_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f11,f20])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    v1_relat_1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (29217)------------------------------
% 0.22/0.47  % (29217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (29217)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (29217)Memory used [KB]: 10618
% 0.22/0.47  % (29217)Time elapsed: 0.054 s
% 0.22/0.47  % (29217)------------------------------
% 0.22/0.47  % (29217)------------------------------
% 0.22/0.47  % (29213)Success in time 0.112 s
%------------------------------------------------------------------------------
