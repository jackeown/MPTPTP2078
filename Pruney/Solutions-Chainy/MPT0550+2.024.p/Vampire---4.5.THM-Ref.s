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
% DateTime   : Thu Dec  3 12:49:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 114 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  168 ( 304 expanded)
%              Number of equality atoms :   42 (  99 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f42,f46,f50,f54,f59,f64,f86,f106,f118])).

fof(f118,plain,
    ( ~ spl3_7
    | spl3_3
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f109,f104,f44,f62])).

fof(f62,plain,
    ( spl3_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f44,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f104,plain,
    ( spl3_13
  <=> sK0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f109,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_13 ),
    inference(superposition,[],[f66,f105])).

fof(f105,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f104])).

% (15492)Refutation not found, incomplete strategy% (15492)------------------------------
% (15492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15492)Termination reason: Refutation not found, incomplete strategy

% (15492)Memory used [KB]: 10490
% (15492)Time elapsed: 0.077 s
% (15492)------------------------------
% (15492)------------------------------
fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f29,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f106,plain,
    ( ~ spl3_4
    | spl3_13
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f102,f82,f40,f104,f48])).

fof(f48,plain,
    ( spl3_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f40,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f82,plain,
    ( spl3_10
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f102,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f100,f83])).

fof(f83,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f100,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

% (15506)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (15505)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f86,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f80,f36,f62,f48,f82])).

fof(f36,plain,
    ( spl3_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_1 ),
    inference(superposition,[],[f79,f37])).

fof(f37,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(resolution,[],[f78,f28])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f31,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k9_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f30,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f64,plain,
    ( spl3_7
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f60,f57,f52,f62])).

fof(f52,plain,
    ( spl3_5
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f57,plain,
    ( spl3_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f60,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(superposition,[],[f53,f58])).

fof(f58,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f53,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f59,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f55,f52,f57])).

fof(f55,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_5 ),
    inference(resolution,[],[f28,f53])).

fof(f54,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f34,f52])).

fof(f34,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f2,f22])).

fof(f22,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK2) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f48])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k9_relat_1(sK1,sK0)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(f46,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f25,f44])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f40])).

fof(f26,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f36])).

fof(f27,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:50:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (15497)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (15492)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (15497)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f38,f42,f46,f50,f54,f59,f64,f86,f106,f118])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    ~spl3_7 | spl3_3 | ~spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f109,f104,f44,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl3_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    spl3_3 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl3_13 <=> sK0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~v1_xboole_0(k1_xboole_0) | ~spl3_13),
% 0.20/0.47    inference(superposition,[],[f66,f105])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    sK0 = k1_relat_1(k1_xboole_0) | ~spl3_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f104])).
% 0.20/0.47  % (15492)Refutation not found, incomplete strategy% (15492)------------------------------
% 0.20/0.47  % (15492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (15492)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (15492)Memory used [KB]: 10490
% 0.20/0.47  % (15492)Time elapsed: 0.077 s
% 0.20/0.47  % (15492)------------------------------
% 0.20/0.47  % (15492)------------------------------
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(resolution,[],[f29,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    ~spl3_4 | spl3_13 | ~spl3_2 | ~spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f102,f82,f40,f104,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl3_4 <=> v1_relat_1(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    spl3_2 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl3_10 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    sK0 = k1_relat_1(k1_xboole_0) | ~v1_relat_1(sK1) | (~spl3_2 | ~spl3_10)),
% 0.20/0.47    inference(forward_demodulation,[],[f100,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f82])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl3_2),
% 0.20/0.47    inference(resolution,[],[f33,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f40])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.47  % (15506)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (15505)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl3_10 | ~spl3_4 | ~spl3_7 | ~spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f80,f36,f62,f48,f82])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    spl3_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK1) | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl3_1),
% 0.20/0.47    inference(superposition,[],[f79,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f36])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f78,f28])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(global_subsumption,[],[f31,f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(superposition,[],[f30,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl3_7 | ~spl3_5 | ~spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f60,f57,f52,f62])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    spl3_5 <=> v1_xboole_0(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl3_6 <=> k1_xboole_0 = sK2),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0) | (~spl3_5 | ~spl3_6)),
% 0.20/0.47    inference(superposition,[],[f53,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f57])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    v1_xboole_0(sK2) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f52])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl3_6 | ~spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f55,f52,f57])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | ~spl3_5),
% 0.20/0.47    inference(resolution,[],[f28,f53])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f52])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    v1_xboole_0(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    v1_xboole_0(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f2,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK2)),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ? [X0] : v1_xboole_0(X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f24,f48])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f25,f44])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    k1_xboole_0 != sK0),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f40])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f36])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (15497)------------------------------
% 0.20/0.47  % (15497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (15497)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (15497)Memory used [KB]: 10618
% 0.20/0.47  % (15497)Time elapsed: 0.064 s
% 0.20/0.47  % (15497)------------------------------
% 0.20/0.47  % (15497)------------------------------
% 0.20/0.47  % (15498)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (15490)Success in time 0.118 s
%------------------------------------------------------------------------------
