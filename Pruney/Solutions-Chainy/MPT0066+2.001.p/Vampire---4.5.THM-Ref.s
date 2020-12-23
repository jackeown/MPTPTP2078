%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 102 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 274 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f54,f106,f121,f135])).

fof(f135,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f133,f26])).

fof(f26,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f133,plain,
    ( r2_xboole_0(sK0,sK0)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f110,f36])).

fof(f36,plain,
    ( sK0 = sK1
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f110,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f20,f53])).

fof(f53,plain,
    ( sK0 = sK2
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f20,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r2_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r2_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).

fof(f121,plain,
    ( ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f112,f40])).

fof(f40,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_2
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f112,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f42,f53])).

fof(f42,plain,(
    ~ r2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f20,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f106,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f104,f19])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f104,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_3 ),
    inference(superposition,[],[f86,f68])).

fof(f68,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f44,plain,(
    r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f20,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f86,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(X0,sK2))
    | spl3_3 ),
    inference(superposition,[],[f70,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f70,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(sK2,X0))
    | spl3_3 ),
    inference(resolution,[],[f49,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f49,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f45,f51,f47])).

fof(f45,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f21,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f32,f38,f34])).

fof(f32,plain,
    ( r2_xboole_0(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f19,f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:59:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (3162)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.45  % (3154)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (3162)Refutation not found, incomplete strategy% (3162)------------------------------
% 0.21/0.46  % (3162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (3162)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (3162)Memory used [KB]: 6140
% 0.21/0.46  % (3162)Time elapsed: 0.039 s
% 0.21/0.46  % (3162)------------------------------
% 0.21/0.46  % (3162)------------------------------
% 0.21/0.46  % (3160)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (3160)Refutation not found, incomplete strategy% (3160)------------------------------
% 0.21/0.47  % (3160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3160)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (3160)Memory used [KB]: 1535
% 0.21/0.47  % (3160)Time elapsed: 0.052 s
% 0.21/0.47  % (3160)------------------------------
% 0.21/0.47  % (3160)------------------------------
% 0.21/0.48  % (3166)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (3157)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (3166)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f41,f54,f106,f121,f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    $false | (~spl3_1 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : ~r2_xboole_0(X0,X0)),
% 0.21/0.48    inference(rectify,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    r2_xboole_0(sK0,sK0) | (~spl3_1 | ~spl3_4)),
% 0.21/0.48    inference(backward_demodulation,[],[f110,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    sK0 = sK1 | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl3_1 <=> sK0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    r2_xboole_0(sK1,sK0) | ~spl3_4),
% 0.21/0.48    inference(backward_demodulation,[],[f20,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    sK0 = sK2 | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl3_4 <=> sK0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    r2_xboole_0(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ~spl3_2 | ~spl3_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f120])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    $false | (~spl3_2 | ~spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    r2_xboole_0(sK0,sK1) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl3_2 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ~r2_xboole_0(sK0,sK1) | ~spl3_4),
% 0.21/0.48    inference(backward_demodulation,[],[f42,f53])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~r2_xboole_0(sK2,sK1)),
% 0.21/0.48    inference(resolution,[],[f20,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    $false | spl3_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f104,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | spl3_3),
% 0.21/0.48    inference(superposition,[],[f86,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    sK1 = k3_xboole_0(sK1,sK2)),
% 0.21/0.48    inference(resolution,[],[f44,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2)),
% 0.21/0.48    inference(resolution,[],[f20,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK0,k3_xboole_0(X0,sK2))) ) | spl3_3),
% 0.21/0.48    inference(superposition,[],[f70,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK0,k3_xboole_0(sK2,X0))) ) | spl3_3),
% 0.21/0.48    inference(resolution,[],[f49,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK2) | spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl3_3 <=> r1_tarski(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~spl3_3 | spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f45,f51,f47])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 0.21/0.48    inference(resolution,[],[f21,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~r2_xboole_0(sK0,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl3_1 | spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f38,f34])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    r2_xboole_0(sK0,sK1) | sK0 = sK1),
% 0.21/0.48    inference(resolution,[],[f19,f24])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (3166)------------------------------
% 0.21/0.48  % (3166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3166)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (3166)Memory used [KB]: 6140
% 0.21/0.48  % (3166)Time elapsed: 0.059 s
% 0.21/0.48  % (3166)------------------------------
% 0.21/0.48  % (3166)------------------------------
% 0.21/0.48  % (3157)Refutation not found, incomplete strategy% (3157)------------------------------
% 0.21/0.48  % (3157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3157)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3157)Memory used [KB]: 6012
% 0.21/0.48  % (3157)Time elapsed: 0.066 s
% 0.21/0.48  % (3157)------------------------------
% 0.21/0.49  % (3157)------------------------------
% 0.21/0.49  % (3146)Success in time 0.124 s
%------------------------------------------------------------------------------
