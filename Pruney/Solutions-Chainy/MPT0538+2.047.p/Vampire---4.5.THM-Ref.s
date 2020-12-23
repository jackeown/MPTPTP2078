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
% DateTime   : Thu Dec  3 12:49:15 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   52 (  57 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 103 expanded)
%              Number of equality atoms :   34 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f59,f62,f66])).

fof(f66,plain,
    ( spl2_1
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl2_1
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f64])).

fof(f64,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f39,f63])).

fof(f63,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl2_5 ),
    inference(resolution,[],[f58,f23])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f58,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_5
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f39,plain,
    ( k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl2_1
  <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f62,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f61,f53])).

fof(f53,plain,
    ( spl2_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f61,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f60,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f60,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f35,f22])).

fof(f22,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f59,plain,
    ( ~ spl2_4
    | spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f51,f42,f57,f53])).

fof(f42,plain,
    ( spl2_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f51,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) )
    | ~ spl2_2 ),
    inference(superposition,[],[f27,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f45,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f40,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:50:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (22732)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.47/0.56  % (22732)Refutation not found, incomplete strategy% (22732)------------------------------
% 1.47/0.56  % (22732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (22732)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (22732)Memory used [KB]: 1663
% 1.47/0.56  % (22732)Time elapsed: 0.130 s
% 1.47/0.56  % (22732)------------------------------
% 1.47/0.56  % (22732)------------------------------
% 1.47/0.56  % (22748)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.56  % (22748)Refutation found. Thanks to Tanya!
% 1.47/0.56  % SZS status Theorem for theBenchmark
% 1.47/0.56  % SZS output start Proof for theBenchmark
% 1.47/0.56  fof(f67,plain,(
% 1.47/0.56    $false),
% 1.47/0.56    inference(avatar_sat_refutation,[],[f40,f45,f59,f62,f66])).
% 1.47/0.56  fof(f66,plain,(
% 1.47/0.56    spl2_1 | ~spl2_5),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f65])).
% 1.47/0.56  fof(f65,plain,(
% 1.47/0.56    $false | (spl2_1 | ~spl2_5)),
% 1.47/0.56    inference(trivial_inequality_removal,[],[f64])).
% 1.47/0.56  fof(f64,plain,(
% 1.47/0.56    k1_xboole_0 != k1_xboole_0 | (spl2_1 | ~spl2_5)),
% 1.47/0.56    inference(superposition,[],[f39,f63])).
% 1.47/0.56  fof(f63,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | ~spl2_5),
% 1.47/0.56    inference(resolution,[],[f58,f23])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.47/0.56  fof(f58,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | ~spl2_5),
% 1.47/0.56    inference(avatar_component_clause,[],[f57])).
% 1.47/0.56  fof(f57,plain,(
% 1.47/0.56    spl2_5 <=> ! [X0] : (~r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = k8_relat_1(X0,k1_xboole_0))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.47/0.56  fof(f39,plain,(
% 1.47/0.56    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) | spl2_1),
% 1.47/0.56    inference(avatar_component_clause,[],[f37])).
% 1.47/0.56  fof(f37,plain,(
% 1.47/0.56    spl2_1 <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.47/0.56  fof(f62,plain,(
% 1.47/0.56    spl2_4),
% 1.47/0.56    inference(avatar_split_clause,[],[f61,f53])).
% 1.47/0.56  fof(f53,plain,(
% 1.47/0.56    spl2_4 <=> v1_relat_1(k1_xboole_0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.47/0.56  fof(f61,plain,(
% 1.47/0.56    v1_relat_1(k1_xboole_0)),
% 1.47/0.56    inference(resolution,[],[f60,f24])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f15])).
% 1.47/0.56  fof(f15,plain,(
% 1.47/0.56    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f13])).
% 1.47/0.56  fof(f13,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.47/0.56    inference(unused_predicate_definition_removal,[],[f8])).
% 1.47/0.56  fof(f8,axiom,(
% 1.47/0.56    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.47/0.56  fof(f60,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.47/0.56    inference(resolution,[],[f35,f22])).
% 1.47/0.56  fof(f22,plain,(
% 1.47/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.47/0.56  fof(f35,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f28,f34])).
% 1.47/0.56  fof(f34,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f26,f33])).
% 1.47/0.56  fof(f33,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f29,f32])).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f30,f31])).
% 1.47/0.56  fof(f31,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f6])).
% 1.47/0.56  fof(f6,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).
% 1.47/0.56  fof(f30,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.47/0.56  fof(f29,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f3])).
% 1.47/0.56  fof(f3,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f5])).
% 1.47/0.56  fof(f5,axiom,(
% 1.47/0.56    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f18])).
% 1.47/0.56  fof(f18,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.47/0.56    inference(ennf_transformation,[],[f7])).
% 1.47/0.56  fof(f7,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.47/0.56  fof(f59,plain,(
% 1.47/0.56    ~spl2_4 | spl2_5 | ~spl2_2),
% 1.47/0.56    inference(avatar_split_clause,[],[f51,f42,f57,f53])).
% 1.47/0.56  fof(f42,plain,(
% 1.47/0.56    spl2_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.47/0.56  fof(f51,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | ~spl2_2),
% 1.47/0.56    inference(superposition,[],[f27,f44])).
% 1.47/0.56  fof(f44,plain,(
% 1.47/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl2_2),
% 1.47/0.56    inference(avatar_component_clause,[],[f42])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 1.47/0.56    inference(cnf_transformation,[],[f17])).
% 1.47/0.56  fof(f17,plain,(
% 1.47/0.56    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(flattening,[],[f16])).
% 1.47/0.56  fof(f16,plain,(
% 1.47/0.56    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f9])).
% 1.47/0.56  fof(f9,axiom,(
% 1.47/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 1.47/0.56  fof(f45,plain,(
% 1.47/0.56    spl2_2),
% 1.47/0.56    inference(avatar_split_clause,[],[f21,f42])).
% 1.47/0.56  fof(f21,plain,(
% 1.47/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.47/0.56    inference(cnf_transformation,[],[f10])).
% 1.47/0.56  fof(f10,axiom,(
% 1.47/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.47/0.56  fof(f40,plain,(
% 1.47/0.56    ~spl2_1),
% 1.47/0.56    inference(avatar_split_clause,[],[f19,f37])).
% 1.47/0.56  fof(f19,plain,(
% 1.47/0.56    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 1.47/0.56    inference(cnf_transformation,[],[f14])).
% 1.47/0.56  fof(f14,plain,(
% 1.47/0.56    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 1.47/0.56    inference(ennf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,negated_conjecture,(
% 1.47/0.56    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 1.47/0.56    inference(negated_conjecture,[],[f11])).
% 1.47/0.56  fof(f11,conjecture,(
% 1.47/0.56    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (22748)------------------------------
% 1.47/0.56  % (22748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (22748)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (22748)Memory used [KB]: 10618
% 1.47/0.56  % (22748)Time elapsed: 0.137 s
% 1.47/0.56  % (22748)------------------------------
% 1.47/0.56  % (22748)------------------------------
% 1.47/0.57  % (22733)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.47/0.57  % (22740)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.57  % (22737)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.47/0.57  % (22736)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.47/0.57  % (22731)Success in time 0.207 s
%------------------------------------------------------------------------------
