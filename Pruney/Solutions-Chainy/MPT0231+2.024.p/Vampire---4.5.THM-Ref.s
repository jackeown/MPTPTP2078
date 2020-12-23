%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:57 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 193 expanded)
%              Number of leaves         :   13 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  121 ( 302 expanded)
%              Number of equality atoms :   64 ( 210 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f105,f113])).

fof(f113,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f111,f35])).

fof(f35,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f111,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_1 ),
    inference(resolution,[],[f109,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f109,plain,
    ( r2_hidden(sK0,o_0_0_xboole_0)
    | ~ spl6_1 ),
    inference(superposition,[],[f62,f68])).

fof(f68,plain,
    ( o_0_0_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl6_1
  <=> o_0_0_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f62,plain,(
    ! [X3,X1] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f61])).

% (5501)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f61,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k3_enumset1(X3,X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f105,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f101,f90])).

fof(f90,plain,
    ( sK0 != sK1
    | ~ spl6_2 ),
    inference(superposition,[],[f15,f86])).

fof(f86,plain,
    ( sK1 = sK2
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f84,f15])).

fof(f84,plain,
    ( sK1 = sK2
    | sK0 = sK2
    | ~ spl6_2 ),
    inference(resolution,[],[f75,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,
    ( r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl6_2 ),
    inference(superposition,[],[f58,f72])).

fof(f72,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_2
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f58,plain,(
    ! [X2] : r2_hidden(X2,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k3_enumset1(X2,X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f19,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f38])).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f15,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f101,plain,
    ( sK0 = sK1
    | ~ spl6_2 ),
    inference(resolution,[],[f87,f62])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | sK1 = X0 )
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f76,f86])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | sK2 = X0 )
    | ~ spl6_2 ),
    inference(superposition,[],[f56,f72])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f20,f39])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f73,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f64,f70,f66])).

fof(f64,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | o_0_0_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(resolution,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f16,f31,f39,f39])).

fof(f31,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f40,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f14,f38,f39])).

fof(f14,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:38:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (5504)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (5529)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (5529)Refutation not found, incomplete strategy% (5529)------------------------------
% 0.22/0.53  % (5529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5529)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5529)Memory used [KB]: 1663
% 0.22/0.53  % (5529)Time elapsed: 0.003 s
% 0.22/0.53  % (5529)------------------------------
% 0.22/0.53  % (5529)------------------------------
% 1.54/0.57  % (5505)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.54/0.58  % (5527)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.54/0.58  % (5527)Refutation found. Thanks to Tanya!
% 1.54/0.58  % SZS status Theorem for theBenchmark
% 1.54/0.58  % SZS output start Proof for theBenchmark
% 1.54/0.58  fof(f114,plain,(
% 1.54/0.58    $false),
% 1.54/0.58    inference(avatar_sat_refutation,[],[f73,f105,f113])).
% 1.54/0.58  fof(f113,plain,(
% 1.54/0.58    ~spl6_1),
% 1.54/0.58    inference(avatar_contradiction_clause,[],[f112])).
% 1.54/0.58  fof(f112,plain,(
% 1.54/0.58    $false | ~spl6_1),
% 1.54/0.58    inference(subsumption_resolution,[],[f111,f35])).
% 1.54/0.58  fof(f35,plain,(
% 1.54/0.58    v1_xboole_0(o_0_0_xboole_0)),
% 1.54/0.58    inference(cnf_transformation,[],[f3])).
% 1.54/0.58  fof(f3,axiom,(
% 1.54/0.58    v1_xboole_0(o_0_0_xboole_0)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 1.54/0.58  fof(f111,plain,(
% 1.54/0.58    ~v1_xboole_0(o_0_0_xboole_0) | ~spl6_1),
% 1.54/0.58    inference(resolution,[],[f109,f33])).
% 1.54/0.58  fof(f33,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f1])).
% 1.54/0.58  fof(f1,axiom,(
% 1.54/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.54/0.58  fof(f109,plain,(
% 1.54/0.58    r2_hidden(sK0,o_0_0_xboole_0) | ~spl6_1),
% 1.54/0.58    inference(superposition,[],[f62,f68])).
% 1.54/0.58  fof(f68,plain,(
% 1.54/0.58    o_0_0_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) | ~spl6_1),
% 1.54/0.58    inference(avatar_component_clause,[],[f66])).
% 1.54/0.58  fof(f66,plain,(
% 1.54/0.58    spl6_1 <=> o_0_0_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.54/0.58  fof(f62,plain,(
% 1.54/0.58    ( ! [X3,X1] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X1))) )),
% 1.54/0.58    inference(equality_resolution,[],[f61])).
% 1.54/0.58  % (5501)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.54/0.58  fof(f61,plain,(
% 1.54/0.58    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k3_enumset1(X3,X3,X3,X3,X1) != X2) )),
% 1.54/0.58    inference(equality_resolution,[],[f49])).
% 1.54/0.58  fof(f49,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.54/0.58    inference(definition_unfolding,[],[f28,f38])).
% 1.54/0.58  fof(f38,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.54/0.58    inference(definition_unfolding,[],[f30,f37])).
% 1.54/0.58  fof(f37,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.54/0.58    inference(definition_unfolding,[],[f34,f36])).
% 1.54/0.58  fof(f36,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f9])).
% 1.54/0.58  fof(f9,axiom,(
% 1.54/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.54/0.58  fof(f34,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f8])).
% 1.54/0.58  fof(f8,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.54/0.58  fof(f30,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f7])).
% 1.54/0.58  fof(f7,axiom,(
% 1.54/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.54/0.58  fof(f28,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.54/0.58    inference(cnf_transformation,[],[f5])).
% 1.54/0.58  fof(f5,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.54/0.58  fof(f105,plain,(
% 1.54/0.58    ~spl6_2),
% 1.54/0.58    inference(avatar_contradiction_clause,[],[f104])).
% 1.54/0.58  fof(f104,plain,(
% 1.54/0.58    $false | ~spl6_2),
% 1.54/0.58    inference(subsumption_resolution,[],[f101,f90])).
% 1.54/0.58  fof(f90,plain,(
% 1.54/0.58    sK0 != sK1 | ~spl6_2),
% 1.54/0.58    inference(superposition,[],[f15,f86])).
% 1.54/0.58  fof(f86,plain,(
% 1.54/0.58    sK1 = sK2 | ~spl6_2),
% 1.54/0.58    inference(subsumption_resolution,[],[f84,f15])).
% 1.54/0.58  fof(f84,plain,(
% 1.54/0.58    sK1 = sK2 | sK0 = sK2 | ~spl6_2),
% 1.54/0.58    inference(resolution,[],[f75,f63])).
% 1.54/0.58  fof(f63,plain,(
% 1.54/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.54/0.58    inference(equality_resolution,[],[f50])).
% 1.54/0.58  fof(f50,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.54/0.58    inference(definition_unfolding,[],[f27,f38])).
% 1.54/0.58  fof(f27,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.54/0.58    inference(cnf_transformation,[],[f5])).
% 1.54/0.58  fof(f75,plain,(
% 1.54/0.58    r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl6_2),
% 1.54/0.58    inference(superposition,[],[f58,f72])).
% 1.54/0.58  fof(f72,plain,(
% 1.54/0.58    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | ~spl6_2),
% 1.54/0.58    inference(avatar_component_clause,[],[f70])).
% 1.54/0.58  fof(f70,plain,(
% 1.54/0.58    spl6_2 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.54/0.58  fof(f58,plain,(
% 1.54/0.58    ( ! [X2] : (r2_hidden(X2,k3_enumset1(X2,X2,X2,X2,X2))) )),
% 1.54/0.58    inference(equality_resolution,[],[f57])).
% 1.54/0.58  fof(f57,plain,(
% 1.54/0.58    ( ! [X2,X1] : (r2_hidden(X2,X1) | k3_enumset1(X2,X2,X2,X2,X2) != X1) )),
% 1.54/0.58    inference(equality_resolution,[],[f47])).
% 1.54/0.58  fof(f47,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.54/0.58    inference(definition_unfolding,[],[f19,f39])).
% 1.54/0.58  fof(f39,plain,(
% 1.54/0.58    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.54/0.58    inference(definition_unfolding,[],[f23,f38])).
% 1.54/0.58  fof(f23,plain,(
% 1.54/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f6])).
% 1.54/0.58  fof(f6,axiom,(
% 1.54/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.54/0.58  fof(f19,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.54/0.58    inference(cnf_transformation,[],[f4])).
% 1.54/0.58  fof(f4,axiom,(
% 1.54/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.54/0.58  fof(f15,plain,(
% 1.54/0.58    sK0 != sK2),
% 1.54/0.58    inference(cnf_transformation,[],[f13])).
% 1.54/0.58  fof(f13,plain,(
% 1.54/0.58    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 1.54/0.58    inference(ennf_transformation,[],[f12])).
% 1.54/0.58  fof(f12,negated_conjecture,(
% 1.54/0.58    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.54/0.58    inference(negated_conjecture,[],[f11])).
% 1.54/0.58  fof(f11,conjecture,(
% 1.54/0.58    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 1.54/0.58  fof(f101,plain,(
% 1.54/0.58    sK0 = sK1 | ~spl6_2),
% 1.54/0.58    inference(resolution,[],[f87,f62])).
% 1.54/0.58  fof(f87,plain,(
% 1.54/0.58    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK1 = X0) ) | ~spl6_2),
% 1.54/0.58    inference(backward_demodulation,[],[f76,f86])).
% 1.54/0.58  fof(f76,plain,(
% 1.54/0.58    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK2 = X0) ) | ~spl6_2),
% 1.54/0.58    inference(superposition,[],[f56,f72])).
% 1.54/0.58  fof(f56,plain,(
% 1.54/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X2) )),
% 1.54/0.58    inference(equality_resolution,[],[f46])).
% 1.54/0.58  fof(f46,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.54/0.58    inference(definition_unfolding,[],[f20,f39])).
% 1.54/0.58  fof(f20,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.54/0.58    inference(cnf_transformation,[],[f4])).
% 1.54/0.58  fof(f73,plain,(
% 1.54/0.58    spl6_1 | spl6_2),
% 1.54/0.58    inference(avatar_split_clause,[],[f64,f70,f66])).
% 1.54/0.58  fof(f64,plain,(
% 1.54/0.58    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | o_0_0_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 1.54/0.58    inference(resolution,[],[f40,f43])).
% 1.54/0.58  fof(f43,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | o_0_0_xboole_0 = X0) )),
% 1.54/0.58    inference(definition_unfolding,[],[f16,f31,f39,f39])).
% 1.54/0.58  fof(f31,plain,(
% 1.54/0.58    k1_xboole_0 = o_0_0_xboole_0),
% 1.54/0.58    inference(cnf_transformation,[],[f2])).
% 1.54/0.58  fof(f2,axiom,(
% 1.54/0.58    k1_xboole_0 = o_0_0_xboole_0),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 1.54/0.58  fof(f16,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f10])).
% 1.54/0.58  fof(f10,axiom,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.54/0.58  fof(f40,plain,(
% 1.54/0.58    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 1.54/0.58    inference(definition_unfolding,[],[f14,f38,f39])).
% 1.54/0.58  fof(f14,plain,(
% 1.54/0.58    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 1.54/0.58    inference(cnf_transformation,[],[f13])).
% 1.54/0.58  % SZS output end Proof for theBenchmark
% 1.54/0.58  % (5527)------------------------------
% 1.54/0.58  % (5527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (5527)Termination reason: Refutation
% 1.54/0.58  
% 1.54/0.58  % (5527)Memory used [KB]: 6268
% 1.54/0.58  % (5527)Time elapsed: 0.152 s
% 1.54/0.58  % (5527)------------------------------
% 1.54/0.58  % (5527)------------------------------
% 1.54/0.58  % (5501)Refutation not found, incomplete strategy% (5501)------------------------------
% 1.54/0.58  % (5501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (5501)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (5501)Memory used [KB]: 1663
% 1.54/0.58  % (5501)Time elapsed: 0.150 s
% 1.54/0.58  % (5501)------------------------------
% 1.54/0.58  % (5501)------------------------------
% 1.54/0.58  % (5519)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.54/0.58  % (5503)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.54/0.58  % (5513)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.54/0.59  % (5512)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.54/0.59  % (5523)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.54/0.60  % (5506)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.54/0.60  % (5522)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.54/0.60  % (5500)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.54/0.60  % (5499)Success in time 0.237 s
%------------------------------------------------------------------------------
