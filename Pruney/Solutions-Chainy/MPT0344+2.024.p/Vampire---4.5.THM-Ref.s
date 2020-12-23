%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 256 expanded)
%              Number of leaves         :   31 (  90 expanded)
%              Depth                    :   19
%              Number of atoms          :  245 ( 461 expanded)
%              Number of equality atoms :   81 ( 207 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32318)Refutation not found, incomplete strategy% (32318)------------------------------
% (32318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32318)Termination reason: Refutation not found, incomplete strategy

% (32318)Memory used [KB]: 10874
% (32318)Time elapsed: 0.134 s
% (32318)------------------------------
% (32318)------------------------------
fof(f1406,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f156,f235,f266,f391,f485,f685,f1403])).

fof(f1403,plain,(
    ~ spl3_54 ),
    inference(avatar_contradiction_clause,[],[f1402])).

fof(f1402,plain,
    ( $false
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f1401,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1401,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f1400,f42])).

fof(f1400,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f1399,f42])).

fof(f1399,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f1398,f77])).

fof(f77,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f1398,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))))
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f1382,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1382,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))
    | ~ spl3_54 ),
    inference(superposition,[],[f82,f683])).

fof(f683,plain,
    ( k1_xboole_0 = k6_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f681])).

fof(f681,plain,
    ( spl3_54
  <=> k1_xboole_0 = k6_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f82,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ) ),
    inference(definition_unfolding,[],[f60,f76,f75,f76,f76])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f51,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f72])).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f685,plain,
    ( spl3_54
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f676,f482,f681])).

fof(f482,plain,
    ( spl3_37
  <=> r1_tarski(k6_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f676,plain,
    ( k1_xboole_0 = k6_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1))
    | ~ spl3_37 ),
    inference(resolution,[],[f484,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f484,plain,
    ( r1_tarski(k6_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1)),k1_xboole_0)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f482])).

fof(f485,plain,
    ( spl3_37
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f474,f303,f482])).

fof(f303,plain,
    ( spl3_26
  <=> r2_hidden(sK2(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f474,plain,
    ( r1_tarski(k6_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1)),k1_xboole_0)
    | ~ spl3_26 ),
    inference(unit_resulting_resolution,[],[f305,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f76])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f305,plain,
    ( r2_hidden(sK2(sK1),k1_xboole_0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f303])).

fof(f391,plain,
    ( spl3_26
    | spl3_1
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f390,f246,f89,f84,f303])).

fof(f84,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f89,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f246,plain,
    ( spl3_18
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

% (32303)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f390,plain,
    ( r2_hidden(sK2(sK1),k1_xboole_0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f384,f86])).

fof(f86,plain,
    ( k1_xboole_0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f384,plain,
    ( r2_hidden(sK2(sK1),k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(resolution,[],[f268,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f268,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f129,f248])).

fof(f248,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f246])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f91,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f91,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f266,plain,
    ( spl3_18
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f244,f150,f246])).

fof(f150,plain,
    ( spl3_10
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f244,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_10 ),
    inference(resolution,[],[f152,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f152,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f235,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f225,f86])).

fof(f225,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(resolution,[],[f216,f47])).

fof(f216,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f155,f129])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f156,plain,
    ( spl3_10
    | spl3_11 ),
    inference(avatar_split_clause,[],[f147,f154,f150])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f41,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f41,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,sK0) )
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,X0) )
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ! [X2] :
          ( ~ r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,sK0) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ~ ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f92,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f89])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f40,f84])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (32315)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.49  % (32323)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.50  % (32307)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (32326)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.50  % (32307)Refutation not found, incomplete strategy% (32307)------------------------------
% 0.20/0.50  % (32307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32315)Refutation not found, incomplete strategy% (32315)------------------------------
% 0.20/0.50  % (32315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32310)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (32302)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (32302)Refutation not found, incomplete strategy% (32302)------------------------------
% 0.20/0.50  % (32302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32307)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (32307)Memory used [KB]: 10618
% 0.20/0.51  % (32307)Time elapsed: 0.085 s
% 0.20/0.51  % (32307)------------------------------
% 0.20/0.51  % (32307)------------------------------
% 0.20/0.51  % (32315)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (32315)Memory used [KB]: 10618
% 0.20/0.51  % (32315)Time elapsed: 0.091 s
% 0.20/0.51  % (32315)------------------------------
% 0.20/0.51  % (32315)------------------------------
% 0.20/0.51  % (32305)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (32301)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (32304)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (32299)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (32313)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (32318)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (32320)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (32321)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (32306)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (32316)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (32320)Refutation not found, incomplete strategy% (32320)------------------------------
% 0.20/0.52  % (32320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32320)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32320)Memory used [KB]: 10746
% 0.20/0.52  % (32320)Time elapsed: 0.112 s
% 0.20/0.52  % (32320)------------------------------
% 0.20/0.52  % (32320)------------------------------
% 0.20/0.52  % (32327)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (32302)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32302)Memory used [KB]: 6268
% 0.20/0.52  % (32302)Time elapsed: 0.092 s
% 0.20/0.52  % (32302)------------------------------
% 0.20/0.52  % (32302)------------------------------
% 0.20/0.52  % (32306)Refutation not found, incomplete strategy% (32306)------------------------------
% 0.20/0.52  % (32306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32306)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32306)Memory used [KB]: 10746
% 0.20/0.52  % (32306)Time elapsed: 0.113 s
% 0.20/0.52  % (32306)------------------------------
% 0.20/0.52  % (32306)------------------------------
% 0.20/0.53  % (32325)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (32300)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (32323)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (32322)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (32324)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (32300)Refutation not found, incomplete strategy% (32300)------------------------------
% 0.20/0.53  % (32300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (32300)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (32300)Memory used [KB]: 10746
% 0.20/0.53  % (32300)Time elapsed: 0.117 s
% 0.20/0.53  % (32300)------------------------------
% 0.20/0.53  % (32300)------------------------------
% 0.20/0.53  % (32312)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (32308)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (32309)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (32314)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (32308)Refutation not found, incomplete strategy% (32308)------------------------------
% 0.20/0.53  % (32308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (32308)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (32308)Memory used [KB]: 10618
% 0.20/0.53  % (32308)Time elapsed: 0.132 s
% 0.20/0.53  % (32308)------------------------------
% 0.20/0.53  % (32308)------------------------------
% 0.20/0.53  % (32309)Refutation not found, incomplete strategy% (32309)------------------------------
% 0.20/0.53  % (32309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (32309)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (32309)Memory used [KB]: 10618
% 0.20/0.53  % (32309)Time elapsed: 0.131 s
% 0.20/0.53  % (32309)------------------------------
% 0.20/0.53  % (32309)------------------------------
% 0.20/0.54  % (32319)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (32319)Refutation not found, incomplete strategy% (32319)------------------------------
% 0.20/0.54  % (32319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32319)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (32319)Memory used [KB]: 1791
% 0.20/0.54  % (32319)Time elapsed: 0.103 s
% 0.20/0.54  % (32319)------------------------------
% 0.20/0.54  % (32319)------------------------------
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  % (32318)Refutation not found, incomplete strategy% (32318)------------------------------
% 0.20/0.54  % (32318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32318)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (32318)Memory used [KB]: 10874
% 0.20/0.54  % (32318)Time elapsed: 0.134 s
% 0.20/0.54  % (32318)------------------------------
% 0.20/0.54  % (32318)------------------------------
% 0.20/0.54  fof(f1406,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f87,f92,f156,f235,f266,f391,f485,f685,f1403])).
% 0.20/0.54  fof(f1403,plain,(
% 0.20/0.54    ~spl3_54),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1402])).
% 0.20/0.54  fof(f1402,plain,(
% 0.20/0.54    $false | ~spl3_54),
% 0.20/0.54    inference(subsumption_resolution,[],[f1401,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.54  fof(f1401,plain,(
% 0.20/0.54    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_54),
% 0.20/0.54    inference(forward_demodulation,[],[f1400,f42])).
% 0.20/0.54  fof(f1400,plain,(
% 0.20/0.54    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl3_54),
% 0.20/0.54    inference(forward_demodulation,[],[f1399,f42])).
% 0.20/0.54  fof(f1399,plain,(
% 0.20/0.54    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) | ~spl3_54),
% 0.20/0.54    inference(forward_demodulation,[],[f1398,f77])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.20/0.54    inference(definition_unfolding,[],[f48,f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f49,f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f50,f71])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f62,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f64,f69])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f65,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f66,f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.54    inference(rectify,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.54  fof(f1398,plain,(
% 0.20/0.54    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) | ~spl3_54),
% 0.20/0.54    inference(forward_demodulation,[],[f1382,f63])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.54  fof(f1382,plain,(
% 0.20/0.54    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) | ~spl3_54),
% 0.20/0.54    inference(superposition,[],[f82,f683])).
% 0.20/0.54  fof(f683,plain,(
% 0.20/0.54    k1_xboole_0 = k6_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1)) | ~spl3_54),
% 0.20/0.54    inference(avatar_component_clause,[],[f681])).
% 0.20/0.54  fof(f681,plain,(
% 0.20/0.54    spl3_54 <=> k1_xboole_0 = k6_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) )),
% 0.20/0.54    inference(equality_resolution,[],[f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f60,f76,f75,f76,f76])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f51,f74])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f52,f73])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f44,f72])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,axiom,(
% 0.20/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.54  fof(f685,plain,(
% 0.20/0.54    spl3_54 | ~spl3_37),
% 0.20/0.54    inference(avatar_split_clause,[],[f676,f482,f681])).
% 0.20/0.54  fof(f482,plain,(
% 0.20/0.54    spl3_37 <=> r1_tarski(k6_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1)),k1_xboole_0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.54  fof(f676,plain,(
% 0.20/0.54    k1_xboole_0 = k6_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1)) | ~spl3_37),
% 0.20/0.54    inference(resolution,[],[f484,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.54  fof(f484,plain,(
% 0.20/0.54    r1_tarski(k6_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1)),k1_xboole_0) | ~spl3_37),
% 0.20/0.54    inference(avatar_component_clause,[],[f482])).
% 0.20/0.54  fof(f485,plain,(
% 0.20/0.54    spl3_37 | ~spl3_26),
% 0.20/0.54    inference(avatar_split_clause,[],[f474,f303,f482])).
% 0.20/0.54  fof(f303,plain,(
% 0.20/0.54    spl3_26 <=> r2_hidden(sK2(sK1),k1_xboole_0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.54  fof(f474,plain,(
% 0.20/0.54    r1_tarski(k6_enumset1(sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1),sK2(sK1)),k1_xboole_0) | ~spl3_26),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f305,f78])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f59,f76])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.54  fof(f305,plain,(
% 0.20/0.54    r2_hidden(sK2(sK1),k1_xboole_0) | ~spl3_26),
% 0.20/0.54    inference(avatar_component_clause,[],[f303])).
% 0.20/0.54  fof(f391,plain,(
% 0.20/0.54    spl3_26 | spl3_1 | ~spl3_2 | ~spl3_18),
% 0.20/0.54    inference(avatar_split_clause,[],[f390,f246,f89,f84,f303])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    spl3_1 <=> k1_xboole_0 = sK1),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.54  fof(f246,plain,(
% 0.20/0.54    spl3_18 <=> k1_xboole_0 = sK0),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.54  % (32303)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  fof(f390,plain,(
% 0.20/0.54    r2_hidden(sK2(sK1),k1_xboole_0) | (spl3_1 | ~spl3_2 | ~spl3_18)),
% 0.20/0.54    inference(subsumption_resolution,[],[f384,f86])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    k1_xboole_0 != sK1 | spl3_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f84])).
% 0.20/0.54  fof(f384,plain,(
% 0.20/0.54    r2_hidden(sK2(sK1),k1_xboole_0) | k1_xboole_0 = sK1 | (~spl3_2 | ~spl3_18)),
% 0.20/0.54    inference(resolution,[],[f268,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.54  fof(f268,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,k1_xboole_0)) ) | (~spl3_2 | ~spl3_18)),
% 0.20/0.54    inference(backward_demodulation,[],[f129,f248])).
% 0.20/0.54  fof(f248,plain,(
% 0.20/0.54    k1_xboole_0 = sK0 | ~spl3_18),
% 0.20/0.54    inference(avatar_component_clause,[],[f246])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) ) | ~spl3_2),
% 0.20/0.54    inference(resolution,[],[f91,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f89])).
% 0.20/0.54  fof(f266,plain,(
% 0.20/0.54    spl3_18 | ~spl3_10),
% 0.20/0.54    inference(avatar_split_clause,[],[f244,f150,f246])).
% 0.20/0.54  fof(f150,plain,(
% 0.20/0.54    spl3_10 <=> v1_xboole_0(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.54  fof(f244,plain,(
% 0.20/0.54    k1_xboole_0 = sK0 | ~spl3_10),
% 0.20/0.54    inference(resolution,[],[f152,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    v1_xboole_0(sK0) | ~spl3_10),
% 0.20/0.54    inference(avatar_component_clause,[],[f150])).
% 0.20/0.54  fof(f235,plain,(
% 0.20/0.54    spl3_1 | ~spl3_2 | ~spl3_11),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f234])).
% 0.20/0.54  fof(f234,plain,(
% 0.20/0.54    $false | (spl3_1 | ~spl3_2 | ~spl3_11)),
% 0.20/0.54    inference(subsumption_resolution,[],[f225,f86])).
% 0.20/0.54  fof(f225,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | (~spl3_2 | ~spl3_11)),
% 0.20/0.54    inference(resolution,[],[f216,f47])).
% 0.20/0.54  fof(f216,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | (~spl3_2 | ~spl3_11)),
% 0.20/0.54    inference(subsumption_resolution,[],[f155,f129])).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl3_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f154])).
% 0.20/0.54  fof(f154,plain,(
% 0.20/0.54    spl3_11 <=> ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    spl3_10 | spl3_11),
% 0.20/0.54    inference(avatar_split_clause,[],[f147,f154,f150])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | v1_xboole_0(sK0)) )),
% 0.20/0.54    inference(resolution,[],[f41,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X2] : (~m1_subset_1(X2,sK0) | ~r2_hidden(X2,sK1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (! [X2] : (~r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(flattening,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ? [X0,X1] : ((! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.20/0.54    inference(negated_conjecture,[],[f22])).
% 0.20/0.54  fof(f22,conjecture,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    spl3_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f39,f89])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ~spl3_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f40,f84])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    k1_xboole_0 != sK1),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (32323)------------------------------
% 0.20/0.54  % (32323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32323)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (32323)Memory used [KB]: 7419
% 0.20/0.54  % (32323)Time elapsed: 0.113 s
% 0.20/0.54  % (32323)------------------------------
% 0.20/0.54  % (32323)------------------------------
% 0.20/0.54  % (32297)Success in time 0.173 s
%------------------------------------------------------------------------------
