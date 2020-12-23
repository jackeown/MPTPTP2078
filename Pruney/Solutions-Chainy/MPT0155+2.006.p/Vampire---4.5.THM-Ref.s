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
% DateTime   : Thu Dec  3 12:33:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 101 expanded)
%              Number of leaves         :   16 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 178 expanded)
%              Number of equality atoms :   59 (  89 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f88,f111,f122,f132,f135])).

fof(f135,plain,
    ( spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f134,f115,f85])).

fof(f85,plain,
    ( spl6_2
  <=> k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f115,plain,
    ( spl6_6
  <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f134,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))))
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f133,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f133,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0))))
    | ~ spl6_6 ),
    inference(resolution,[],[f117,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ) ),
    inference(definition_unfolding,[],[f24,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f117,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f132,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f121,f57])).

fof(f57,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k1_enumset1(X4,X1,X2)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f121,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_7
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f122,plain,
    ( spl6_6
    | ~ spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f112,f108,f119,f115])).

fof(f108,plain,
    ( spl6_5
  <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f112,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))
    | r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))
    | ~ spl6_5 ),
    inference(superposition,[],[f26,f110])).

fof(f110,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f111,plain,
    ( spl6_5
    | spl6_2 ),
    inference(avatar_split_clause,[],[f96,f85,f108])).

fof(f96,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))
    | spl6_2 ),
    inference(trivial_inequality_removal,[],[f95])).

fof(f95,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))
    | spl6_2 ),
    inference(superposition,[],[f87,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(X0,k3_xboole_0(k1_enumset1(X1,X1,X1),X0))) = X0
      | sK3(k1_enumset1(X1,X1,X1),X0) = X1 ) ),
    inference(superposition,[],[f78,f20])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0)))) = X1
      | sK3(k1_enumset1(X0,X0,X0),X1) = X0 ) ),
    inference(resolution,[],[f70,f44])).

fof(f70,plain,(
    ! [X4,X5] :
      ( r1_tarski(k1_enumset1(X4,X4,X4),X5)
      | sK3(k1_enumset1(X4,X4,X4),X5) = X4 ) ),
    inference(resolution,[],[f49,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_enumset1(X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f28,f41])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f87,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f88,plain,
    ( ~ spl6_2
    | spl6_1 ),
    inference(avatar_split_clause,[],[f83,f60,f85])).

fof(f60,plain,
    ( spl6_1
  <=> k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f83,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))))
    | spl6_1 ),
    inference(forward_demodulation,[],[f62,f20])).

fof(f62,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0))))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f63,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f43,f60])).

fof(f43,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f18,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f31,f40,f41])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f18,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:01:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (26140)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.48  % (26140)Refutation not found, incomplete strategy% (26140)------------------------------
% 0.22/0.48  % (26140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26140)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (26140)Memory used [KB]: 10618
% 0.22/0.48  % (26140)Time elapsed: 0.064 s
% 0.22/0.48  % (26140)------------------------------
% 0.22/0.48  % (26140)------------------------------
% 0.22/0.48  % (26148)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.49  % (26148)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f63,f88,f111,f122,f132,f135])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    spl6_2 | ~spl6_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f134,f115,f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl6_2 <=> k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    spl6_6 <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)))) | ~spl6_6),
% 0.22/0.49    inference(forward_demodulation,[],[f133,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))) | ~spl6_6),
% 0.22/0.49    inference(resolution,[],[f117,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1) )),
% 0.22/0.49    inference(definition_unfolding,[],[f24,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f23,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)) | ~spl6_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f115])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    spl6_7),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f131])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    $false | spl6_7),
% 0.22/0.49    inference(resolution,[],[f121,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X4,X2,X1] : (r2_hidden(X4,k1_enumset1(X4,X1,X2))) )),
% 0.22/0.49    inference(equality_resolution,[],[f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X4,X1,X2) != X3) )),
% 0.22/0.49    inference(equality_resolution,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) | spl6_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f119])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    spl6_7 <=> r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    spl6_6 | ~spl6_7 | ~spl6_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f112,f108,f119,f115])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    spl6_5 <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) | r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)) | ~spl6_5),
% 0.22/0.49    inference(superposition,[],[f26,f110])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)) | ~spl6_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f108])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.22/0.49    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    spl6_5 | spl6_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f96,f85,f108])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)) | spl6_2),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f95])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)) | spl6_2),
% 0.22/0.49    inference(superposition,[],[f87,f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(k1_enumset1(X1,X1,X1),k5_xboole_0(X0,k3_xboole_0(k1_enumset1(X1,X1,X1),X0))) = X0 | sK3(k1_enumset1(X1,X1,X1),X0) = X1) )),
% 0.22/0.49    inference(superposition,[],[f78,f20])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0)))) = X1 | sK3(k1_enumset1(X0,X0,X0),X1) = X0) )),
% 0.22/0.49    inference(resolution,[],[f70,f44])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X4,X5] : (r1_tarski(k1_enumset1(X4,X4,X4),X5) | sK3(k1_enumset1(X4,X4,X4),X5) = X4) )),
% 0.22/0.49    inference(resolution,[],[f49,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0] : (~r2_hidden(X2,k1_enumset1(X0,X0,X0)) | X0 = X2) )),
% 0.22/0.49    inference(equality_resolution,[],[f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.22/0.49    inference(definition_unfolding,[],[f28,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f19,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)))) | spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ~spl6_2 | spl6_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f83,f60,f85])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl6_1 <=> k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)))) | spl6_1),
% 0.22/0.49    inference(forward_demodulation,[],[f62,f20])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))) | spl6_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~spl6_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f60])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0))))),
% 0.22/0.49    inference(definition_unfolding,[],[f18,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0))))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f31,f40,f41])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.49    inference(negated_conjecture,[],[f11])).
% 0.22/0.49  fof(f11,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (26148)------------------------------
% 0.22/0.49  % (26148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (26148)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (26148)Memory used [KB]: 10746
% 0.22/0.49  % (26148)Time elapsed: 0.069 s
% 0.22/0.49  % (26148)------------------------------
% 0.22/0.49  % (26148)------------------------------
% 0.22/0.49  % (26131)Success in time 0.123 s
%------------------------------------------------------------------------------
