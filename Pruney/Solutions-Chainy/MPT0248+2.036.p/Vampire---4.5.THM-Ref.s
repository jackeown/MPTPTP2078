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
% DateTime   : Thu Dec  3 12:37:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 112 expanded)
%              Number of leaves         :   13 (  50 expanded)
%              Depth                    :    6
%              Number of atoms          :  121 ( 271 expanded)
%              Number of equality atoms :   69 ( 185 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f50,f55,f60,f69,f74,f123,f124,f133])).

fof(f133,plain,
    ( spl3_2
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f132,f52,f38,f43])).

fof(f43,plain,
    ( spl3_2
  <=> sK2 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,
    ( spl3_1
  <=> k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f52,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f132,plain,
    ( sK2 = k2_tarski(sK0,sK0)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f125,f81])).

fof(f81,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f19,f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f125,plain,
    ( k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f40,f53])).

fof(f53,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f40,plain,
    ( k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f124,plain,
    ( spl3_5
    | spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f119,f38,f71,f57])).

fof(f57,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f71,plain,
    ( spl3_7
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f119,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_1 ),
    inference(resolution,[],[f105,f85])).

fof(f85,plain,(
    ! [X4,X3] : r1_tarski(X3,k2_xboole_0(X4,X3)) ),
    inference(superposition,[],[f17,f19])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = X0
        | k1_xboole_0 = X0 )
    | ~ spl3_1 ),
    inference(superposition,[],[f31,f40])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X1))
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f20,f16,f16])).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f123,plain,
    ( spl3_4
    | spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f118,f38,f66,f52])).

fof(f66,plain,
    ( spl3_6
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f118,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ spl3_1 ),
    inference(resolution,[],[f105,f17])).

fof(f74,plain,
    ( ~ spl3_7
    | ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f63,f43,f38,f71])).

fof(f63,plain,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | ~ spl3_1
    | spl3_2 ),
    inference(superposition,[],[f45,f40])).

fof(f45,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f69,plain,
    ( ~ spl3_6
    | ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f62,f47,f38,f66])).

fof(f47,plain,
    ( spl3_3
  <=> sK1 = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f62,plain,
    ( sK1 != k2_xboole_0(sK1,sK2)
    | ~ spl3_1
    | spl3_3 ),
    inference(superposition,[],[f49,f40])).

fof(f49,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f60,plain,
    ( ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f28,f47,f57])).

fof(f28,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f11,f16])).

fof(f11,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f55,plain,
    ( ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f27,f52,f43])).

fof(f27,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f12,f16])).

fof(f12,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f26,f47,f43])).

fof(f26,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | sK2 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f13,f16,f16])).

fof(f13,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f25,f38])).

fof(f25,plain,(
    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:44:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (5780)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (5788)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (5788)Refutation not found, incomplete strategy% (5788)------------------------------
% 0.20/0.51  % (5788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5796)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (5780)Refutation not found, incomplete strategy% (5780)------------------------------
% 0.20/0.52  % (5780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5788)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5788)Memory used [KB]: 10746
% 0.20/0.52  % (5788)Time elapsed: 0.102 s
% 0.20/0.52  % (5788)------------------------------
% 0.20/0.52  % (5788)------------------------------
% 0.20/0.52  % (5780)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5780)Memory used [KB]: 1663
% 0.20/0.52  % (5780)Time elapsed: 0.101 s
% 0.20/0.52  % (5780)------------------------------
% 0.20/0.52  % (5780)------------------------------
% 0.20/0.52  % (5790)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (5796)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f41,f50,f55,f60,f69,f74,f123,f124,f133])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    spl3_2 | ~spl3_1 | ~spl3_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f132,f52,f38,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    spl3_2 <=> sK2 = k2_tarski(sK0,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    spl3_1 <=> k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    spl3_4 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    sK2 = k2_tarski(sK0,sK0) | (~spl3_1 | ~spl3_4)),
% 0.20/0.52    inference(forward_demodulation,[],[f125,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.52    inference(superposition,[],[f19,f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    k2_tarski(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2) | (~spl3_1 | ~spl3_4)),
% 0.20/0.52    inference(backward_demodulation,[],[f40,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | ~spl3_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f52])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0) | ~spl3_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f38])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    spl3_5 | spl3_7 | ~spl3_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f119,f38,f71,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    spl3_5 <=> k1_xboole_0 = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    spl3_7 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    sK2 = k2_xboole_0(sK1,sK2) | k1_xboole_0 = sK2 | ~spl3_1),
% 0.20/0.52    inference(resolution,[],[f105,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X4,X3] : (r1_tarski(X3,k2_xboole_0(X4,X3))) )),
% 0.20/0.52    inference(superposition,[],[f17,f19])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0) ) | ~spl3_1),
% 0.20/0.52    inference(superposition,[],[f31,f40])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X1)) | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f20,f16,f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    spl3_4 | spl3_6 | ~spl3_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f118,f38,f66,f52])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    spl3_6 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    sK1 = k2_xboole_0(sK1,sK2) | k1_xboole_0 = sK1 | ~spl3_1),
% 0.20/0.52    inference(resolution,[],[f105,f17])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ~spl3_7 | ~spl3_1 | spl3_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f63,f43,f38,f71])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    sK2 != k2_xboole_0(sK1,sK2) | (~spl3_1 | spl3_2)),
% 0.20/0.52    inference(superposition,[],[f45,f40])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    sK2 != k2_tarski(sK0,sK0) | spl3_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f43])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ~spl3_6 | ~spl3_1 | spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f62,f47,f38,f66])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    spl3_3 <=> sK1 = k2_tarski(sK0,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    sK1 != k2_xboole_0(sK1,sK2) | (~spl3_1 | spl3_3)),
% 0.20/0.52    inference(superposition,[],[f49,f40])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    sK1 != k2_tarski(sK0,sK0) | spl3_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f47])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ~spl3_5 | ~spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f28,f47,f57])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    sK1 != k2_tarski(sK0,sK0) | k1_xboole_0 != sK2),
% 0.20/0.52    inference(definition_unfolding,[],[f11,f16])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ~spl3_2 | ~spl3_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f27,f52,f43])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | sK2 != k2_tarski(sK0,sK0)),
% 0.20/0.52    inference(definition_unfolding,[],[f12,f16])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ~spl3_2 | ~spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f26,f47,f43])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    sK1 != k2_tarski(sK0,sK0) | sK2 != k2_tarski(sK0,sK0)),
% 0.20/0.52    inference(definition_unfolding,[],[f13,f16,f16])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    spl3_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f25,f38])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    k2_xboole_0(sK1,sK2) = k2_tarski(sK0,sK0)),
% 0.20/0.52    inference(definition_unfolding,[],[f14,f16])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (5796)------------------------------
% 0.20/0.52  % (5796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5796)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (5796)Memory used [KB]: 10746
% 0.20/0.52  % (5796)Time elapsed: 0.118 s
% 0.20/0.52  % (5796)------------------------------
% 0.20/0.52  % (5796)------------------------------
% 0.20/0.53  % (5779)Success in time 0.164 s
%------------------------------------------------------------------------------
