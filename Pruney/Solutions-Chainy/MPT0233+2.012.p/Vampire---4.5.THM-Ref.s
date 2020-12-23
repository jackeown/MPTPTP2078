%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 254 expanded)
%              Number of leaves         :   14 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 ( 472 expanded)
%              Number of equality atoms :   76 ( 309 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f315,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f166,f177,f188,f199,f314])).

fof(f314,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f218,f290])).

fof(f290,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f284,f201])).

fof(f201,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f118,f153])).

fof(f153,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl6_1
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f118,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f71,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f71,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f33,f67,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f284,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3)))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f142,f272])).

fof(f272,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f270,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f270,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f216,f42])).

fof(f216,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl6_1 ),
    inference(superposition,[],[f88,f153])).

fof(f88,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) != X0
      | r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f38,f68,f67])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f67])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f142,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f117,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f117,plain,(
    r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f110,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f110,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f34,f35,f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f67])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f35,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f27])).

fof(f34,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f218,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl6_1 ),
    inference(superposition,[],[f91,f153])).

fof(f91,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_enumset1(X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f49,f67])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f199,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f93,f193])).

fof(f193,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f101,f165])).

fof(f165,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl6_4
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f101,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f34,f94])).

fof(f93,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f188,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f93,f182])).

fof(f182,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f111,f161])).

fof(f161,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK3,sK3,sK3,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl6_3
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f111,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(unit_resulting_resolution,[],[f35,f35,f94])).

fof(f177,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f93,f168])).

fof(f168,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f110,f157])).

fof(f157,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_2
  <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f166,plain,
    ( spl6_1
    | spl6_2
    | spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f119,f163,f159,f155,f151])).

fof(f119,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK3)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(resolution,[],[f71,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f36,f68,f68,f67,f67])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:57:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (32149)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (32157)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (32153)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (32149)Refutation not found, incomplete strategy% (32149)------------------------------
% 0.22/0.53  % (32149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32166)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (32149)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32149)Memory used [KB]: 1663
% 0.22/0.53  % (32149)Time elapsed: 0.103 s
% 0.22/0.53  % (32149)------------------------------
% 0.22/0.53  % (32149)------------------------------
% 0.22/0.54  % (32178)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (32178)Refutation not found, incomplete strategy% (32178)------------------------------
% 0.22/0.54  % (32178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32178)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (32178)Memory used [KB]: 1663
% 0.22/0.54  % (32178)Time elapsed: 0.001 s
% 0.22/0.54  % (32178)------------------------------
% 0.22/0.54  % (32178)------------------------------
% 0.22/0.54  % (32152)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (32148)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (32155)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (32175)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (32150)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (32151)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (32164)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (32174)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (32173)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (32177)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (32172)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (32167)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (32176)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (32165)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (32169)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (32165)Refutation not found, incomplete strategy% (32165)------------------------------
% 0.22/0.56  % (32165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32165)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (32165)Memory used [KB]: 10618
% 0.22/0.56  % (32165)Time elapsed: 0.136 s
% 0.22/0.56  % (32165)------------------------------
% 0.22/0.56  % (32165)------------------------------
% 0.22/0.56  % (32170)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (32168)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (32154)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (32158)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (32156)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (32161)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (32162)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (32161)Refutation not found, incomplete strategy% (32161)------------------------------
% 0.22/0.56  % (32161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32161)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (32161)Memory used [KB]: 10618
% 0.22/0.56  % (32161)Time elapsed: 0.148 s
% 0.22/0.56  % (32161)------------------------------
% 0.22/0.56  % (32161)------------------------------
% 0.22/0.56  % (32160)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (32174)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f315,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f166,f177,f188,f199,f314])).
% 0.22/0.57  fof(f314,plain,(
% 0.22/0.57    ~spl6_1),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f308])).
% 0.22/0.57  fof(f308,plain,(
% 0.22/0.57    $false | ~spl6_1),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f218,f290])).
% 0.22/0.57  fof(f290,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_1),
% 0.22/0.57    inference(forward_demodulation,[],[f284,f201])).
% 0.22/0.57  fof(f201,plain,(
% 0.22/0.57    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl6_1),
% 0.22/0.57    inference(backward_demodulation,[],[f118,f153])).
% 0.22/0.57  fof(f153,plain,(
% 0.22/0.57    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) | ~spl6_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f151])).
% 0.22/0.57  fof(f151,plain,(
% 0.22/0.57    spl6_1 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.57  fof(f118,plain,(
% 0.22/0.57    k2_enumset1(sK0,sK0,sK0,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f71,f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 0.22/0.57    inference(definition_unfolding,[],[f33,f67,f67])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f65,f59])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,axiom,(
% 0.22/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.57    inference(ennf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.57    inference(negated_conjecture,[],[f23])).
% 0.22/0.57  fof(f23,conjecture,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.22/0.57  fof(f284,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3)))) ) | ~spl6_1),
% 0.22/0.57    inference(backward_demodulation,[],[f142,f272])).
% 0.22/0.57  fof(f272,plain,(
% 0.22/0.57    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_1),
% 0.22/0.57    inference(forward_demodulation,[],[f270,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.57  fof(f270,plain,(
% 0.22/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) | ~spl6_1),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f216,f42])).
% 0.22/0.57  fof(f216,plain,(
% 0.22/0.57    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) | ~spl6_1),
% 0.22/0.57    inference(superposition,[],[f88,f153])).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))) )),
% 0.22/0.57    inference(equality_resolution,[],[f74])).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X1) != X0 | r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f38,f68,f67])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f50,f67])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,axiom,(
% 0.22/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f22])).
% 0.22/0.57  fof(f22,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.22/0.57  fof(f142,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK3)))) )),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f117,f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.57  fof(f117,plain,(
% 0.22/0.57    r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK3))),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f110,f83])).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f51,f68])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,axiom,(
% 0.22/0.57    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.57  fof(f110,plain,(
% 0.22/0.57    ~r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3))),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f34,f35,f94])).
% 0.22/0.57  fof(f94,plain,(
% 0.22/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.22/0.57    inference(equality_resolution,[],[f79])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.22/0.57    inference(definition_unfolding,[],[f47,f67])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    sK0 != sK3),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    sK0 != sK2),
% 0.22/0.57    inference(cnf_transformation,[],[f27])).
% 0.22/0.57  fof(f218,plain,(
% 0.22/0.57    r2_hidden(sK1,k1_xboole_0) | ~spl6_1),
% 0.22/0.57    inference(superposition,[],[f91,f153])).
% 0.22/0.57  fof(f91,plain,(
% 0.22/0.57    ( ! [X0,X3] : (r2_hidden(X3,k2_enumset1(X0,X0,X0,X3))) )),
% 0.22/0.57    inference(equality_resolution,[],[f90])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X3) != X2) )),
% 0.22/0.57    inference(equality_resolution,[],[f77])).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.22/0.57    inference(definition_unfolding,[],[f49,f67])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f199,plain,(
% 0.22/0.57    ~spl6_4),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f195])).
% 0.22/0.57  fof(f195,plain,(
% 0.22/0.57    $false | ~spl6_4),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f93,f193])).
% 0.22/0.57  fof(f193,plain,(
% 0.22/0.57    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_4),
% 0.22/0.57    inference(backward_demodulation,[],[f101,f165])).
% 0.22/0.57  fof(f165,plain,(
% 0.22/0.57    k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl6_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f163])).
% 0.22/0.57  fof(f163,plain,(
% 0.22/0.57    spl6_4 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    ~r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f34,f34,f94])).
% 0.22/0.57  fof(f93,plain,(
% 0.22/0.57    ( ! [X3,X1] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f92])).
% 0.22/0.57  fof(f92,plain,(
% 0.22/0.57    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_enumset1(X3,X3,X3,X1) != X2) )),
% 0.22/0.57    inference(equality_resolution,[],[f78])).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.22/0.57    inference(definition_unfolding,[],[f48,f67])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f188,plain,(
% 0.22/0.57    ~spl6_3),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f184])).
% 0.22/0.57  fof(f184,plain,(
% 0.22/0.57    $false | ~spl6_3),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f93,f182])).
% 0.22/0.57  fof(f182,plain,(
% 0.22/0.57    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_3),
% 0.22/0.57    inference(backward_demodulation,[],[f111,f161])).
% 0.22/0.57  fof(f161,plain,(
% 0.22/0.57    k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK3,sK3,sK3,sK3) | ~spl6_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f159])).
% 0.22/0.57  fof(f159,plain,(
% 0.22/0.57    spl6_3 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK3,sK3,sK3,sK3)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.57  fof(f111,plain,(
% 0.22/0.57    ~r2_hidden(sK0,k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f35,f35,f94])).
% 0.22/0.57  fof(f177,plain,(
% 0.22/0.57    ~spl6_2),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.57  fof(f173,plain,(
% 0.22/0.57    $false | ~spl6_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f93,f168])).
% 0.22/0.57  fof(f168,plain,(
% 0.22/0.57    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl6_2),
% 0.22/0.57    inference(backward_demodulation,[],[f110,f157])).
% 0.22/0.57  fof(f157,plain,(
% 0.22/0.57    k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK3) | ~spl6_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f155])).
% 0.22/0.57  fof(f155,plain,(
% 0.22/0.57    spl6_2 <=> k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK3)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.57  fof(f166,plain,(
% 0.22/0.57    spl6_1 | spl6_2 | spl6_3 | spl6_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f119,f163,f159,f155,f151])).
% 0.22/0.57  fof(f119,plain,(
% 0.22/0.57    k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK2) | k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK3,sK3,sK3,sK3) | k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK3) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.22/0.57    inference(resolution,[],[f71,f76])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X1,X1,X1,X1) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X2) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(definition_unfolding,[],[f36,f68,f68,f67,f67])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (32174)------------------------------
% 0.22/0.57  % (32174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (32174)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (32174)Memory used [KB]: 6396
% 0.22/0.57  % (32174)Time elapsed: 0.159 s
% 0.22/0.57  % (32174)------------------------------
% 0.22/0.57  % (32174)------------------------------
% 0.22/0.57  % (32147)Success in time 0.207 s
%------------------------------------------------------------------------------
