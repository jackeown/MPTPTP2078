%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (2359 expanded)
%              Number of leaves         :    9 ( 720 expanded)
%              Depth                    :   21
%              Number of atoms          :  130 (3830 expanded)
%              Number of equality atoms :   35 (2010 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f393,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f17,f388,f388,f21])).

% (3870)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f388,plain,(
    ! [X3] : r2_hidden(sK1,X3) ),
    inference(global_subsumption,[],[f16,f381])).

fof(f381,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_xboole_0,X3)
      | r2_hidden(sK1,X3) ) ),
    inference(superposition,[],[f44,f336])).

fof(f336,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(resolution,[],[f277,f276])).

% (3885)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f276,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f219,f252])).

fof(f252,plain,(
    k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f238,f239])).

% (3870)Refutation not found, incomplete strategy% (3870)------------------------------
% (3870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3870)Termination reason: Refutation not found, incomplete strategy

% (3870)Memory used [KB]: 10618
% (3870)Time elapsed: 0.138 s
% (3870)------------------------------
% (3870)------------------------------
fof(f239,plain,
    ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,sK2),k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f219,f67])).

fof(f67,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f65,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f65,plain,(
    ! [X0] :
      ( ~ sP5(X0,sK2,k2_enumset1(sK0,sK0,sK0,sK1))
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f47,f37])).

fof(f37,plain,(
    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f15,f36,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

% (3881)Refutation not found, incomplete strategy% (3881)------------------------------
% (3881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3881)Termination reason: Refutation not found, incomplete strategy

% (3881)Memory used [KB]: 10746
% (3881)Time elapsed: 0.121 s
% (3881)------------------------------
% (3881)------------------------------
fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f19,f35])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f15,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f238,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,sK2),X7)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f219,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f92,f21])).

fof(f92,plain,(
    ! [X0] : r1_xboole_0(sK2,X0) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( r1_xboole_0(sK2,X0)
      | r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f71,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),k1_xboole_0)
      | r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f67,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(sK2,X0),X1)
      | r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f69,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f21,f17])).

fof(f219,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0) ) ),
    inference(resolution,[],[f213,f209])).

fof(f209,plain,(
    ! [X1] :
      ( r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),k1_xboole_0)
      | k1_xboole_0 = X1
      | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1) ) ),
    inference(resolution,[],[f127,f65])).

fof(f127,plain,(
    ! [X0] :
      ( sP5(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
      | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f40,f37])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sP5(sK4(X0,X1,X2),X1,X0) ) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP5(sK4(X0,X1,X2),X1,X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X1)
      | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f209,f48])).

fof(f277,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1)),X2)
      | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) ) ),
    inference(backward_demodulation,[],[f234,f252])).

fof(f234,plain,(
    ! [X2] :
      ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)
      | ~ r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),X2) ) ),
    inference(resolution,[],[f219,f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f176,f21])).

fof(f176,plain,(
    ! [X0] : r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,(
    ! [X0] :
      ( r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0)
      | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0) ) ),
    inference(resolution,[],[f143,f118])).

fof(f118,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),X0),k1_xboole_0)
      | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0) ) ),
    inference(resolution,[],[f68,f22])).

fof(f68,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_enumset1(sK0,sK0,sK0,sK1))
      | r2_hidden(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f65,f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),X0),X1)
      | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0) ) ),
    inference(resolution,[],[f118,f48])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f16,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f17,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (3884)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (3861)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (3876)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (3876)Refutation not found, incomplete strategy% (3876)------------------------------
% 0.21/0.51  % (3876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3876)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3876)Memory used [KB]: 10618
% 0.21/0.51  % (3876)Time elapsed: 0.106 s
% 0.21/0.51  % (3876)------------------------------
% 0.21/0.51  % (3876)------------------------------
% 0.21/0.51  % (3868)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (3868)Refutation not found, incomplete strategy% (3868)------------------------------
% 0.21/0.51  % (3868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3868)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3868)Memory used [KB]: 10618
% 0.21/0.51  % (3868)Time elapsed: 0.099 s
% 0.21/0.51  % (3868)------------------------------
% 0.21/0.51  % (3868)------------------------------
% 0.21/0.52  % (3862)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (3883)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (3875)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (3873)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (3867)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (3871)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (3859)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (3859)Refutation not found, incomplete strategy% (3859)------------------------------
% 0.21/0.53  % (3859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3859)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3859)Memory used [KB]: 1663
% 0.21/0.53  % (3859)Time elapsed: 0.085 s
% 0.21/0.53  % (3859)------------------------------
% 0.21/0.53  % (3859)------------------------------
% 0.21/0.53  % (3864)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (3860)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (3865)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (3872)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (3882)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (3866)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (3863)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (3869)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (3881)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (3869)Refutation not found, incomplete strategy% (3869)------------------------------
% 0.21/0.54  % (3869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3869)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3869)Memory used [KB]: 10618
% 0.21/0.54  % (3869)Time elapsed: 0.128 s
% 0.21/0.54  % (3869)------------------------------
% 0.21/0.54  % (3869)------------------------------
% 0.21/0.54  % (3874)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (3874)Refutation not found, incomplete strategy% (3874)------------------------------
% 0.21/0.54  % (3874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3874)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3874)Memory used [KB]: 6140
% 0.21/0.54  % (3874)Time elapsed: 0.002 s
% 0.21/0.54  % (3874)------------------------------
% 0.21/0.54  % (3874)------------------------------
% 0.21/0.55  % (3877)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (3880)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (3878)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (3883)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f393,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f17,f388,f388,f21])).
% 0.21/0.55  % (3870)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.55  fof(f388,plain,(
% 0.21/0.55    ( ! [X3] : (r2_hidden(sK1,X3)) )),
% 0.21/0.55    inference(global_subsumption,[],[f16,f381])).
% 0.21/0.55  fof(f381,plain,(
% 0.21/0.55    ( ! [X3] : (~r1_tarski(k1_xboole_0,X3) | r2_hidden(sK1,X3)) )),
% 0.21/0.55    inference(superposition,[],[f44,f336])).
% 0.21/0.55  fof(f336,plain,(
% 0.21/0.55    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f331])).
% 0.21/0.55  fof(f331,plain,(
% 0.21/0.55    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.21/0.55    inference(resolution,[],[f277,f276])).
% 0.21/0.55  % (3885)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  fof(f276,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0,X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(backward_demodulation,[],[f219,f252])).
% 0.21/0.55  fof(f252,plain,(
% 0.21/0.55    k1_xboole_0 = sK2),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f244])).
% 0.21/0.55  fof(f244,plain,(
% 0.21/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.21/0.55    inference(resolution,[],[f238,f239])).
% 0.21/0.55  % (3870)Refutation not found, incomplete strategy% (3870)------------------------------
% 0.21/0.55  % (3870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3870)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3870)Memory used [KB]: 10618
% 0.21/0.55  % (3870)Time elapsed: 0.138 s
% 0.21/0.55  % (3870)------------------------------
% 0.21/0.55  % (3870)------------------------------
% 0.21/0.55  fof(f239,plain,(
% 0.21/0.55    r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,sK2),k1_xboole_0) | k1_xboole_0 = sK2),
% 0.21/0.55    inference(resolution,[],[f219,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.55    inference(resolution,[],[f65,f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0] : (~sP5(X0,sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(superposition,[],[f47,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),sK2))),
% 0.21/0.55    inference(definition_unfolding,[],[f15,f36,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f20,f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.56  % (3881)Refutation not found, incomplete strategy% (3881)------------------------------
% 0.21/0.56  % (3881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3881)Memory used [KB]: 10746
% 0.21/0.56  % (3881)Time elapsed: 0.121 s
% 0.21/0.56  % (3881)------------------------------
% 0.21/0.56  % (3881)------------------------------
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f19,f35])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.56    inference(negated_conjecture,[],[f10])).
% 0.21/0.56  fof(f10,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~sP5(X3,X1,X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 0.21/0.56    inference(definition_unfolding,[],[f28,f36])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f238,plain,(
% 0.21/0.56    ( ! [X7] : (~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,sK2),X7) | k1_xboole_0 = sK2) )),
% 0.21/0.56    inference(resolution,[],[f219,f93])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(resolution,[],[f92,f21])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(sK2,X0)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f83])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(sK2,X0) | r1_xboole_0(sK2,X0)) )),
% 0.21/0.56    inference(resolution,[],[f71,f69])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK3(sK2,X0),k1_xboole_0) | r1_xboole_0(sK2,X0)) )),
% 0.21/0.56    inference(resolution,[],[f67,f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(sK2,X0),X1) | r1_xboole_0(sK2,X0)) )),
% 0.21/0.56    inference(resolution,[],[f69,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(resolution,[],[f21,f17])).
% 0.21/0.56  fof(f219,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f215])).
% 0.21/0.56  fof(f215,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X0 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0)) )),
% 0.21/0.56    inference(resolution,[],[f213,f209])).
% 0.21/0.56  fof(f209,plain,(
% 0.21/0.56    ( ! [X1] : (r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),k1_xboole_0) | k1_xboole_0 = X1 | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X1),X1)) )),
% 0.21/0.56    inference(resolution,[],[f127,f65])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    ( ! [X0] : (sP5(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(superposition,[],[f40,f37])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X2) | sP5(sK4(X0,X1,X2),X1,X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f30,f36])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP5(sK4(X0,X1,X2),X1,X0) | r2_hidden(sK4(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f213,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X1) | r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(resolution,[],[f209,f48])).
% 0.21/0.56  fof(f277,plain,(
% 0.21/0.56    ( ! [X2] : (~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK1)),X2) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f234,f252])).
% 0.21/0.56  fof(f234,plain,(
% 0.21/0.56    ( ! [X2] : (k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) | ~r2_hidden(sK4(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),X2)) )),
% 0.21/0.56    inference(resolution,[],[f219,f177])).
% 0.21/0.56  fof(f177,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(resolution,[],[f176,f21])).
% 0.21/0.56  fof(f176,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f164])).
% 0.21/0.56  fof(f164,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0) | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0)) )),
% 0.21/0.56    inference(resolution,[],[f143,f118])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),X0),k1_xboole_0) | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0)) )),
% 0.21/0.56    inference(resolution,[],[f68,f22])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X2] : (~r2_hidden(X2,k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(X2,k1_xboole_0)) )),
% 0.21/0.56    inference(resolution,[],[f65,f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f143,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),X0),X1) | r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X0)) )),
% 0.21/0.56    inference(resolution,[],[f118,f48])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f33,f35])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (3883)------------------------------
% 0.21/0.56  % (3883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3883)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (3883)Memory used [KB]: 6396
% 0.21/0.56  % (3883)Time elapsed: 0.141 s
% 0.21/0.56  % (3883)------------------------------
% 0.21/0.56  % (3883)------------------------------
% 0.21/0.56  % (3858)Success in time 0.188 s
%------------------------------------------------------------------------------
