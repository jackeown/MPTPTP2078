%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:32 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   63 (  91 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 129 expanded)
%              Number of equality atoms :   68 (  96 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1948,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f56,f1935,f1947])).

fof(f1947,plain,
    ( spl2_1
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f1946])).

fof(f1946,plain,
    ( $false
    | spl2_1
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1945,f34])).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f1945,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | spl2_1
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f1944,f218])).

fof(f218,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(forward_demodulation,[],[f217,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f217,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_tarski(k1_tarski(X0)) ),
    inference(forward_demodulation,[],[f205,f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f35,f34])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f205,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f190,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f59,f63])).

fof(f63,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f60,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f60,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f39,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f39,f33])).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f190,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f86,f61])).

fof(f61,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f39,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f86,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) = k2_xboole_0(X2,X3) ),
    inference(superposition,[],[f30,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f1944,plain,
    ( k2_tarski(sK0,sK0) != k3_tarski(k1_tarski(k1_tarski(sK0)))
    | spl2_1
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f1940,f34])).

fof(f1940,plain,
    ( k2_tarski(sK0,sK0) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK0)))
    | spl2_1
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f48,f1934])).

fof(f1934,plain,
    ( sK0 = sK1
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f1932])).

fof(f1932,plain,
    ( spl2_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f48,plain,
    ( k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_1
  <=> k2_tarski(sK0,sK1) = k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1935,plain,
    ( spl2_4
    | spl2_2 ),
    inference(avatar_split_clause,[],[f1930,f53,f1932])).

fof(f53,plain,
    ( spl2_2
  <=> k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1930,plain,
    ( sK0 = sK1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f1919,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f1919,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 = sK1
    | spl2_2 ),
    inference(superposition,[],[f55,f209])).

fof(f209,plain,(
    ! [X6,X5] :
      ( k2_xboole_0(k1_tarski(X6),k1_tarski(X5)) = k5_xboole_0(k1_tarski(X6),k1_tarski(X5))
      | X5 = X6 ) ),
    inference(superposition,[],[f190,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f55,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f56,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f51,f46,f53])).

fof(f51,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_1 ),
    inference(superposition,[],[f48,f35])).

fof(f49,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f27,f46])).

fof(f27,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24])).

fof(f24,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (10770)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (10770)Refutation not found, incomplete strategy% (10770)------------------------------
% 0.21/0.50  % (10770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10770)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (10770)Memory used [KB]: 10618
% 0.21/0.50  % (10770)Time elapsed: 0.095 s
% 0.21/0.50  % (10770)------------------------------
% 0.21/0.50  % (10770)------------------------------
% 0.21/0.51  % (10782)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (10790)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (10782)Refutation not found, incomplete strategy% (10782)------------------------------
% 0.21/0.51  % (10782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10782)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10782)Memory used [KB]: 1791
% 0.21/0.51  % (10782)Time elapsed: 0.099 s
% 0.21/0.51  % (10782)------------------------------
% 0.21/0.51  % (10782)------------------------------
% 0.21/0.51  % (10783)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (10762)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (10769)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (10775)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (10763)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (10786)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (10761)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (10766)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (10783)Refutation not found, incomplete strategy% (10783)------------------------------
% 0.21/0.53  % (10783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10777)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (10779)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (10774)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (10778)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (10771)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (10768)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.53  % (10762)Refutation not found, incomplete strategy% (10762)------------------------------
% 1.34/0.53  % (10762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (10762)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (10762)Memory used [KB]: 10746
% 1.34/0.53  % (10762)Time elapsed: 0.127 s
% 1.34/0.53  % (10762)------------------------------
% 1.34/0.53  % (10762)------------------------------
% 1.34/0.53  % (10783)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  % (10771)Refutation not found, incomplete strategy% (10771)------------------------------
% 1.34/0.53  % (10771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (10771)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (10771)Memory used [KB]: 10618
% 1.34/0.53  % (10771)Time elapsed: 0.132 s
% 1.34/0.53  % (10771)------------------------------
% 1.34/0.53  % (10771)------------------------------
% 1.34/0.53  
% 1.34/0.53  % (10783)Memory used [KB]: 10746
% 1.34/0.53  % (10783)Time elapsed: 0.068 s
% 1.34/0.53  % (10783)------------------------------
% 1.34/0.53  % (10783)------------------------------
% 1.34/0.54  % (10768)Refutation not found, incomplete strategy% (10768)------------------------------
% 1.34/0.54  % (10768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (10768)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (10768)Memory used [KB]: 10746
% 1.34/0.54  % (10768)Time elapsed: 0.126 s
% 1.34/0.54  % (10768)------------------------------
% 1.34/0.54  % (10768)------------------------------
% 1.34/0.54  % (10764)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.54  % (10765)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.54  % (10789)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.54  % (10788)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.54  % (10781)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.54  % (10785)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.54  % (10760)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.54  % (10760)Refutation not found, incomplete strategy% (10760)------------------------------
% 1.34/0.54  % (10760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (10760)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (10760)Memory used [KB]: 1663
% 1.34/0.54  % (10760)Time elapsed: 0.136 s
% 1.34/0.54  % (10760)------------------------------
% 1.34/0.54  % (10760)------------------------------
% 1.34/0.54  % (10781)Refutation not found, incomplete strategy% (10781)------------------------------
% 1.34/0.54  % (10781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (10781)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (10781)Memory used [KB]: 10746
% 1.34/0.54  % (10781)Time elapsed: 0.139 s
% 1.34/0.54  % (10781)------------------------------
% 1.34/0.54  % (10781)------------------------------
% 1.34/0.54  % (10780)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.55  % (10787)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.55  % (10784)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.55  % (10784)Refutation not found, incomplete strategy% (10784)------------------------------
% 1.34/0.55  % (10784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (10784)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (10784)Memory used [KB]: 1663
% 1.34/0.55  % (10784)Time elapsed: 0.138 s
% 1.34/0.55  % (10784)------------------------------
% 1.34/0.55  % (10784)------------------------------
% 1.34/0.55  % (10776)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.55  % (10776)Refutation not found, incomplete strategy% (10776)------------------------------
% 1.34/0.55  % (10776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (10776)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (10776)Memory used [KB]: 6140
% 1.34/0.55  % (10776)Time elapsed: 0.150 s
% 1.34/0.55  % (10776)------------------------------
% 1.34/0.55  % (10776)------------------------------
% 1.53/0.55  % (10772)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.55  % (10767)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.53/0.56  % (10778)Refutation not found, incomplete strategy% (10778)------------------------------
% 1.53/0.56  % (10778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (10778)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (10778)Memory used [KB]: 10618
% 1.53/0.56  % (10778)Time elapsed: 0.135 s
% 1.53/0.56  % (10778)------------------------------
% 1.53/0.56  % (10778)------------------------------
% 1.53/0.60  % (10816)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.53/0.60  % (10816)Refutation not found, incomplete strategy% (10816)------------------------------
% 1.53/0.60  % (10816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (10816)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.60  
% 1.53/0.60  % (10816)Memory used [KB]: 6140
% 1.53/0.60  % (10816)Time elapsed: 0.049 s
% 1.53/0.60  % (10816)------------------------------
% 1.53/0.60  % (10816)------------------------------
% 1.90/0.63  % (10817)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.90/0.65  % (10824)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 1.90/0.65  % (10822)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 1.90/0.67  % (10818)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.90/0.67  % (10819)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 1.90/0.67  % (10826)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 1.90/0.67  % (10821)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.15/0.67  % (10820)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.15/0.67  % (10826)Refutation not found, incomplete strategy% (10826)------------------------------
% 2.15/0.67  % (10826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.67  % (10826)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.67  
% 2.15/0.67  % (10826)Memory used [KB]: 6268
% 2.15/0.67  % (10826)Time elapsed: 0.059 s
% 2.15/0.67  % (10826)------------------------------
% 2.15/0.67  % (10826)------------------------------
% 2.15/0.68  % (10823)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.15/0.71  % (10825)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.15/0.72  % (10827)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.15/0.72  % (10827)Refutation not found, incomplete strategy% (10827)------------------------------
% 2.15/0.72  % (10827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.73  % (10827)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.73  
% 2.15/0.73  % (10827)Memory used [KB]: 1791
% 2.15/0.73  % (10827)Time elapsed: 0.066 s
% 2.15/0.73  % (10827)------------------------------
% 2.15/0.73  % (10827)------------------------------
% 2.76/0.78  % (10833)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.76/0.79  % (10818)Refutation found. Thanks to Tanya!
% 2.76/0.79  % SZS status Theorem for theBenchmark
% 2.76/0.79  % SZS output start Proof for theBenchmark
% 2.76/0.79  fof(f1948,plain,(
% 2.76/0.79    $false),
% 2.76/0.79    inference(avatar_sat_refutation,[],[f49,f56,f1935,f1947])).
% 2.76/0.79  fof(f1947,plain,(
% 2.76/0.79    spl2_1 | ~spl2_4),
% 2.76/0.79    inference(avatar_contradiction_clause,[],[f1946])).
% 2.76/0.79  fof(f1946,plain,(
% 2.76/0.79    $false | (spl2_1 | ~spl2_4)),
% 2.76/0.79    inference(subsumption_resolution,[],[f1945,f34])).
% 2.76/0.79  fof(f34,plain,(
% 2.76/0.79    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.76/0.79    inference(cnf_transformation,[],[f9])).
% 2.76/0.79  fof(f9,axiom,(
% 2.76/0.79    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.76/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.76/0.79  fof(f1945,plain,(
% 2.76/0.79    k1_tarski(sK0) != k2_tarski(sK0,sK0) | (spl2_1 | ~spl2_4)),
% 2.76/0.79    inference(forward_demodulation,[],[f1944,f218])).
% 2.76/0.79  fof(f218,plain,(
% 2.76/0.79    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 2.76/0.79    inference(forward_demodulation,[],[f217,f40])).
% 2.76/0.79  fof(f40,plain,(
% 2.76/0.79    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.76/0.79    inference(cnf_transformation,[],[f6])).
% 2.76/0.81  fof(f6,axiom,(
% 2.76/0.81    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.76/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.76/0.81  fof(f217,plain,(
% 2.76/0.81    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_tarski(k1_tarski(X0))) )),
% 2.76/0.81    inference(forward_demodulation,[],[f205,f50])).
% 2.76/0.81  fof(f50,plain,(
% 2.76/0.81    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 2.76/0.81    inference(superposition,[],[f35,f34])).
% 2.76/0.81  fof(f35,plain,(
% 2.76/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.76/0.81    inference(cnf_transformation,[],[f16])).
% 2.76/0.81  fof(f16,axiom,(
% 2.76/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.76/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.76/0.81  fof(f205,plain,(
% 2.76/0.81    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0)) )),
% 2.76/0.81    inference(superposition,[],[f190,f76])).
% 2.76/0.81  fof(f76,plain,(
% 2.76/0.81    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.76/0.81    inference(forward_demodulation,[],[f59,f63])).
% 2.76/0.81  fof(f63,plain,(
% 2.76/0.81    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 2.76/0.81    inference(forward_demodulation,[],[f60,f41])).
% 2.76/0.81  fof(f41,plain,(
% 2.76/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.76/0.81    inference(cnf_transformation,[],[f5])).
% 2.76/0.81  fof(f5,axiom,(
% 2.76/0.81    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 2.76/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.76/0.81  fof(f60,plain,(
% 2.76/0.81    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(X1,X1)) )),
% 2.76/0.81    inference(superposition,[],[f39,f31])).
% 2.76/0.81  fof(f31,plain,(
% 2.76/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.76/0.81    inference(cnf_transformation,[],[f4])).
% 2.76/0.81  fof(f4,axiom,(
% 2.76/0.81    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.76/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.76/0.81  fof(f39,plain,(
% 2.76/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.76/0.81    inference(cnf_transformation,[],[f3])).
% 2.76/0.81  fof(f3,axiom,(
% 2.76/0.81    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.76/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.76/0.81  fof(f59,plain,(
% 2.76/0.81    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 2.76/0.81    inference(superposition,[],[f39,f33])).
% 2.76/0.81  fof(f33,plain,(
% 2.76/0.81    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.76/0.81    inference(cnf_transformation,[],[f21])).
% 2.76/0.81  fof(f21,plain,(
% 2.76/0.81    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.76/0.81    inference(rectify,[],[f2])).
% 2.76/0.81  fof(f2,axiom,(
% 2.76/0.81    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.76/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.76/0.81  fof(f190,plain,(
% 2.76/0.81    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 2.76/0.81    inference(forward_demodulation,[],[f86,f61])).
% 2.76/0.81  fof(f61,plain,(
% 2.76/0.81    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))) )),
% 2.76/0.81    inference(superposition,[],[f39,f32])).
% 2.76/0.81  fof(f32,plain,(
% 2.76/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.76/0.81    inference(cnf_transformation,[],[f1])).
% 2.76/0.81  fof(f1,axiom,(
% 2.76/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.76/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.76/0.81  fof(f86,plain,(
% 2.76/0.81    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) = k2_xboole_0(X2,X3)) )),
% 2.76/0.81    inference(superposition,[],[f30,f28])).
% 2.76/0.81  fof(f28,plain,(
% 2.76/0.81    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.76/0.81    inference(cnf_transformation,[],[f7])).
% 2.76/0.81  fof(f7,axiom,(
% 2.76/0.81    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.76/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.76/0.81  fof(f30,plain,(
% 2.76/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.76/0.81    inference(cnf_transformation,[],[f8])).
% 2.76/0.81  fof(f8,axiom,(
% 2.76/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.76/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.76/0.81  fof(f1944,plain,(
% 2.76/0.81    k2_tarski(sK0,sK0) != k3_tarski(k1_tarski(k1_tarski(sK0))) | (spl2_1 | ~spl2_4)),
% 2.76/0.81    inference(forward_demodulation,[],[f1940,f34])).
% 2.76/0.81  fof(f1940,plain,(
% 2.76/0.81    k2_tarski(sK0,sK0) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK0))) | (spl2_1 | ~spl2_4)),
% 2.76/0.81    inference(backward_demodulation,[],[f48,f1934])).
% 2.76/0.81  fof(f1934,plain,(
% 2.76/0.81    sK0 = sK1 | ~spl2_4),
% 2.76/0.81    inference(avatar_component_clause,[],[f1932])).
% 2.76/0.81  fof(f1932,plain,(
% 2.76/0.81    spl2_4 <=> sK0 = sK1),
% 2.76/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.76/0.81  fof(f48,plain,(
% 2.76/0.81    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) | spl2_1),
% 2.76/0.81    inference(avatar_component_clause,[],[f46])).
% 2.76/0.81  fof(f46,plain,(
% 2.76/0.81    spl2_1 <=> k2_tarski(sK0,sK1) = k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.76/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.76/0.81  fof(f1935,plain,(
% 2.76/0.81    spl2_4 | spl2_2),
% 2.76/0.81    inference(avatar_split_clause,[],[f1930,f53,f1932])).
% 2.76/0.81  fof(f53,plain,(
% 2.76/0.81    spl2_2 <=> k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.76/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.76/0.81  fof(f1930,plain,(
% 2.76/0.81    sK0 = sK1 | spl2_2),
% 2.76/0.81    inference(subsumption_resolution,[],[f1919,f29])).
% 2.76/0.81  fof(f29,plain,(
% 2.76/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.76/0.81    inference(cnf_transformation,[],[f23])).
% 2.76/0.81  fof(f23,plain,(
% 2.76/0.81    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 2.76/0.81    inference(ennf_transformation,[],[f18])).
% 2.76/0.81  fof(f18,axiom,(
% 2.76/0.81    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.76/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 2.76/0.81  fof(f1919,plain,(
% 2.76/0.81    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK0 = sK1 | spl2_2),
% 2.76/0.81    inference(superposition,[],[f55,f209])).
% 2.76/0.81  fof(f209,plain,(
% 2.76/0.81    ( ! [X6,X5] : (k2_xboole_0(k1_tarski(X6),k1_tarski(X5)) = k5_xboole_0(k1_tarski(X6),k1_tarski(X5)) | X5 = X6) )),
% 2.76/0.81    inference(superposition,[],[f190,f37])).
% 2.76/0.81  fof(f37,plain,(
% 2.76/0.81    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.76/0.81    inference(cnf_transformation,[],[f26])).
% 2.76/0.81  fof(f26,plain,(
% 2.76/0.81    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 2.76/0.81    inference(nnf_transformation,[],[f17])).
% 2.76/0.81  fof(f17,axiom,(
% 2.76/0.81    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 2.76/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 2.76/0.81  fof(f55,plain,(
% 2.76/0.81    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl2_2),
% 2.76/0.81    inference(avatar_component_clause,[],[f53])).
% 2.76/0.81  fof(f56,plain,(
% 2.76/0.81    ~spl2_2 | spl2_1),
% 2.76/0.81    inference(avatar_split_clause,[],[f51,f46,f53])).
% 2.76/0.81  fof(f51,plain,(
% 2.76/0.81    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl2_1),
% 2.76/0.81    inference(superposition,[],[f48,f35])).
% 2.76/0.81  fof(f49,plain,(
% 2.76/0.81    ~spl2_1),
% 2.76/0.81    inference(avatar_split_clause,[],[f27,f46])).
% 2.76/0.81  fof(f27,plain,(
% 2.76/0.81    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.76/0.81    inference(cnf_transformation,[],[f25])).
% 2.76/0.81  fof(f25,plain,(
% 2.76/0.81    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.76/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24])).
% 2.76/0.81  fof(f24,plain,(
% 2.76/0.81    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.76/0.81    introduced(choice_axiom,[])).
% 2.76/0.81  fof(f22,plain,(
% 2.76/0.81    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.76/0.81    inference(ennf_transformation,[],[f20])).
% 2.76/0.81  fof(f20,negated_conjecture,(
% 2.76/0.81    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.76/0.81    inference(negated_conjecture,[],[f19])).
% 2.76/0.81  fof(f19,conjecture,(
% 2.76/0.81    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.76/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 2.76/0.81  % SZS output end Proof for theBenchmark
% 2.76/0.81  % (10818)------------------------------
% 2.76/0.81  % (10818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.81  % (10818)Termination reason: Refutation
% 2.76/0.81  
% 2.76/0.81  % (10818)Memory used [KB]: 7547
% 2.76/0.81  % (10818)Time elapsed: 0.222 s
% 2.76/0.81  % (10818)------------------------------
% 2.76/0.81  % (10818)------------------------------
% 2.76/0.81  % (10755)Success in time 0.444 s
%------------------------------------------------------------------------------
