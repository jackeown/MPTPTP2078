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
% DateTime   : Thu Dec  3 12:30:13 EST 2020

% Result     : Theorem 2.34s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   47 (  74 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :   15
%              Number of atoms          :   63 (  95 expanded)
%              Number of equality atoms :   41 (  68 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2927,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f190,f213,f2926])).

fof(f2926,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f2925])).

fof(f2925,plain,
    ( $false
    | spl3_3 ),
    inference(trivial_inequality_removal,[],[f2924])).

fof(f2924,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(forward_demodulation,[],[f2923,f45])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f25,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2923,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)))
    | spl3_3 ),
    inference(forward_demodulation,[],[f2922,f95])).

fof(f95,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f32,f25])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f2922,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,k1_xboole_0)))
    | spl3_3 ),
    inference(forward_demodulation,[],[f2921,f48])).

fof(f48,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f24,f25])).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f2921,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)))))
    | spl3_3 ),
    inference(forward_demodulation,[],[f2751,f25])).

fof(f2751,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)),sK2)))
    | spl3_3 ),
    inference(superposition,[],[f212,f175])).

fof(f175,plain,(
    ! [X10,X8,X7,X9] : k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X9,X10))))) = k4_xboole_0(X7,k2_xboole_0(X8,k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X8,X9)),X10))) ),
    inference(forward_demodulation,[],[f174,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f174,plain,(
    ! [X10,X8,X7,X9] : k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X9,X10))))) = k4_xboole_0(X7,k2_xboole_0(X8,k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X8),X9),X10))) ),
    inference(forward_demodulation,[],[f173,f33])).

fof(f173,plain,(
    ! [X10,X8,X7,X9] : k4_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X8),X9),X10)) = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X9,X10))))) ),
    inference(forward_demodulation,[],[f150,f33])).

fof(f150,plain,(
    ! [X10,X8,X7,X9] : k4_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X8),X9),X10)) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X9,X10)))) ),
    inference(superposition,[],[f140,f33])).

fof(f140,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f37,f33])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f31,f28,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f212,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)))))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl3_3
  <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f213,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f208,f187,f210])).

fof(f187,plain,
    ( spl3_2
  <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f208,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)))))
    | spl3_2 ),
    inference(superposition,[],[f189,f33])).

fof(f189,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f187])).

fof(f190,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f185,f39,f187])).

fof(f39,plain,
    ( spl3_1
  <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f185,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f41,f33])).

fof(f41,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f42,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f34,f39])).

fof(f34,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f20,f28])).

fof(f20,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:01:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (21436)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (21429)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (21429)Refutation not found, incomplete strategy% (21429)------------------------------
% 0.21/0.50  % (21429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21429)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21429)Memory used [KB]: 1663
% 0.21/0.50  % (21429)Time elapsed: 0.093 s
% 0.21/0.50  % (21429)------------------------------
% 0.21/0.50  % (21429)------------------------------
% 0.21/0.50  % (21445)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (21433)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (21440)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (21438)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (21439)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (21437)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (21453)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (21435)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (21449)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (21451)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (21449)Refutation not found, incomplete strategy% (21449)------------------------------
% 0.21/0.52  % (21449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21449)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21449)Memory used [KB]: 10618
% 0.21/0.52  % (21449)Time elapsed: 0.115 s
% 0.21/0.52  % (21449)------------------------------
% 0.21/0.52  % (21449)------------------------------
% 0.21/0.52  % (21443)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (21441)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (21451)Refutation not found, incomplete strategy% (21451)------------------------------
% 0.21/0.52  % (21451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21450)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.53  % (21430)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.53  % (21457)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.53  % (21434)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.40/0.53  % (21431)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.40/0.53  % (21432)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.40/0.53  % (21451)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.53  
% 1.40/0.53  % (21451)Memory used [KB]: 10746
% 1.40/0.53  % (21451)Time elapsed: 0.084 s
% 1.40/0.53  % (21451)------------------------------
% 1.40/0.53  % (21451)------------------------------
% 1.40/0.53  % (21437)Refutation not found, incomplete strategy% (21437)------------------------------
% 1.40/0.53  % (21437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.53  % (21437)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.53  
% 1.40/0.53  % (21437)Memory used [KB]: 10618
% 1.40/0.53  % (21437)Time elapsed: 0.124 s
% 1.40/0.53  % (21437)------------------------------
% 1.40/0.53  % (21437)------------------------------
% 1.40/0.53  % (21446)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.54  % (21446)Refutation not found, incomplete strategy% (21446)------------------------------
% 1.40/0.54  % (21446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (21446)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (21446)Memory used [KB]: 10618
% 1.40/0.54  % (21446)Time elapsed: 0.138 s
% 1.40/0.54  % (21446)------------------------------
% 1.40/0.54  % (21446)------------------------------
% 1.40/0.54  % (21450)Refutation not found, incomplete strategy% (21450)------------------------------
% 1.40/0.54  % (21450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (21450)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (21450)Memory used [KB]: 1663
% 1.40/0.54  % (21450)Time elapsed: 0.142 s
% 1.40/0.54  % (21450)------------------------------
% 1.40/0.54  % (21450)------------------------------
% 1.40/0.54  % (21431)Refutation not found, incomplete strategy% (21431)------------------------------
% 1.40/0.54  % (21431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (21442)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.54  % (21458)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.54  % (21455)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.54  % (21431)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (21431)Memory used [KB]: 10618
% 1.40/0.54  % (21431)Time elapsed: 0.137 s
% 1.40/0.54  % (21431)------------------------------
% 1.40/0.54  % (21431)------------------------------
% 1.40/0.54  % (21447)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.54  % (21456)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.55  % (21448)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.56/0.55  % (21452)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.56/0.55  % (21444)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.56/0.55  % (21452)Refutation not found, incomplete strategy% (21452)------------------------------
% 1.56/0.55  % (21452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (21452)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  
% 1.56/0.56  % (21452)Memory used [KB]: 1663
% 1.56/0.56  % (21452)Time elapsed: 0.152 s
% 1.56/0.56  % (21452)------------------------------
% 1.56/0.56  % (21452)------------------------------
% 1.56/0.56  % (21454)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.04/0.63  % (21461)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.04/0.63  % (21462)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.04/0.65  % (21463)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.04/0.65  % (21459)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.04/0.67  % (21464)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.04/0.67  % (21459)Refutation not found, incomplete strategy% (21459)------------------------------
% 2.04/0.67  % (21459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.67  % (21459)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.67  
% 2.04/0.67  % (21459)Memory used [KB]: 6140
% 2.04/0.67  % (21459)Time elapsed: 0.114 s
% 2.04/0.67  % (21459)------------------------------
% 2.04/0.67  % (21459)------------------------------
% 2.04/0.67  % (21460)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.34/0.68  % (21465)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.34/0.69  % (21466)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.34/0.70  % (21445)Refutation found. Thanks to Tanya!
% 2.34/0.70  % SZS status Theorem for theBenchmark
% 2.34/0.70  % SZS output start Proof for theBenchmark
% 2.34/0.70  fof(f2927,plain,(
% 2.34/0.70    $false),
% 2.34/0.70    inference(avatar_sat_refutation,[],[f42,f190,f213,f2926])).
% 2.34/0.70  fof(f2926,plain,(
% 2.34/0.70    spl3_3),
% 2.34/0.70    inference(avatar_contradiction_clause,[],[f2925])).
% 2.34/0.70  fof(f2925,plain,(
% 2.34/0.70    $false | spl3_3),
% 2.34/0.70    inference(trivial_inequality_removal,[],[f2924])).
% 2.34/0.70  fof(f2924,plain,(
% 2.34/0.70    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_3),
% 2.34/0.70    inference(forward_demodulation,[],[f2923,f45])).
% 2.34/0.70  fof(f45,plain,(
% 2.34/0.70    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.34/0.70    inference(superposition,[],[f25,f22])).
% 2.34/0.70  fof(f22,plain,(
% 2.34/0.70    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.34/0.70    inference(cnf_transformation,[],[f2])).
% 2.34/0.70  fof(f2,axiom,(
% 2.34/0.70    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.34/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.34/0.70  fof(f25,plain,(
% 2.34/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.34/0.70    inference(cnf_transformation,[],[f1])).
% 2.34/0.70  fof(f1,axiom,(
% 2.34/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.34/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.34/0.70  fof(f2923,plain,(
% 2.34/0.70    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))) | spl3_3),
% 2.34/0.70    inference(forward_demodulation,[],[f2922,f95])).
% 2.34/0.70  fof(f95,plain,(
% 2.34/0.70    ( ! [X6,X7,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 2.34/0.70    inference(superposition,[],[f32,f25])).
% 2.34/0.70  fof(f32,plain,(
% 2.34/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.34/0.70    inference(cnf_transformation,[],[f12])).
% 2.34/0.70  fof(f12,axiom,(
% 2.34/0.70    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.34/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.34/0.70  fof(f2922,plain,(
% 2.34/0.70    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,k1_xboole_0))) | spl3_3),
% 2.34/0.70    inference(forward_demodulation,[],[f2921,f48])).
% 2.34/0.70  fof(f48,plain,(
% 2.34/0.70    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 2.34/0.70    inference(superposition,[],[f24,f25])).
% 2.34/0.70  fof(f24,plain,(
% 2.34/0.70    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.34/0.70    inference(cnf_transformation,[],[f9])).
% 2.34/0.70  fof(f9,axiom,(
% 2.34/0.70    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.34/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.34/0.70  fof(f2921,plain,(
% 2.34/0.70    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))))) | spl3_3),
% 2.34/0.70    inference(forward_demodulation,[],[f2751,f25])).
% 2.34/0.70  fof(f2751,plain,(
% 2.34/0.70    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)),sK2))) | spl3_3),
% 2.34/0.70    inference(superposition,[],[f212,f175])).
% 2.34/0.70  fof(f175,plain,(
% 2.34/0.70    ( ! [X10,X8,X7,X9] : (k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X9,X10))))) = k4_xboole_0(X7,k2_xboole_0(X8,k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X8,X9)),X10)))) )),
% 2.34/0.70    inference(forward_demodulation,[],[f174,f33])).
% 2.34/0.70  fof(f33,plain,(
% 2.34/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.34/0.70    inference(cnf_transformation,[],[f8])).
% 2.34/0.70  fof(f8,axiom,(
% 2.34/0.70    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.34/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.34/0.70  fof(f174,plain,(
% 2.34/0.70    ( ! [X10,X8,X7,X9] : (k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X9,X10))))) = k4_xboole_0(X7,k2_xboole_0(X8,k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X8),X9),X10)))) )),
% 2.34/0.70    inference(forward_demodulation,[],[f173,f33])).
% 2.34/0.70  fof(f173,plain,(
% 2.34/0.70    ( ! [X10,X8,X7,X9] : (k4_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X8),X9),X10)) = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X9,X10)))))) )),
% 2.34/0.70    inference(forward_demodulation,[],[f150,f33])).
% 2.34/0.70  fof(f150,plain,(
% 2.34/0.70    ( ! [X10,X8,X7,X9] : (k4_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X8),X9),X10)) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X9,X10))))) )),
% 2.34/0.70    inference(superposition,[],[f140,f33])).
% 2.34/0.70  fof(f140,plain,(
% 2.34/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 2.34/0.70    inference(forward_demodulation,[],[f37,f33])).
% 2.34/0.70  fof(f37,plain,(
% 2.34/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 2.34/0.70    inference(definition_unfolding,[],[f31,f28,f28])).
% 2.34/0.70  fof(f28,plain,(
% 2.34/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.34/0.70    inference(cnf_transformation,[],[f10])).
% 2.34/0.70  fof(f10,axiom,(
% 2.34/0.70    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.34/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.34/0.70  fof(f31,plain,(
% 2.34/0.70    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.34/0.70    inference(cnf_transformation,[],[f11])).
% 2.34/0.70  fof(f11,axiom,(
% 2.34/0.70    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.34/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.34/0.70  fof(f212,plain,(
% 2.34/0.70    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))))) | spl3_3),
% 2.34/0.70    inference(avatar_component_clause,[],[f210])).
% 2.34/0.70  fof(f210,plain,(
% 2.34/0.70    spl3_3 <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)))))),
% 2.34/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.34/0.70  fof(f213,plain,(
% 2.34/0.70    ~spl3_3 | spl3_2),
% 2.34/0.70    inference(avatar_split_clause,[],[f208,f187,f210])).
% 2.34/0.70  fof(f187,plain,(
% 2.34/0.70    spl3_2 <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))))),
% 2.34/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.34/0.70  fof(f208,plain,(
% 2.34/0.70    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))))) | spl3_2),
% 2.34/0.70    inference(superposition,[],[f189,f33])).
% 2.34/0.70  fof(f189,plain,(
% 2.34/0.70    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) | spl3_2),
% 2.34/0.70    inference(avatar_component_clause,[],[f187])).
% 2.34/0.70  fof(f190,plain,(
% 2.34/0.70    ~spl3_2 | spl3_1),
% 2.34/0.70    inference(avatar_split_clause,[],[f185,f39,f187])).
% 2.34/0.70  fof(f39,plain,(
% 2.34/0.70    spl3_1 <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))),
% 2.34/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.34/0.70  fof(f185,plain,(
% 2.34/0.70    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)))) | spl3_1),
% 2.34/0.70    inference(forward_demodulation,[],[f41,f33])).
% 2.34/0.70  fof(f41,plain,(
% 2.34/0.70    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) | spl3_1),
% 2.34/0.70    inference(avatar_component_clause,[],[f39])).
% 2.34/0.70  fof(f42,plain,(
% 2.34/0.70    ~spl3_1),
% 2.34/0.70    inference(avatar_split_clause,[],[f34,f39])).
% 2.34/0.70  fof(f34,plain,(
% 2.34/0.70    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))),
% 2.34/0.70    inference(definition_unfolding,[],[f20,f28])).
% 2.34/0.70  fof(f20,plain,(
% 2.34/0.70    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 2.34/0.70    inference(cnf_transformation,[],[f17])).
% 2.34/0.70  fof(f17,plain,(
% 2.34/0.70    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 2.34/0.70    inference(ennf_transformation,[],[f15])).
% 2.34/0.70  fof(f15,negated_conjecture,(
% 2.34/0.70    ~! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 2.34/0.70    inference(negated_conjecture,[],[f14])).
% 2.34/0.70  fof(f14,conjecture,(
% 2.34/0.70    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 2.34/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 2.34/0.70  % SZS output end Proof for theBenchmark
% 2.34/0.70  % (21445)------------------------------
% 2.34/0.70  % (21445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.34/0.70  % (21445)Termination reason: Refutation
% 2.34/0.70  
% 2.34/0.70  % (21445)Memory used [KB]: 13432
% 2.34/0.70  % (21445)Time elapsed: 0.290 s
% 2.34/0.70  % (21445)------------------------------
% 2.34/0.70  % (21445)------------------------------
% 2.34/0.70  % (21428)Success in time 0.345 s
%------------------------------------------------------------------------------
