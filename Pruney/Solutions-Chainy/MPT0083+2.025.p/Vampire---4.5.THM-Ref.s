%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:14 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   55 (  89 expanded)
%              Number of leaves         :   14 (  27 expanded)
%              Depth                    :   15
%              Number of atoms          :   88 ( 160 expanded)
%              Number of equality atoms :   29 (  45 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f396,plain,(
    $false ),
    inference(subsumption_resolution,[],[f395,f52])).

fof(f52,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f41,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f395,plain,(
    r2_hidden(sK4(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f393,f35])).

fof(f393,plain,(
    r2_hidden(sK4(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f83,f373])).

fof(f373,plain,(
    ! [X22] : k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(X22,sK1)) ),
    inference(superposition,[],[f186,f209])).

fof(f209,plain,(
    sK1 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f204,f36])).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f204,plain,(
    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f39,f188])).

fof(f188,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f168,f79])).

fof(f79,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f75,f36])).

fof(f75,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f39,f66])).

fof(f66,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f50,f32])).

fof(f32,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f168,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f47,f56])).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f45,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f186,plain,(
    ! [X6,X7,X5] : k1_xboole_0 = k3_xboole_0(X7,k3_xboole_0(X5,k4_xboole_0(X6,X7))) ),
    inference(superposition,[],[f168,f47])).

fof(f83,plain,(
    r2_hidden(sK4(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(sK2,sK1)))) ),
    inference(forward_demodulation,[],[f81,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f81,plain,(
    r2_hidden(sK4(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))) ),
    inference(resolution,[],[f40,f33])).

fof(f33,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (2940)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (2937)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.48  % (2956)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.49  % (2956)Refutation not found, incomplete strategy% (2956)------------------------------
% 0.20/0.49  % (2956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (2938)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (2936)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (2936)Refutation not found, incomplete strategy% (2936)------------------------------
% 0.20/0.49  % (2936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (2936)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (2936)Memory used [KB]: 10490
% 0.20/0.49  % (2936)Time elapsed: 0.073 s
% 0.20/0.49  % (2936)------------------------------
% 0.20/0.49  % (2936)------------------------------
% 0.20/0.49  % (2945)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (2935)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (2946)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.50  % (2956)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (2956)Memory used [KB]: 10618
% 0.20/0.50  % (2956)Time elapsed: 0.073 s
% 0.20/0.50  % (2956)------------------------------
% 0.20/0.50  % (2956)------------------------------
% 0.20/0.50  % (2933)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (2948)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  % (2953)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.50  % (2953)Refutation not found, incomplete strategy% (2953)------------------------------
% 0.20/0.50  % (2953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (2953)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (2953)Memory used [KB]: 6012
% 0.20/0.50  % (2953)Time elapsed: 0.096 s
% 0.20/0.50  % (2953)------------------------------
% 0.20/0.50  % (2953)------------------------------
% 0.20/0.51  % (2954)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.51  % (2941)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.51  % (2934)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (2949)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (2944)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.52  % (2943)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.52  % (2939)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.52  % (2955)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.52  % (2952)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.52  % (2942)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.31/0.53  % (2952)Refutation found. Thanks to Tanya!
% 1.31/0.53  % SZS status Theorem for theBenchmark
% 1.31/0.53  % SZS output start Proof for theBenchmark
% 1.31/0.53  fof(f396,plain,(
% 1.31/0.53    $false),
% 1.31/0.53    inference(subsumption_resolution,[],[f395,f52])).
% 1.31/0.53  fof(f52,plain,(
% 1.31/0.53    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f51,f34])).
% 1.31/0.53  fof(f34,plain,(
% 1.31/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f11])).
% 1.31/0.53  fof(f11,axiom,(
% 1.31/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.31/0.53  fof(f51,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.31/0.53    inference(superposition,[],[f41,f35])).
% 1.31/0.53  fof(f35,plain,(
% 1.31/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f6])).
% 1.31/0.53  fof(f6,axiom,(
% 1.31/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.31/0.53  fof(f41,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f29])).
% 1.31/0.53  fof(f29,plain,(
% 1.31/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.31/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f28])).
% 1.31/0.53  fof(f28,plain,(
% 1.31/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f20,plain,(
% 1.31/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.31/0.53    inference(ennf_transformation,[],[f15])).
% 1.31/0.53  fof(f15,plain,(
% 1.31/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.53    inference(rectify,[],[f2])).
% 1.31/0.53  fof(f2,axiom,(
% 1.31/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.31/0.53  fof(f395,plain,(
% 1.31/0.53    r2_hidden(sK4(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)),k1_xboole_0)),
% 1.31/0.53    inference(forward_demodulation,[],[f393,f35])).
% 1.31/0.53  fof(f393,plain,(
% 1.31/0.53    r2_hidden(sK4(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,k1_xboole_0))),
% 1.31/0.53    inference(backward_demodulation,[],[f83,f373])).
% 1.31/0.53  fof(f373,plain,(
% 1.31/0.53    ( ! [X22] : (k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(X22,sK1))) )),
% 1.31/0.53    inference(superposition,[],[f186,f209])).
% 1.31/0.53  fof(f209,plain,(
% 1.31/0.53    sK1 = k4_xboole_0(sK1,sK0)),
% 1.31/0.53    inference(forward_demodulation,[],[f204,f36])).
% 1.31/0.53  fof(f36,plain,(
% 1.31/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.31/0.53    inference(cnf_transformation,[],[f8])).
% 1.31/0.53  fof(f8,axiom,(
% 1.31/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.31/0.53  fof(f204,plain,(
% 1.31/0.53    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.31/0.53    inference(superposition,[],[f39,f188])).
% 1.31/0.53  fof(f188,plain,(
% 1.31/0.53    k1_xboole_0 = k3_xboole_0(sK1,sK0)),
% 1.31/0.53    inference(superposition,[],[f168,f79])).
% 1.31/0.53  fof(f79,plain,(
% 1.31/0.53    sK0 = k4_xboole_0(sK0,sK1)),
% 1.31/0.53    inference(forward_demodulation,[],[f75,f36])).
% 1.31/0.53  fof(f75,plain,(
% 1.31/0.53    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.31/0.53    inference(superposition,[],[f39,f66])).
% 1.31/0.53  fof(f66,plain,(
% 1.31/0.53    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.31/0.53    inference(resolution,[],[f50,f32])).
% 1.31/0.53  fof(f32,plain,(
% 1.31/0.53    r1_xboole_0(sK0,sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f25])).
% 1.31/0.53  fof(f25,plain,(
% 1.31/0.53    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 1.31/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f24])).
% 1.31/0.53  fof(f24,plain,(
% 1.31/0.53    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f18,plain,(
% 1.31/0.53    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f14])).
% 1.31/0.53  fof(f14,negated_conjecture,(
% 1.31/0.53    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 1.31/0.53    inference(negated_conjecture,[],[f13])).
% 1.31/0.53  fof(f13,conjecture,(
% 1.31/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).
% 1.31/0.53  fof(f50,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.31/0.53    inference(resolution,[],[f41,f37])).
% 1.31/0.53  fof(f37,plain,(
% 1.31/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.31/0.53    inference(cnf_transformation,[],[f27])).
% 1.31/0.53  fof(f27,plain,(
% 1.31/0.53    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.31/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f26])).
% 1.31/0.53  fof(f26,plain,(
% 1.31/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f19,plain,(
% 1.31/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.31/0.53    inference(ennf_transformation,[],[f3])).
% 1.31/0.53  fof(f3,axiom,(
% 1.31/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.31/0.53  fof(f168,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.31/0.53    inference(superposition,[],[f47,f56])).
% 1.31/0.53  fof(f56,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 1.31/0.53    inference(resolution,[],[f45,f38])).
% 1.31/0.53  fof(f38,plain,(
% 1.31/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f5])).
% 1.31/0.53  fof(f5,axiom,(
% 1.31/0.53    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.31/0.53  fof(f45,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f22])).
% 1.31/0.53  fof(f22,plain,(
% 1.31/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f17])).
% 1.31/0.53  fof(f17,plain,(
% 1.31/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 1.31/0.53    inference(unused_predicate_definition_removal,[],[f7])).
% 1.31/0.53  fof(f7,axiom,(
% 1.31/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.31/0.53  fof(f47,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f10])).
% 1.31/0.53  fof(f10,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.31/0.53  fof(f39,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f9])).
% 1.31/0.53  fof(f9,axiom,(
% 1.31/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.31/0.53  fof(f186,plain,(
% 1.31/0.53    ( ! [X6,X7,X5] : (k1_xboole_0 = k3_xboole_0(X7,k3_xboole_0(X5,k4_xboole_0(X6,X7)))) )),
% 1.31/0.53    inference(superposition,[],[f168,f47])).
% 1.31/0.53  fof(f83,plain,(
% 1.31/0.53    r2_hidden(sK4(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(sK2,sK1))))),
% 1.31/0.53    inference(forward_demodulation,[],[f81,f48])).
% 1.31/0.53  fof(f48,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f4])).
% 1.31/0.53  fof(f4,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.31/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.31/0.53  fof(f81,plain,(
% 1.31/0.53    r2_hidden(sK4(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)),k3_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)))),
% 1.31/0.53    inference(resolution,[],[f40,f33])).
% 1.31/0.53  fof(f33,plain,(
% 1.31/0.53    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 1.31/0.53    inference(cnf_transformation,[],[f25])).
% 1.31/0.53  fof(f40,plain,(
% 1.31/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f29])).
% 1.31/0.53  % SZS output end Proof for theBenchmark
% 1.31/0.53  % (2952)------------------------------
% 1.31/0.53  % (2952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (2952)Termination reason: Refutation
% 1.31/0.53  
% 1.31/0.53  % (2952)Memory used [KB]: 6396
% 1.31/0.53  % (2952)Time elapsed: 0.112 s
% 1.31/0.53  % (2952)------------------------------
% 1.31/0.53  % (2952)------------------------------
% 1.31/0.53  % (2932)Success in time 0.168 s
%------------------------------------------------------------------------------
