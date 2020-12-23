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
% DateTime   : Thu Dec  3 12:44:39 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 422 expanded)
%              Number of leaves         :   19 ( 119 expanded)
%              Depth                    :   17
%              Number of atoms          :  227 (1027 expanded)
%              Number of equality atoms :   98 ( 465 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f704,plain,(
    $false ),
    inference(global_subsumption,[],[f73,f250,f703])).

fof(f703,plain,(
    sK0 = sK1 ),
    inference(backward_demodulation,[],[f674,f697])).

fof(f697,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f268,f689])).

fof(f689,plain,(
    sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f414,f674])).

fof(f414,plain,(
    sK0 = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f406,f285])).

fof(f285,plain,(
    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f151,f276])).

fof(f276,plain,(
    k3_subset_1(sK0,sK1) = k3_xboole_0(sK0,k3_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f155,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

% (2657)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (2644)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (2661)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% (2655)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (2656)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (2667)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (2648)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (2667)Refutation not found, incomplete strategy% (2667)------------------------------
% (2667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2667)Termination reason: Refutation not found, incomplete strategy

% (2667)Memory used [KB]: 1663
% (2667)Time elapsed: 0.001 s
% (2667)------------------------------
% (2667)------------------------------
% (2662)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (2639)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% (2664)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (2653)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f155,plain,(
    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK0) ),
    inference(resolution,[],[f152,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f152,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK0) ),
    inference(superposition,[],[f65,f141])).

fof(f141,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f67,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f151,plain,(
    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))) ),
    inference(superposition,[],[f62,f141])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f46,f47,f47])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f406,plain,(
    sK0 = k5_xboole_0(k5_xboole_0(sK0,k3_subset_1(sK0,sK1)),k3_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f343,f276])).

fof(f343,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f342,f74])).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f64,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f40,f47])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

% (2653)Refutation not found, incomplete strategy% (2653)------------------------------
% (2653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

% (2653)Termination reason: Refutation not found, incomplete strategy

% (2653)Memory used [KB]: 10618
fof(f342,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f339,f135])).

% (2653)Time elapsed: 0.176 s
% (2653)------------------------------
% (2653)------------------------------
fof(f135,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f134,f88])).

fof(f88,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f52,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f134,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f129,f74])).

fof(f129,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0))) ),
    inference(superposition,[],[f62,f94])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f87,f44])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f339,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(backward_demodulation,[],[f176,f322])).

fof(f322,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f89,f44])).

fof(f89,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2) ),
    inference(resolution,[],[f52,f65])).

fof(f176,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) ),
    inference(forward_demodulation,[],[f160,f44])).

fof(f160,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f66,f62])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f61,f61])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f268,plain,(
    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),sK1) ),
    inference(resolution,[],[f246,f52])).

fof(f246,plain,(
    r1_tarski(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),sK1) ),
    inference(superposition,[],[f65,f242])).

fof(f242,plain,(
    k3_subset_1(sK0,sK1) = k3_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f241,f238])).

fof(f238,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    inference(forward_demodulation,[],[f232,f44])).

fof(f232,plain,
    ( r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f152,f91])).

fof(f91,plain,
    ( sK0 = sK1
    | k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f52,f72])).

fof(f72,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f35,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f35,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f241,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    inference(forward_demodulation,[],[f237,f44])).

fof(f237,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    inference(trivial_inequality_removal,[],[f234])).

fof(f234,plain,
    ( sK0 != sK0
    | ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f73,f91])).

fof(f674,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f671,f44])).

fof(f671,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f273,f34])).

fof(f273,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k3_xboole_0(X2,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f271,f37])).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f271,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f92,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f92,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k1_zfmisc_1(X7))
      | k3_xboole_0(X6,X7) = X6 ) ),
    inference(resolution,[],[f52,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f250,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f118,f242])).

fof(f118,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f65,f62])).

fof(f73,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f36,f39])).

fof(f36,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:34:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (2660)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (2651)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (2642)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.56  % (2658)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.57  % (2666)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.57  % (2649)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (2641)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.57  % (2643)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (2649)Refutation not found, incomplete strategy% (2649)------------------------------
% 0.22/0.57  % (2649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (2640)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.57  % (2649)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (2649)Memory used [KB]: 10618
% 0.22/0.57  % (2649)Time elapsed: 0.141 s
% 0.22/0.57  % (2649)------------------------------
% 0.22/0.57  % (2649)------------------------------
% 0.22/0.57  % (2646)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.57  % (2647)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.58  % (2666)Refutation not found, incomplete strategy% (2666)------------------------------
% 0.22/0.58  % (2666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (2647)Refutation not found, incomplete strategy% (2647)------------------------------
% 0.22/0.58  % (2647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (2647)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (2647)Memory used [KB]: 10746
% 0.22/0.58  % (2647)Time elapsed: 0.152 s
% 0.22/0.58  % (2647)------------------------------
% 0.22/0.58  % (2647)------------------------------
% 0.22/0.58  % (2666)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (2666)Memory used [KB]: 10746
% 0.22/0.58  % (2666)Time elapsed: 0.152 s
% 0.22/0.58  % (2666)------------------------------
% 0.22/0.58  % (2666)------------------------------
% 0.22/0.58  % (2652)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.60/0.58  % (2638)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.60/0.58  % (2638)Refutation not found, incomplete strategy% (2638)------------------------------
% 1.60/0.58  % (2638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (2638)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (2638)Memory used [KB]: 1663
% 1.60/0.58  % (2638)Time elapsed: 0.126 s
% 1.60/0.58  % (2638)------------------------------
% 1.60/0.58  % (2638)------------------------------
% 1.60/0.59  % (2637)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.60/0.59  % (2660)Refutation found. Thanks to Tanya!
% 1.60/0.59  % SZS status Theorem for theBenchmark
% 1.60/0.59  % SZS output start Proof for theBenchmark
% 1.60/0.59  fof(f704,plain,(
% 1.60/0.59    $false),
% 1.60/0.59    inference(global_subsumption,[],[f73,f250,f703])).
% 1.60/0.59  fof(f703,plain,(
% 1.60/0.59    sK0 = sK1),
% 1.60/0.59    inference(backward_demodulation,[],[f674,f697])).
% 1.60/0.59  fof(f697,plain,(
% 1.60/0.59    sK0 = k3_xboole_0(sK0,sK1)),
% 1.60/0.59    inference(backward_demodulation,[],[f268,f689])).
% 1.60/0.59  fof(f689,plain,(
% 1.60/0.59    sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 1.60/0.59    inference(backward_demodulation,[],[f414,f674])).
% 1.60/0.59  fof(f414,plain,(
% 1.60/0.59    sK0 = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))),
% 1.60/0.59    inference(forward_demodulation,[],[f406,f285])).
% 1.60/0.59  fof(f285,plain,(
% 1.60/0.59    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k3_subset_1(sK0,sK1))),
% 1.60/0.59    inference(backward_demodulation,[],[f151,f276])).
% 1.60/0.59  fof(f276,plain,(
% 1.60/0.59    k3_subset_1(sK0,sK1) = k3_xboole_0(sK0,k3_subset_1(sK0,sK1))),
% 1.60/0.59    inference(superposition,[],[f155,f44])).
% 1.60/0.59  fof(f44,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f2])).
% 1.60/0.59  fof(f2,axiom,(
% 1.60/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.60/0.59  % (2657)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.60/0.59  % (2644)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.60/0.59  % (2661)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.60/0.59  % (2655)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.60/0.59  % (2656)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.60/0.59  % (2667)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.60/0.59  % (2648)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.60/0.59  % (2667)Refutation not found, incomplete strategy% (2667)------------------------------
% 1.60/0.59  % (2667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (2667)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.59  
% 1.60/0.59  % (2667)Memory used [KB]: 1663
% 1.60/0.59  % (2667)Time elapsed: 0.001 s
% 1.60/0.59  % (2667)------------------------------
% 1.60/0.59  % (2667)------------------------------
% 1.60/0.59  % (2662)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.60/0.60  % (2639)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.60/0.60  % (2664)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.60/0.60  % (2653)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.60/0.60  fof(f155,plain,(
% 1.60/0.60    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK0)),
% 1.60/0.60    inference(resolution,[],[f152,f52])).
% 1.60/0.60  fof(f52,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.60/0.60    inference(cnf_transformation,[],[f21])).
% 1.60/0.60  fof(f21,plain,(
% 1.60/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.60/0.60    inference(ennf_transformation,[],[f6])).
% 1.60/0.60  fof(f6,axiom,(
% 1.60/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.60/0.60  fof(f152,plain,(
% 1.60/0.60    r1_tarski(k3_subset_1(sK0,sK1),sK0)),
% 1.60/0.60    inference(superposition,[],[f65,f141])).
% 1.60/0.60  fof(f141,plain,(
% 1.60/0.60    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.60/0.60    inference(resolution,[],[f67,f34])).
% 1.60/0.60  fof(f34,plain,(
% 1.60/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.60/0.60    inference(cnf_transformation,[],[f26])).
% 1.60/0.60  fof(f26,plain,(
% 1.60/0.60    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.60/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 1.60/0.60  fof(f25,plain,(
% 1.60/0.60    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.60/0.60    introduced(choice_axiom,[])).
% 1.60/0.60  fof(f24,plain,(
% 1.60/0.60    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.60    inference(flattening,[],[f23])).
% 1.60/0.60  fof(f23,plain,(
% 1.60/0.60    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.60    inference(nnf_transformation,[],[f19])).
% 1.60/0.60  fof(f19,plain,(
% 1.60/0.60    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.60    inference(ennf_transformation,[],[f18])).
% 1.60/0.60  fof(f18,negated_conjecture,(
% 1.60/0.60    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.60/0.60    inference(negated_conjecture,[],[f17])).
% 1.60/0.60  fof(f17,conjecture,(
% 1.60/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 1.60/0.60  fof(f67,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.60/0.60    inference(definition_unfolding,[],[f53,f47])).
% 1.60/0.60  fof(f47,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f4])).
% 1.60/0.60  fof(f4,axiom,(
% 1.60/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.60/0.60  fof(f53,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f22])).
% 1.60/0.60  fof(f22,plain,(
% 1.60/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.60    inference(ennf_transformation,[],[f15])).
% 1.60/0.60  fof(f15,axiom,(
% 1.60/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.60/0.60  fof(f65,plain,(
% 1.60/0.60    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.60/0.60    inference(definition_unfolding,[],[f42,f47])).
% 1.60/0.60  fof(f42,plain,(
% 1.60/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f8])).
% 1.60/0.60  fof(f8,axiom,(
% 1.60/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.60/0.60  fof(f151,plain,(
% 1.60/0.60    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1)))),
% 1.60/0.60    inference(superposition,[],[f62,f141])).
% 1.60/0.60  fof(f62,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 1.60/0.60    inference(definition_unfolding,[],[f46,f47,f47])).
% 1.60/0.60  fof(f46,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f9])).
% 1.60/0.60  fof(f9,axiom,(
% 1.60/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.60/0.60  fof(f406,plain,(
% 1.60/0.60    sK0 = k5_xboole_0(k5_xboole_0(sK0,k3_subset_1(sK0,sK1)),k3_subset_1(sK0,sK1))),
% 1.60/0.60    inference(superposition,[],[f343,f276])).
% 1.60/0.60  fof(f343,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0) )),
% 1.60/0.60    inference(forward_demodulation,[],[f342,f74])).
% 1.60/0.60  fof(f74,plain,(
% 1.60/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.60/0.60    inference(forward_demodulation,[],[f64,f63])).
% 1.60/0.60  fof(f63,plain,(
% 1.60/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.60/0.60    inference(definition_unfolding,[],[f40,f47])).
% 1.60/0.60  fof(f40,plain,(
% 1.60/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f10])).
% 1.60/0.60  fof(f10,axiom,(
% 1.60/0.60    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.60/0.60  fof(f64,plain,(
% 1.60/0.60    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 1.60/0.60    inference(definition_unfolding,[],[f41,f61])).
% 1.60/0.60  fof(f61,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.60/0.60    inference(definition_unfolding,[],[f45,f47])).
% 1.60/0.60  fof(f45,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f11])).
% 1.60/0.60  fof(f11,axiom,(
% 1.60/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.60/0.60  fof(f41,plain,(
% 1.60/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.60/0.60    inference(cnf_transformation,[],[f5])).
% 1.60/0.60  % (2653)Refutation not found, incomplete strategy% (2653)------------------------------
% 1.60/0.60  % (2653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  fof(f5,axiom,(
% 1.60/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.60/0.60  % (2653)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.60  
% 1.60/0.60  % (2653)Memory used [KB]: 10618
% 1.60/0.60  fof(f342,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))) )),
% 1.60/0.60    inference(forward_demodulation,[],[f339,f135])).
% 1.60/0.60  % (2653)Time elapsed: 0.176 s
% 1.60/0.60  % (2653)------------------------------
% 1.60/0.60  % (2653)------------------------------
% 1.60/0.60  fof(f135,plain,(
% 1.60/0.60    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.60/0.60    inference(forward_demodulation,[],[f134,f88])).
% 1.60/0.60  fof(f88,plain,(
% 1.60/0.60    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 1.60/0.60    inference(resolution,[],[f52,f68])).
% 1.60/0.60  fof(f68,plain,(
% 1.60/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.60/0.60    inference(equality_resolution,[],[f55])).
% 1.60/0.60  fof(f55,plain,(
% 1.60/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.60/0.60    inference(cnf_transformation,[],[f29])).
% 1.60/0.60  fof(f29,plain,(
% 1.60/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.60    inference(flattening,[],[f28])).
% 1.60/0.60  fof(f28,plain,(
% 1.60/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.60    inference(nnf_transformation,[],[f3])).
% 1.60/0.60  fof(f3,axiom,(
% 1.60/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.60  fof(f134,plain,(
% 1.60/0.60    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,X1))) )),
% 1.60/0.60    inference(forward_demodulation,[],[f129,f74])).
% 1.60/0.60  fof(f129,plain,(
% 1.60/0.60    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0)))) )),
% 1.60/0.60    inference(superposition,[],[f62,f94])).
% 1.60/0.60  fof(f94,plain,(
% 1.60/0.60    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.60/0.60    inference(superposition,[],[f87,f44])).
% 1.60/0.60  fof(f87,plain,(
% 1.60/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.60/0.60    inference(resolution,[],[f52,f38])).
% 1.60/0.60  fof(f38,plain,(
% 1.60/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f7])).
% 1.60/0.60  fof(f7,axiom,(
% 1.60/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.60/0.60  fof(f339,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 1.60/0.60    inference(backward_demodulation,[],[f176,f322])).
% 1.60/0.60  fof(f322,plain,(
% 1.60/0.60    ( ! [X2,X3] : (k5_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) )),
% 1.60/0.60    inference(superposition,[],[f89,f44])).
% 1.60/0.60  fof(f89,plain,(
% 1.60/0.60    ( ! [X2,X3] : (k5_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2)) )),
% 1.60/0.60    inference(resolution,[],[f52,f65])).
% 1.60/0.60  fof(f176,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))))) )),
% 1.60/0.60    inference(forward_demodulation,[],[f160,f44])).
% 1.60/0.60  fof(f160,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))) )),
% 1.60/0.60    inference(superposition,[],[f66,f62])).
% 1.60/0.60  fof(f66,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.60/0.60    inference(definition_unfolding,[],[f43,f61,f61])).
% 1.60/0.60  fof(f43,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f1])).
% 1.60/0.60  fof(f1,axiom,(
% 1.60/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.60/0.60  fof(f268,plain,(
% 1.60/0.60    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),sK1)),
% 1.60/0.60    inference(resolution,[],[f246,f52])).
% 1.60/0.60  fof(f246,plain,(
% 1.60/0.60    r1_tarski(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),sK1)),
% 1.60/0.60    inference(superposition,[],[f65,f242])).
% 1.60/0.60  fof(f242,plain,(
% 1.60/0.60    k3_subset_1(sK0,sK1) = k3_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 1.60/0.60    inference(subsumption_resolution,[],[f241,f238])).
% 1.60/0.60  fof(f238,plain,(
% 1.60/0.60    k3_subset_1(sK0,sK1) = k3_xboole_0(sK1,k3_subset_1(sK0,sK1)) | r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 1.60/0.60    inference(forward_demodulation,[],[f232,f44])).
% 1.60/0.60  fof(f232,plain,(
% 1.60/0.60    r1_tarski(k3_subset_1(sK0,sK0),sK0) | k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 1.60/0.60    inference(superposition,[],[f152,f91])).
% 1.60/0.60  fof(f91,plain,(
% 1.60/0.60    sK0 = sK1 | k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 1.60/0.60    inference(resolution,[],[f52,f72])).
% 1.60/0.60  fof(f72,plain,(
% 1.60/0.60    r1_tarski(k3_subset_1(sK0,sK1),sK1) | sK0 = sK1),
% 1.60/0.60    inference(backward_demodulation,[],[f35,f39])).
% 1.60/0.60  fof(f39,plain,(
% 1.60/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.60/0.60    inference(cnf_transformation,[],[f14])).
% 1.60/0.60  fof(f14,axiom,(
% 1.60/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.60/0.60  fof(f35,plain,(
% 1.60/0.60    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.60/0.60    inference(cnf_transformation,[],[f26])).
% 1.60/0.60  fof(f241,plain,(
% 1.60/0.60    k3_subset_1(sK0,sK1) = k3_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 1.60/0.60    inference(forward_demodulation,[],[f237,f44])).
% 1.60/0.60  fof(f237,plain,(
% 1.60/0.60    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 1.60/0.60    inference(trivial_inequality_removal,[],[f234])).
% 1.60/0.60  fof(f234,plain,(
% 1.60/0.60    sK0 != sK0 | ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 1.60/0.60    inference(superposition,[],[f73,f91])).
% 1.60/0.60  fof(f674,plain,(
% 1.60/0.60    sK1 = k3_xboole_0(sK0,sK1)),
% 1.60/0.60    inference(superposition,[],[f671,f44])).
% 1.60/0.60  fof(f671,plain,(
% 1.60/0.60    sK1 = k3_xboole_0(sK1,sK0)),
% 1.60/0.60    inference(resolution,[],[f273,f34])).
% 1.60/0.60  fof(f273,plain,(
% 1.60/0.60    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_xboole_0(X2,X3) = X2) )),
% 1.60/0.60    inference(subsumption_resolution,[],[f271,f37])).
% 1.60/0.60  fof(f37,plain,(
% 1.60/0.60    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f16])).
% 1.60/0.60  fof(f16,axiom,(
% 1.60/0.60    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.60/0.60  fof(f271,plain,(
% 1.60/0.60    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | v1_xboole_0(k1_zfmisc_1(X3))) )),
% 1.60/0.60    inference(resolution,[],[f92,f48])).
% 1.60/0.60  fof(f48,plain,(
% 1.60/0.60    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f27])).
% 1.60/0.60  fof(f27,plain,(
% 1.60/0.60    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.60/0.60    inference(nnf_transformation,[],[f20])).
% 1.60/0.60  fof(f20,plain,(
% 1.60/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.60/0.60    inference(ennf_transformation,[],[f13])).
% 1.60/0.60  fof(f13,axiom,(
% 1.60/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.60/0.60  fof(f92,plain,(
% 1.60/0.60    ( ! [X6,X7] : (~r2_hidden(X6,k1_zfmisc_1(X7)) | k3_xboole_0(X6,X7) = X6) )),
% 1.60/0.60    inference(resolution,[],[f52,f71])).
% 1.60/0.60  fof(f71,plain,(
% 1.60/0.60    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.60/0.60    inference(equality_resolution,[],[f57])).
% 1.60/0.60  fof(f57,plain,(
% 1.60/0.60    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.60/0.60    inference(cnf_transformation,[],[f33])).
% 1.60/0.60  fof(f33,plain,(
% 1.60/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.60/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 1.60/0.60  fof(f32,plain,(
% 1.60/0.60    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.60/0.60    introduced(choice_axiom,[])).
% 1.60/0.60  fof(f31,plain,(
% 1.60/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.60/0.60    inference(rectify,[],[f30])).
% 1.60/0.60  fof(f30,plain,(
% 1.60/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.60/0.60    inference(nnf_transformation,[],[f12])).
% 1.60/0.60  fof(f12,axiom,(
% 1.60/0.60    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.60/0.60  fof(f250,plain,(
% 1.60/0.60    r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.60/0.60    inference(superposition,[],[f118,f242])).
% 1.60/0.60  fof(f118,plain,(
% 1.60/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.60/0.60    inference(superposition,[],[f65,f62])).
% 1.60/0.60  fof(f73,plain,(
% 1.60/0.60    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.60/0.60    inference(backward_demodulation,[],[f36,f39])).
% 1.60/0.60  fof(f36,plain,(
% 1.60/0.60    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.60/0.60    inference(cnf_transformation,[],[f26])).
% 1.60/0.60  % SZS output end Proof for theBenchmark
% 1.60/0.60  % (2660)------------------------------
% 1.60/0.60  % (2660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (2660)Termination reason: Refutation
% 1.60/0.60  
% 1.60/0.60  % (2660)Memory used [KB]: 6524
% 1.60/0.60  % (2660)Time elapsed: 0.168 s
% 1.60/0.60  % (2660)------------------------------
% 1.60/0.60  % (2660)------------------------------
% 1.60/0.60  % (2659)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.60/0.60  % (2636)Success in time 0.236 s
%------------------------------------------------------------------------------
