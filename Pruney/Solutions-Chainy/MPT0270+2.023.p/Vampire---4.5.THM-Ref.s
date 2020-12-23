%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:59 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 210 expanded)
%              Number of leaves         :   12 (  60 expanded)
%              Depth                    :   27
%              Number of atoms          :  121 ( 487 expanded)
%              Number of equality atoms :   47 ( 165 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f383,plain,(
    $false ),
    inference(subsumption_resolution,[],[f382,f98])).

fof(f98,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f61,f95])).

fof(f95,plain,(
    sK1 = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f94,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f94,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f47,f87])).

fof(f87,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))
    | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f82,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK1,k1_tarski(sK0)))
      | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ) ),
    inference(forward_demodulation,[],[f81,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))
      | ~ r2_hidden(X0,k3_xboole_0(k1_tarski(sK0),sK1)) ) ),
    inference(resolution,[],[f76,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f76,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f43,f69])).

fof(f69,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f65,f41])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK1,k1_tarski(sK0)))
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(forward_demodulation,[],[f64,f44])).

fof(f64,plain,(
    ! [X0] :
      ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
      | ~ r2_hidden(X0,k3_xboole_0(k1_tarski(sK0),sK1)) ) ),
    inference(resolution,[],[f63,f50])).

fof(f63,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f37,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( r2_hidden(sK0,sK1)
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( ~ r2_hidden(sK0,sK1)
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK0,sK1)
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( ~ r2_hidden(sK0,sK1)
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f61,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f382,plain,(
    r2_hidden(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f381])).

fof(f381,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f38,f380])).

fof(f380,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(forward_demodulation,[],[f372,f39])).

fof(f372,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f47,f358])).

fof(f358,plain,(
    k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f312,f95])).

fof(f312,plain,(
    ! [X5] : k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(X5))) ),
    inference(resolution,[],[f199,f41])).

fof(f199,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(X1)))) ),
    inference(resolution,[],[f150,f50])).

fof(f150,plain,(
    ! [X3] : r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(X3))) ),
    inference(resolution,[],[f103,f51])).

fof(f103,plain,(
    ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(X0))) ),
    inference(resolution,[],[f98,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f38,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (28070)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (28073)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (28077)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (28081)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (28069)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (28098)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (28090)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (28075)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (28080)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (28071)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (28072)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (28071)Refutation not found, incomplete strategy% (28071)------------------------------
% 0.21/0.54  % (28071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28071)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28071)Memory used [KB]: 10618
% 0.21/0.54  % (28071)Time elapsed: 0.125 s
% 0.21/0.54  % (28071)------------------------------
% 0.21/0.54  % (28071)------------------------------
% 1.36/0.54  % (28082)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.54  % (28076)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.54  % (28088)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.55  % (28078)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.55  % (28084)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.55  % (28092)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.55  % (28087)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.55  % (28094)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.55  % (28074)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.55  % (28085)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.55  % (28089)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.55  % (28077)Refutation not found, incomplete strategy% (28077)------------------------------
% 1.36/0.55  % (28077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (28095)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.55  % (28077)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (28077)Memory used [KB]: 10618
% 1.36/0.55  % (28077)Time elapsed: 0.139 s
% 1.36/0.55  % (28077)------------------------------
% 1.36/0.55  % (28077)------------------------------
% 1.36/0.55  % (28086)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.55  % (28086)Refutation not found, incomplete strategy% (28086)------------------------------
% 1.36/0.55  % (28086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (28086)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (28086)Memory used [KB]: 10618
% 1.36/0.55  % (28086)Time elapsed: 0.151 s
% 1.36/0.55  % (28086)------------------------------
% 1.36/0.55  % (28086)------------------------------
% 1.54/0.56  % (28092)Refutation found. Thanks to Tanya!
% 1.54/0.56  % SZS status Theorem for theBenchmark
% 1.54/0.56  % SZS output start Proof for theBenchmark
% 1.54/0.56  fof(f383,plain,(
% 1.54/0.56    $false),
% 1.54/0.56    inference(subsumption_resolution,[],[f382,f98])).
% 1.54/0.56  fof(f98,plain,(
% 1.54/0.56    ~r2_hidden(sK0,sK1)),
% 1.54/0.56    inference(superposition,[],[f61,f95])).
% 1.54/0.56  fof(f95,plain,(
% 1.54/0.56    sK1 = k4_xboole_0(sK1,k1_tarski(sK0))),
% 1.54/0.56    inference(forward_demodulation,[],[f94,f39])).
% 1.54/0.56  fof(f39,plain,(
% 1.54/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f8])).
% 1.54/0.56  fof(f8,axiom,(
% 1.54/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.54/0.56  fof(f94,plain,(
% 1.54/0.56    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0)),
% 1.54/0.56    inference(superposition,[],[f47,f87])).
% 1.54/0.56  fof(f87,plain,(
% 1.54/0.56    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.54/0.56    inference(duplicate_literal_removal,[],[f85])).
% 1.54/0.56  fof(f85,plain,(
% 1.54/0.56    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.54/0.56    inference(resolution,[],[f82,f41])).
% 1.54/0.56  fof(f41,plain,(
% 1.54/0.56    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f32])).
% 1.54/0.56  fof(f32,plain,(
% 1.54/0.56    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f31])).
% 1.54/0.56  fof(f31,plain,(
% 1.54/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f25,plain,(
% 1.54/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.54/0.56    inference(ennf_transformation,[],[f5])).
% 1.54/0.56  fof(f5,axiom,(
% 1.54/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.54/0.56  fof(f82,plain,(
% 1.54/0.56    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k1_tarski(sK0))) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f81,f44])).
% 1.54/0.56  fof(f44,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f1])).
% 1.54/0.56  fof(f1,axiom,(
% 1.54/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.54/0.56  fof(f81,plain,(
% 1.54/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) | ~r2_hidden(X0,k3_xboole_0(k1_tarski(sK0),sK1))) )),
% 1.54/0.56    inference(resolution,[],[f76,f50])).
% 1.54/0.56  fof(f50,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f34])).
% 1.54/0.56  fof(f34,plain,(
% 1.54/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f33])).
% 1.54/0.56  fof(f33,plain,(
% 1.54/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f26,plain,(
% 1.54/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.54/0.56    inference(ennf_transformation,[],[f23])).
% 1.54/0.56  fof(f23,plain,(
% 1.54/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.54/0.56    inference(rectify,[],[f4])).
% 1.54/0.56  fof(f4,axiom,(
% 1.54/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.54/0.56  fof(f76,plain,(
% 1.54/0.56    r1_xboole_0(k1_tarski(sK0),sK1) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.54/0.56    inference(superposition,[],[f43,f69])).
% 1.54/0.56  fof(f69,plain,(
% 1.54/0.56    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.54/0.56    inference(resolution,[],[f65,f41])).
% 1.54/0.56  fof(f65,plain,(
% 1.54/0.56    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k1_tarski(sK0))) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f64,f44])).
% 1.54/0.56  fof(f64,plain,(
% 1.54/0.56    ( ! [X0] : (k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | ~r2_hidden(X0,k3_xboole_0(k1_tarski(sK0),sK1))) )),
% 1.54/0.56    inference(resolution,[],[f63,f50])).
% 1.54/0.56  fof(f63,plain,(
% 1.54/0.56    r1_xboole_0(k1_tarski(sK0),sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.54/0.56    inference(resolution,[],[f37,f51])).
% 1.54/0.56  fof(f51,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f27])).
% 1.54/0.56  fof(f27,plain,(
% 1.54/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f18])).
% 1.54/0.56  fof(f18,axiom,(
% 1.54/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.54/0.56  fof(f37,plain,(
% 1.54/0.56    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.54/0.56    inference(cnf_transformation,[],[f30])).
% 1.54/0.56  fof(f30,plain,(
% 1.54/0.56    (r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 1.54/0.56  fof(f29,plain,(
% 1.54/0.56    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f28,plain,(
% 1.54/0.56    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.54/0.56    inference(nnf_transformation,[],[f24])).
% 1.54/0.56  fof(f24,plain,(
% 1.54/0.56    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f21])).
% 1.54/0.56  fof(f21,negated_conjecture,(
% 1.54/0.56    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.54/0.56    inference(negated_conjecture,[],[f20])).
% 1.54/0.56  fof(f20,conjecture,(
% 1.54/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.54/0.56  fof(f43,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f9])).
% 1.54/0.56  fof(f9,axiom,(
% 1.54/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.54/0.56  fof(f47,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f6])).
% 1.54/0.56  fof(f6,axiom,(
% 1.54/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.56  fof(f61,plain,(
% 1.54/0.56    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.54/0.56    inference(equality_resolution,[],[f55])).
% 1.54/0.56  fof(f55,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f36])).
% 1.54/0.56  fof(f36,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.54/0.56    inference(flattening,[],[f35])).
% 1.54/0.56  fof(f35,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.54/0.56    inference(nnf_transformation,[],[f19])).
% 1.54/0.56  fof(f19,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.54/0.56  fof(f382,plain,(
% 1.54/0.56    r2_hidden(sK0,sK1)),
% 1.54/0.56    inference(trivial_inequality_removal,[],[f381])).
% 1.54/0.56  fof(f381,plain,(
% 1.54/0.56    k1_tarski(sK0) != k1_tarski(sK0) | r2_hidden(sK0,sK1)),
% 1.54/0.56    inference(backward_demodulation,[],[f38,f380])).
% 1.54/0.56  fof(f380,plain,(
% 1.54/0.56    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.54/0.56    inference(forward_demodulation,[],[f372,f39])).
% 1.54/0.56  fof(f372,plain,(
% 1.54/0.56    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 1.54/0.56    inference(superposition,[],[f47,f358])).
% 1.54/0.56  fof(f358,plain,(
% 1.54/0.56    k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.54/0.56    inference(superposition,[],[f312,f95])).
% 1.54/0.56  fof(f312,plain,(
% 1.54/0.56    ( ! [X5] : (k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(X5)))) )),
% 1.54/0.56    inference(resolution,[],[f199,f41])).
% 1.54/0.56  fof(f199,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(X1))))) )),
% 1.54/0.56    inference(resolution,[],[f150,f50])).
% 1.54/0.56  fof(f150,plain,(
% 1.54/0.56    ( ! [X3] : (r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(X3)))) )),
% 1.54/0.56    inference(resolution,[],[f103,f51])).
% 1.54/0.56  fof(f103,plain,(
% 1.54/0.56    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(X0)))) )),
% 1.54/0.56    inference(resolution,[],[f98,f54])).
% 1.54/0.56  fof(f54,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f36])).
% 1.54/0.56  fof(f38,plain,(
% 1.54/0.56    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.54/0.56    inference(cnf_transformation,[],[f30])).
% 1.54/0.56  % SZS output end Proof for theBenchmark
% 1.54/0.56  % (28092)------------------------------
% 1.54/0.56  % (28092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (28092)Termination reason: Refutation
% 1.54/0.56  
% 1.54/0.56  % (28092)Memory used [KB]: 1918
% 1.54/0.56  % (28092)Time elapsed: 0.141 s
% 1.54/0.56  % (28092)------------------------------
% 1.54/0.56  % (28092)------------------------------
% 1.54/0.56  % (28068)Success in time 0.193 s
%------------------------------------------------------------------------------
