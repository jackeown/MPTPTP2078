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
% DateTime   : Thu Dec  3 12:40:59 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   49 (  88 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :   91 ( 174 expanded)
%              Number of equality atoms :   47 (  90 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(subsumption_resolution,[],[f123,f88])).

fof(f88,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f34,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f34,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
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

fof(f123,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f56,f121])).

fof(f121,plain,(
    sK1 = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f118,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f118,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f44,f112])).

fof(f112,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f92,f111])).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f110,f61])).

fof(f61,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f40,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f37,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f110,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f43,f101])).

fof(f101,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f97,f35])).

fof(f97,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0) ),
    inference(superposition,[],[f44,f61])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f92,plain,(
    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f90,f40])).

fof(f90,plain,(
    k3_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f43,f89])).

fof(f89,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(subsumption_resolution,[],[f33,f88])).

fof(f33,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f56,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:37:29 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.56  % (30516)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.56  % (30500)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.56  % (30508)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.57  % (30496)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.57  % (30520)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.53/0.57  % (30502)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.58  % (30512)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.53/0.58  % (30523)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.58  % (30497)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.53/0.58  % (30518)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.58  % (30510)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.58  % (30499)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.59  % (30501)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.53/0.59  % (30507)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.71/0.59  % (30501)Refutation found. Thanks to Tanya!
% 1.71/0.59  % SZS status Theorem for theBenchmark
% 1.71/0.59  % SZS output start Proof for theBenchmark
% 1.71/0.59  fof(f125,plain,(
% 1.71/0.59    $false),
% 1.71/0.59    inference(subsumption_resolution,[],[f123,f88])).
% 1.71/0.59  fof(f88,plain,(
% 1.71/0.59    r2_hidden(sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f34,f87])).
% 1.71/0.59  fof(f87,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.71/0.59    inference(resolution,[],[f46,f45])).
% 1.71/0.59  fof(f45,plain,(
% 1.71/0.59    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f26])).
% 1.71/0.59  fof(f26,plain,(
% 1.71/0.59    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.71/0.59    inference(ennf_transformation,[],[f18])).
% 1.71/0.59  fof(f18,axiom,(
% 1.71/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.71/0.59  fof(f46,plain,(
% 1.71/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.71/0.59    inference(cnf_transformation,[],[f27])).
% 1.71/0.59  fof(f27,plain,(
% 1.71/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.71/0.59    inference(ennf_transformation,[],[f23])).
% 1.71/0.59  fof(f23,plain,(
% 1.71/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.71/0.59    inference(unused_predicate_definition_removal,[],[f9])).
% 1.71/0.59  fof(f9,axiom,(
% 1.71/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.71/0.59  fof(f34,plain,(
% 1.71/0.59    r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.71/0.59    inference(cnf_transformation,[],[f30])).
% 1.71/0.59  fof(f30,plain,(
% 1.71/0.59    (r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.71/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 1.71/0.59  fof(f29,plain,(
% 1.71/0.59    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.71/0.59    introduced(choice_axiom,[])).
% 1.71/0.59  fof(f28,plain,(
% 1.71/0.59    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.71/0.59    inference(nnf_transformation,[],[f24])).
% 1.71/0.59  fof(f24,plain,(
% 1.71/0.59    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.71/0.59    inference(ennf_transformation,[],[f21])).
% 1.71/0.59  fof(f21,negated_conjecture,(
% 1.71/0.59    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.71/0.59    inference(negated_conjecture,[],[f20])).
% 1.71/0.59  fof(f20,conjecture,(
% 1.71/0.59    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.71/0.59  fof(f123,plain,(
% 1.71/0.59    ~r2_hidden(sK0,sK1)),
% 1.71/0.59    inference(superposition,[],[f56,f121])).
% 1.71/0.59  fof(f121,plain,(
% 1.71/0.59    sK1 = k4_xboole_0(sK1,k1_tarski(sK0))),
% 1.71/0.59    inference(forward_demodulation,[],[f118,f35])).
% 1.71/0.59  fof(f35,plain,(
% 1.71/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.71/0.59    inference(cnf_transformation,[],[f8])).
% 1.71/0.59  fof(f8,axiom,(
% 1.71/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.71/0.59  fof(f118,plain,(
% 1.71/0.59    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_xboole_0)),
% 1.71/0.59    inference(superposition,[],[f44,f112])).
% 1.71/0.59  fof(f112,plain,(
% 1.71/0.59    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.71/0.59    inference(backward_demodulation,[],[f92,f111])).
% 1.71/0.59  fof(f111,plain,(
% 1.71/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.71/0.59    inference(forward_demodulation,[],[f110,f61])).
% 1.71/0.59  fof(f61,plain,(
% 1.71/0.59    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.71/0.59    inference(superposition,[],[f40,f58])).
% 1.71/0.59  fof(f58,plain,(
% 1.71/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.71/0.59    inference(resolution,[],[f37,f39])).
% 1.71/0.59  fof(f39,plain,(
% 1.71/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f5])).
% 1.71/0.59  fof(f5,axiom,(
% 1.71/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.71/0.59  fof(f37,plain,(
% 1.71/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.71/0.59    inference(cnf_transformation,[],[f25])).
% 1.71/0.59  fof(f25,plain,(
% 1.71/0.59    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.71/0.59    inference(ennf_transformation,[],[f6])).
% 1.71/0.59  fof(f6,axiom,(
% 1.71/0.59    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.71/0.59  fof(f40,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f1])).
% 1.71/0.59  fof(f1,axiom,(
% 1.71/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.71/0.59  fof(f110,plain,(
% 1.71/0.59    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.71/0.59    inference(superposition,[],[f43,f101])).
% 1.71/0.59  fof(f101,plain,(
% 1.71/0.59    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 1.71/0.59    inference(forward_demodulation,[],[f97,f35])).
% 1.71/0.59  fof(f97,plain,(
% 1.71/0.59    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0)) )),
% 1.71/0.59    inference(superposition,[],[f44,f61])).
% 1.71/0.59  fof(f43,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f7])).
% 1.71/0.59  fof(f7,axiom,(
% 1.71/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.71/0.59  fof(f92,plain,(
% 1.71/0.59    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.71/0.59    inference(forward_demodulation,[],[f90,f40])).
% 1.71/0.59  fof(f90,plain,(
% 1.71/0.59    k3_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.71/0.59    inference(superposition,[],[f43,f89])).
% 1.71/0.59  fof(f89,plain,(
% 1.71/0.59    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f33,f88])).
% 1.71/0.59  fof(f33,plain,(
% 1.71/0.59    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.71/0.59    inference(cnf_transformation,[],[f30])).
% 1.71/0.59  fof(f44,plain,(
% 1.71/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f4])).
% 1.71/0.59  fof(f4,axiom,(
% 1.71/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.71/0.59  fof(f56,plain,(
% 1.71/0.59    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.71/0.59    inference(equality_resolution,[],[f50])).
% 1.71/0.59  fof(f50,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f32])).
% 1.71/0.59  fof(f32,plain,(
% 1.71/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.71/0.59    inference(flattening,[],[f31])).
% 1.71/0.59  fof(f31,plain,(
% 1.71/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.71/0.59    inference(nnf_transformation,[],[f19])).
% 1.71/0.59  fof(f19,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.71/0.59  % SZS output end Proof for theBenchmark
% 1.71/0.59  % (30501)------------------------------
% 1.71/0.59  % (30501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (30501)Termination reason: Refutation
% 1.71/0.59  
% 1.71/0.59  % (30501)Memory used [KB]: 6268
% 1.71/0.59  % (30501)Time elapsed: 0.160 s
% 1.71/0.59  % (30501)------------------------------
% 1.71/0.59  % (30501)------------------------------
% 1.71/0.59  % (30521)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.71/0.60  % (30509)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.71/0.60  % (30493)Success in time 0.223 s
%------------------------------------------------------------------------------
