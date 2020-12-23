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
% DateTime   : Thu Dec  3 12:58:41 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 301 expanded)
%              Number of leaves         :   12 (  89 expanded)
%              Depth                    :   17
%              Number of atoms          :  126 ( 661 expanded)
%              Number of equality atoms :   92 ( 476 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f99,f107])).

fof(f107,plain,(
    ! [X2,X3] : k4_tarski(X2,X3) != X3 ),
    inference(forward_demodulation,[],[f106,f84])).

fof(f84,plain,(
    ! [X0] : sK3(k1_tarski(X0)) = X0 ),
    inference(subsumption_resolution,[],[f83,f73])).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f50,f71])).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f70,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f70,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f68,f67])).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f40,f34])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

% (10856)Refutation not found, incomplete strategy% (10856)------------------------------
% (10856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10856)Termination reason: Refutation not found, incomplete strategy

% (10856)Memory used [KB]: 10618
% (10856)Time elapsed: 0.090 s
% (10856)------------------------------
% (10856)------------------------------
fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f68,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f40,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f50,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f83,plain,(
    ! [X0] :
      ( sK3(k1_tarski(X0)) = X0
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f81,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

% (10854)Refutation not found, incomplete strategy% (10854)------------------------------
% (10854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10854)Termination reason: Refutation not found, incomplete strategy

% (10854)Memory used [KB]: 10746
% (10854)Time elapsed: 0.092 s
% (10854)------------------------------
% (10854)------------------------------
fof(f81,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_tarski(X3))
      | X3 = X4 ) ),
    inference(superposition,[],[f51,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f106,plain,(
    ! [X2,X3] : k4_tarski(X2,X3) != sK3(k1_tarski(X3)) ),
    inference(subsumption_resolution,[],[f104,f73])).

fof(f104,plain,(
    ! [X2,X3] :
      ( k4_tarski(X2,X3) != sK3(k1_tarski(X3))
      | k1_xboole_0 = k1_tarski(X3) ) ),
    inference(resolution,[],[f33,f86])).

fof(f86,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(subsumption_resolution,[],[f85,f73])).

fof(f85,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f31,f84])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | k4_tarski(X2,X3) != sK3(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    sK0 = k4_tarski(sK1,sK0) ),
    inference(backward_demodulation,[],[f28,f98])).

fof(f98,plain,(
    sK0 = sK2 ),
    inference(backward_demodulation,[],[f54,f97])).

fof(f97,plain,(
    sK0 = k2_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f53,f93])).

fof(f93,plain,(
    sK0 != sK1 ),
    inference(superposition,[],[f92,f28])).

fof(f92,plain,(
    ! [X2,X3] : k4_tarski(X2,X3) != X2 ),
    inference(forward_demodulation,[],[f91,f84])).

fof(f91,plain,(
    ! [X2,X3] : k4_tarski(X2,X3) != sK3(k1_tarski(X2)) ),
    inference(subsumption_resolution,[],[f89,f73])).

fof(f89,plain,(
    ! [X2,X3] :
      ( k4_tarski(X2,X3) != sK3(k1_tarski(X2))
      | k1_xboole_0 = k1_tarski(X2) ) ),
    inference(resolution,[],[f32,f86])).

fof(f32,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k4_tarski(X2,X3) != sK3(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f29,f52])).

fof(f52,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f41,f28])).

fof(f41,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f29,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f54,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f42,f28])).

fof(f42,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.08  % Command    : run_vampire %s %d
% 0.09/0.27  % Computer   : n010.cluster.edu
% 0.09/0.27  % Model      : x86_64 x86_64
% 0.09/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.27  % Memory     : 8042.1875MB
% 0.09/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.27  % CPULimit   : 60
% 0.09/0.27  % WCLimit    : 600
% 0.09/0.27  % DateTime   : Tue Dec  1 10:06:29 EST 2020
% 0.09/0.27  % CPUTime    : 
% 0.13/0.35  % (10846)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.13/0.37  % (10846)Refutation not found, incomplete strategy% (10846)------------------------------
% 0.13/0.37  % (10846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.37  % (10846)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.37  
% 0.13/0.37  % (10846)Memory used [KB]: 1663
% 0.13/0.37  % (10846)Time elapsed: 0.057 s
% 0.13/0.37  % (10846)------------------------------
% 0.13/0.37  % (10846)------------------------------
% 0.13/0.39  % (10861)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.13/0.39  % (10861)Refutation not found, incomplete strategy% (10861)------------------------------
% 0.13/0.39  % (10861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.39  % (10861)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.39  
% 0.13/0.39  % (10861)Memory used [KB]: 6140
% 0.13/0.39  % (10861)Time elapsed: 0.009 s
% 0.13/0.39  % (10861)------------------------------
% 0.13/0.39  % (10861)------------------------------
% 0.13/0.40  % (10868)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.13/0.40  % (10853)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.13/0.40  % (10868)Refutation not found, incomplete strategy% (10868)------------------------------
% 0.13/0.40  % (10868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.40  % (10868)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.40  
% 0.13/0.40  % (10868)Memory used [KB]: 10746
% 0.13/0.40  % (10868)Time elapsed: 0.061 s
% 0.13/0.40  % (10868)------------------------------
% 0.13/0.40  % (10868)------------------------------
% 0.13/0.40  % (10857)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.13/0.40  % (10857)Refutation not found, incomplete strategy% (10857)------------------------------
% 0.13/0.40  % (10857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.40  % (10857)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.40  
% 0.13/0.40  % (10857)Memory used [KB]: 10618
% 0.13/0.40  % (10857)Time elapsed: 0.081 s
% 0.13/0.40  % (10857)------------------------------
% 0.13/0.40  % (10857)------------------------------
% 0.13/0.41  % (10853)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % (10856)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.13/0.41  % (10854)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f108,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(subsumption_resolution,[],[f99,f107])).
% 0.13/0.41  fof(f107,plain,(
% 0.13/0.41    ( ! [X2,X3] : (k4_tarski(X2,X3) != X3) )),
% 0.13/0.41    inference(forward_demodulation,[],[f106,f84])).
% 0.13/0.41  fof(f84,plain,(
% 0.13/0.41    ( ! [X0] : (sK3(k1_tarski(X0)) = X0) )),
% 0.13/0.41    inference(subsumption_resolution,[],[f83,f73])).
% 0.13/0.41  fof(f73,plain,(
% 0.13/0.41    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.13/0.41    inference(backward_demodulation,[],[f50,f71])).
% 0.13/0.41  fof(f71,plain,(
% 0.13/0.41    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.13/0.41    inference(forward_demodulation,[],[f70,f36])).
% 0.13/0.41  fof(f36,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f4])).
% 0.13/0.41  fof(f4,axiom,(
% 0.13/0.41    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.13/0.41  fof(f70,plain,(
% 0.13/0.41    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,X1)) )),
% 0.13/0.41    inference(forward_demodulation,[],[f68,f67])).
% 0.13/0.41  fof(f67,plain,(
% 0.13/0.41    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 0.13/0.41    inference(superposition,[],[f40,f34])).
% 0.13/0.41  fof(f34,plain,(
% 0.13/0.41    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f17])).
% 0.13/0.41  fof(f17,plain,(
% 0.13/0.41    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.13/0.41    inference(rectify,[],[f1])).
% 0.13/0.41  fof(f1,axiom,(
% 0.13/0.41    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.13/0.41  % (10856)Refutation not found, incomplete strategy% (10856)------------------------------
% 0.13/0.41  % (10856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (10856)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.41  
% 0.13/0.41  % (10856)Memory used [KB]: 10618
% 0.13/0.41  % (10856)Time elapsed: 0.090 s
% 0.13/0.41  % (10856)------------------------------
% 0.13/0.41  % (10856)------------------------------
% 0.13/0.41  fof(f40,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f2])).
% 0.13/0.41  fof(f2,axiom,(
% 0.13/0.41    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.13/0.41  fof(f68,plain,(
% 0.13/0.41    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(X1,X1)) )),
% 0.13/0.41    inference(superposition,[],[f40,f35])).
% 0.13/0.41  fof(f35,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f3])).
% 0.13/0.41  fof(f3,axiom,(
% 0.13/0.41    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.13/0.41  fof(f50,plain,(
% 0.13/0.41    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.13/0.41    inference(equality_resolution,[],[f43])).
% 0.13/0.41  fof(f43,plain,(
% 0.13/0.41    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f25])).
% 0.13/0.41  fof(f25,plain,(
% 0.13/0.41    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.13/0.41    inference(nnf_transformation,[],[f10])).
% 0.13/0.41  fof(f10,axiom,(
% 0.13/0.41    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.13/0.41  fof(f83,plain,(
% 0.13/0.41    ( ! [X0] : (sK3(k1_tarski(X0)) = X0 | k1_xboole_0 = k1_tarski(X0)) )),
% 0.13/0.41    inference(resolution,[],[f81,f31])).
% 0.13/0.41  fof(f31,plain,(
% 0.13/0.41    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f24])).
% 0.13/0.41  fof(f24,plain,(
% 0.13/0.41    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f23])).
% 0.13/0.41  fof(f23,plain,(
% 0.13/0.41    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f19,plain,(
% 0.13/0.41    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.13/0.41    inference(ennf_transformation,[],[f14])).
% 0.13/0.41  fof(f14,axiom,(
% 0.13/0.41    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.13/0.41  % (10854)Refutation not found, incomplete strategy% (10854)------------------------------
% 0.13/0.41  % (10854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (10854)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.41  
% 0.13/0.41  % (10854)Memory used [KB]: 10746
% 0.13/0.41  % (10854)Time elapsed: 0.092 s
% 0.13/0.41  % (10854)------------------------------
% 0.13/0.41  % (10854)------------------------------
% 0.13/0.41  fof(f81,plain,(
% 0.13/0.41    ( ! [X4,X3] : (~r2_hidden(X4,k1_tarski(X3)) | X3 = X4) )),
% 0.13/0.41    inference(superposition,[],[f51,f44])).
% 0.13/0.41  fof(f44,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.13/0.41    inference(cnf_transformation,[],[f25])).
% 0.13/0.41  fof(f51,plain,(
% 0.13/0.41    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.13/0.41    inference(equality_resolution,[],[f47])).
% 0.13/0.41  fof(f47,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f27])).
% 0.13/0.41  fof(f27,plain,(
% 0.13/0.41    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.13/0.41    inference(flattening,[],[f26])).
% 0.13/0.41  fof(f26,plain,(
% 0.13/0.41    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.13/0.41    inference(nnf_transformation,[],[f11])).
% 0.13/0.41  fof(f11,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.13/0.41  fof(f106,plain,(
% 0.13/0.41    ( ! [X2,X3] : (k4_tarski(X2,X3) != sK3(k1_tarski(X3))) )),
% 0.13/0.41    inference(subsumption_resolution,[],[f104,f73])).
% 0.13/0.41  fof(f104,plain,(
% 0.13/0.41    ( ! [X2,X3] : (k4_tarski(X2,X3) != sK3(k1_tarski(X3)) | k1_xboole_0 = k1_tarski(X3)) )),
% 0.13/0.41    inference(resolution,[],[f33,f86])).
% 0.13/0.41  fof(f86,plain,(
% 0.13/0.41    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.13/0.41    inference(subsumption_resolution,[],[f85,f73])).
% 0.13/0.41  fof(f85,plain,(
% 0.13/0.41    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.13/0.41    inference(superposition,[],[f31,f84])).
% 0.13/0.41  fof(f33,plain,(
% 0.13/0.41    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | k4_tarski(X2,X3) != sK3(X0) | k1_xboole_0 = X0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f24])).
% 0.13/0.41  fof(f99,plain,(
% 0.13/0.41    sK0 = k4_tarski(sK1,sK0)),
% 0.13/0.41    inference(backward_demodulation,[],[f28,f98])).
% 0.13/0.41  fof(f98,plain,(
% 0.13/0.41    sK0 = sK2),
% 0.13/0.41    inference(backward_demodulation,[],[f54,f97])).
% 0.13/0.41  fof(f97,plain,(
% 0.13/0.41    sK0 = k2_mcart_1(sK0)),
% 0.13/0.41    inference(subsumption_resolution,[],[f53,f93])).
% 0.13/0.41  fof(f93,plain,(
% 0.13/0.41    sK0 != sK1),
% 0.13/0.41    inference(superposition,[],[f92,f28])).
% 0.13/0.41  fof(f92,plain,(
% 0.13/0.41    ( ! [X2,X3] : (k4_tarski(X2,X3) != X2) )),
% 0.13/0.41    inference(forward_demodulation,[],[f91,f84])).
% 0.13/0.41  fof(f91,plain,(
% 0.13/0.41    ( ! [X2,X3] : (k4_tarski(X2,X3) != sK3(k1_tarski(X2))) )),
% 0.13/0.41    inference(subsumption_resolution,[],[f89,f73])).
% 0.13/0.41  fof(f89,plain,(
% 0.13/0.41    ( ! [X2,X3] : (k4_tarski(X2,X3) != sK3(k1_tarski(X2)) | k1_xboole_0 = k1_tarski(X2)) )),
% 0.13/0.41    inference(resolution,[],[f32,f86])).
% 0.13/0.41  fof(f32,plain,(
% 0.13/0.41    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k4_tarski(X2,X3) != sK3(X0) | k1_xboole_0 = X0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f24])).
% 0.13/0.41  fof(f53,plain,(
% 0.13/0.41    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 0.13/0.41    inference(backward_demodulation,[],[f29,f52])).
% 0.13/0.41  fof(f52,plain,(
% 0.13/0.41    k1_mcart_1(sK0) = sK1),
% 0.13/0.41    inference(superposition,[],[f41,f28])).
% 0.13/0.41  fof(f41,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f13])).
% 0.13/0.41  fof(f13,axiom,(
% 0.13/0.41    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.13/0.41  fof(f29,plain,(
% 0.13/0.41    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.13/0.41    inference(cnf_transformation,[],[f22])).
% 0.13/0.41  fof(f22,plain,(
% 0.13/0.41    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20])).
% 0.13/0.41  fof(f20,plain,(
% 0.13/0.41    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f21,plain,(
% 0.13/0.41    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f18,plain,(
% 0.13/0.41    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.13/0.41    inference(ennf_transformation,[],[f16])).
% 0.13/0.41  fof(f16,negated_conjecture,(
% 0.13/0.41    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.13/0.41    inference(negated_conjecture,[],[f15])).
% 0.13/0.41  fof(f15,conjecture,(
% 0.13/0.41    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.13/0.41  fof(f54,plain,(
% 0.13/0.41    k2_mcart_1(sK0) = sK2),
% 0.13/0.41    inference(superposition,[],[f42,f28])).
% 0.13/0.41  fof(f42,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.13/0.41    inference(cnf_transformation,[],[f13])).
% 0.13/0.41  fof(f28,plain,(
% 0.13/0.41    sK0 = k4_tarski(sK1,sK2)),
% 0.13/0.41    inference(cnf_transformation,[],[f22])).
% 0.13/0.41  % SZS output end Proof for theBenchmark
% 0.13/0.41  % (10853)------------------------------
% 0.13/0.41  % (10853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (10853)Termination reason: Refutation
% 0.13/0.41  
% 0.13/0.41  % (10853)Memory used [KB]: 6268
% 0.13/0.41  % (10853)Time elapsed: 0.076 s
% 0.13/0.41  % (10853)------------------------------
% 0.13/0.41  % (10853)------------------------------
% 0.13/0.41  % (10855)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.13/0.41  % (10845)Success in time 0.126 s
%------------------------------------------------------------------------------
