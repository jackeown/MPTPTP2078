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
% DateTime   : Thu Dec  3 12:58:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  70 expanded)
%              Number of leaves         :    4 (  19 expanded)
%              Depth                    :   13
%              Number of atoms          :   63 ( 182 expanded)
%              Number of equality atoms :   62 ( 181 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f45,f52])).

fof(f52,plain,(
    sK1 = sK4 ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X5] :
      ( k4_tarski(sK0,sK1) != k4_tarski(X4,X5)
      | sK4 = X5 ) ),
    inference(superposition,[],[f13,f31])).

fof(f31,plain,(
    k4_tarski(sK0,sK1) = k4_tarski(sK3,sK4) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(k4_tarski(sK0,sK1),sK2)
      | k4_tarski(sK3,sK4) = X0 ) ),
    inference(superposition,[],[f12,f14])).

fof(f14,plain,(
    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f9,f11,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

% (3883)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f9,plain,(
    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
       => ( X2 = X5
          & X1 = X4
          & X0 = X3 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f45,plain,(
    sK1 != sK4 ),
    inference(trivial_inequality_removal,[],[f42])).

fof(f42,plain,
    ( sK0 != sK0
    | sK1 != sK4 ),
    inference(backward_demodulation,[],[f24,f39])).

fof(f39,plain,(
    sK0 = sK3 ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(sK0,sK1)
      | sK3 = X0 ) ),
    inference(superposition,[],[f12,f31])).

fof(f24,plain,
    ( sK1 != sK4
    | sK0 != sK3 ),
    inference(trivial_inequality_removal,[],[f23])).

fof(f23,plain,
    ( sK2 != sK2
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(superposition,[],[f10,f20])).

fof(f20,plain,(
    sK2 = sK5 ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X5] :
      ( k4_tarski(k4_tarski(sK0,sK1),sK2) != k4_tarski(X4,X5)
      | sK5 = X5 ) ),
    inference(superposition,[],[f13,f14])).

fof(f10,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:40:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (3863)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (3865)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (3859)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (3864)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (3882)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (3860)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (3874)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (3862)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (3866)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (3875)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (3860)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    sK1 != sK1),
% 0.21/0.53    inference(superposition,[],[f45,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    sK1 = sK4),
% 0.21/0.53    inference(equality_resolution,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k4_tarski(sK0,sK1) != k4_tarski(X4,X5) | sK4 = X5) )),
% 0.21/0.53    inference(superposition,[],[f13,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    k4_tarski(sK0,sK1) = k4_tarski(sK3,sK4)),
% 0.21/0.53    inference(equality_resolution,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_tarski(X0,X1) != k4_tarski(k4_tarski(sK0,sK1),sK2) | k4_tarski(sK3,sK4) = X0) )),
% 0.21/0.53    inference(superposition,[],[f12,f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK3,sK4),sK5)),
% 0.21/0.53    inference(definition_unfolding,[],[f9,f11,f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.53  % (3883)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    (sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f5,f7])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)) => ((sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f5,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3,X4,X5] : (k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) => (X2 = X5 & X1 = X4 & X0 = X3))),
% 0.21/0.53    inference(negated_conjecture,[],[f3])).
% 0.21/0.53  fof(f3,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : (k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) => (X2 = X5 & X1 = X4 & X0 = X3))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X0 = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k4_tarski(X0,X1) != k4_tarski(X2,X3))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k4_tarski(X0,X1) = k4_tarski(X2,X3) => (X1 = X3 & X0 = X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_zfmisc_1)).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X1 = X3) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    sK1 != sK4),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    sK0 != sK0 | sK1 != sK4),
% 0.21/0.53    inference(backward_demodulation,[],[f24,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    sK0 = sK3),
% 0.21/0.53    inference(equality_resolution,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_tarski(X0,X1) != k4_tarski(sK0,sK1) | sK3 = X0) )),
% 0.21/0.53    inference(superposition,[],[f12,f31])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    sK1 != sK4 | sK0 != sK3),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    sK2 != sK2 | sK1 != sK4 | sK0 != sK3),
% 0.21/0.53    inference(superposition,[],[f10,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    sK2 = sK5),
% 0.21/0.53    inference(equality_resolution,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k4_tarski(k4_tarski(sK0,sK1),sK2) != k4_tarski(X4,X5) | sK5 = X5) )),
% 0.21/0.53    inference(superposition,[],[f13,f14])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    sK2 != sK5 | sK1 != sK4 | sK0 != sK3),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (3860)------------------------------
% 0.21/0.53  % (3860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3860)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (3860)Memory used [KB]: 1663
% 0.21/0.53  % (3860)Time elapsed: 0.116 s
% 0.21/0.53  % (3860)------------------------------
% 0.21/0.53  % (3860)------------------------------
% 0.21/0.53  % (3858)Success in time 0.165 s
%------------------------------------------------------------------------------
