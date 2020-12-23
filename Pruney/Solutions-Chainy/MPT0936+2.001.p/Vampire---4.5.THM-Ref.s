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
% DateTime   : Thu Dec  3 12:59:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  27 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  52 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f513,plain,(
    $false ),
    inference(subsumption_resolution,[],[f512,f392])).

fof(f392,plain,(
    ! [X0,X1] : k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(subsumption_resolution,[],[f360,f243])).

fof(f243,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_relat_1)).

fof(f360,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f288])).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f119])).

fof(f119,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f59])).

fof(f59,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(f512,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(backward_demodulation,[],[f200,f509])).

fof(f509,plain,(
    ! [X2,X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))) ),
    inference(superposition,[],[f392,f283])).

fof(f283,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f200,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f141])).

fof(f141,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f82,f140])).

fof(f140,plain,
    ( ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
   => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f79])).

fof(f79,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f78])).

fof(f78,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (3519)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (3512)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (3516)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (3519)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f513,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f512,f392])).
% 0.20/0.51  fof(f392,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f360,f243])).
% 0.20/0.51  fof(f243,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f57])).
% 0.20/0.51  fof(f57,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_relat_1)).
% 0.20/0.51  fof(f360,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) | ~v1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 0.20/0.51    inference(equality_resolution,[],[f288])).
% 0.20/0.51  fof(f288,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_tarski(X0) = k1_relat_1(X2) | k1_tarski(k4_tarski(X0,X1)) != X2 | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f120])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2)) | k1_tarski(k4_tarski(X0,X1)) != X2 | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f119])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2)) | k1_tarski(k4_tarski(X0,X1)) != X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f59])).
% 0.20/0.51  fof(f59,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).
% 0.20/0.51  fof(f512,plain,(
% 0.20/0.51    k1_tarski(sK0) != k1_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 0.20/0.51    inference(backward_demodulation,[],[f200,f509])).
% 0.20/0.51  fof(f509,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_tarski(k4_tarski(X0,X1)) = k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) )),
% 0.20/0.51    inference(superposition,[],[f392,f283])).
% 0.20/0.51  fof(f283,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f63])).
% 0.20/0.51  fof(f63,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.20/0.51    inference(cnf_transformation,[],[f141])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f82,f140])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.20/0.51    inference(ennf_transformation,[],[f79])).
% 0.20/0.51  fof(f79,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.20/0.51    inference(negated_conjecture,[],[f78])).
% 0.20/0.51  fof(f78,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (3519)------------------------------
% 0.20/0.51  % (3519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3519)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (3519)Memory used [KB]: 2046
% 0.20/0.51  % (3519)Time elapsed: 0.116 s
% 0.20/0.51  % (3519)------------------------------
% 0.20/0.51  % (3519)------------------------------
% 0.20/0.51  % (3511)Success in time 0.156 s
%------------------------------------------------------------------------------
