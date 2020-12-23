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
% DateTime   : Thu Dec  3 12:59:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 279 expanded)
%              Number of leaves         :    8 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  107 ( 639 expanded)
%              Number of equality atoms :   43 ( 186 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f40])).

fof(f40,plain,(
    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(backward_demodulation,[],[f39,f38])).

fof(f38,plain,(
    k1_mcart_1(sK0) = sK5(sK0) ),
    inference(superposition,[],[f15,f34])).

fof(f34,plain,(
    sK0 = k4_tarski(sK5(sK0),sK6(sK0)) ),
    inference(resolution,[],[f21,f26])).

fof(f26,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(definition_unfolding,[],[f14,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f22,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f14,plain,(
    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f15,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f39,plain,(
    sK0 = k4_tarski(sK5(sK0),k2_mcart_1(sK0)) ),
    inference(backward_demodulation,[],[f34,f37])).

fof(f37,plain,(
    k2_mcart_1(sK0) = sK6(sK0) ),
    inference(superposition,[],[f16,f34])).

fof(f16,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(resolution,[],[f58,f31])).

fof(f31,plain,(
    r2_hidden(k2_mcart_1(sK0),sK4) ),
    inference(resolution,[],[f20,f26])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | sK0 != k4_tarski(k1_mcart_1(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f57,f32])).

fof(f32,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3) ),
    inference(resolution,[],[f20,f28])).

fof(f28,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(resolution,[],[f19,f26])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0] :
      ( sK0 != k4_tarski(k1_mcart_1(sK0),X0)
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(superposition,[],[f55,f44])).

fof(f44,plain,(
    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0))) ),
    inference(backward_demodulation,[],[f43,f42])).

fof(f42,plain,(
    k1_mcart_1(k1_mcart_1(sK0)) = sK5(k1_mcart_1(sK0)) ),
    inference(superposition,[],[f15,f35])).

fof(f35,plain,(
    k1_mcart_1(sK0) = k4_tarski(sK5(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0))) ),
    inference(resolution,[],[f21,f28])).

fof(f43,plain,(
    k1_mcart_1(sK0) = k4_tarski(sK5(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0))) ),
    inference(backward_demodulation,[],[f35,f41])).

fof(f41,plain,(
    k2_mcart_1(k1_mcart_1(sK0)) = sK6(k1_mcart_1(sK0)) ),
    inference(superposition,[],[f16,f35])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sK0 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),X0),X1)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK4) ) ),
    inference(subsumption_resolution,[],[f54,f30])).

fof(f30,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK1) ),
    inference(resolution,[],[f29,f19])).

fof(f29,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f28,f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK1)
      | sK0 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),X0),X1)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK4) ) ),
    inference(backward_demodulation,[],[f52,f49])).

fof(f49,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))) = sK5(k1_mcart_1(k1_mcart_1(sK0))) ),
    inference(superposition,[],[f15,f36])).

fof(f36,plain,(
    k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0)))) ),
    inference(resolution,[],[f21,f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sK0 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),X0),X1)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK1) ) ),
    inference(subsumption_resolution,[],[f50,f33])).

fof(f33,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK2) ),
    inference(resolution,[],[f20,f29])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK2)
      | sK0 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),X0),X1)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK1) ) ),
    inference(backward_demodulation,[],[f47,f48])).

fof(f48,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))) = sK6(k1_mcart_1(k1_mcart_1(sK0))) ),
    inference(superposition,[],[f16,f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sK0 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),X0),X1)
      | ~ r2_hidden(sK6(k1_mcart_1(k1_mcart_1(sK0))),sK2)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK1) ) ),
    inference(superposition,[],[f27,f36])).

fof(f27,plain,(
    ! [X6,X8,X7,X5] :
      ( sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(definition_unfolding,[],[f13,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f23,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f13,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X8,sK4)
      | k4_mcart_1(X5,X6,X7,X8) != sK0 ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 14:52:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (14642)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (14649)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (14641)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (14635)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (14635)Refutation not found, incomplete strategy% (14635)------------------------------
% 0.21/0.52  % (14635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14635)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14635)Memory used [KB]: 1663
% 0.21/0.52  % (14635)Time elapsed: 0.096 s
% 0.21/0.52  % (14635)------------------------------
% 0.21/0.52  % (14635)------------------------------
% 0.21/0.52  % (14641)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f59,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.21/0.52    inference(backward_demodulation,[],[f39,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    k1_mcart_1(sK0) = sK5(sK0)),
% 0.21/0.52    inference(superposition,[],[f15,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK5(sK0),sK6(sK0))),
% 0.21/0.52    inference(resolution,[],[f21,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 0.21/0.53    inference(definition_unfolding,[],[f14,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.21/0.53    inference(negated_conjecture,[],[f8])).
% 0.21/0.53  fof(f8,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK5(X0),sK6(X0)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    sK0 = k4_tarski(sK5(sK0),k2_mcart_1(sK0))),
% 0.21/0.53    inference(backward_demodulation,[],[f34,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    k2_mcart_1(sK0) = sK6(sK0)),
% 0.21/0.53    inference(superposition,[],[f16,f34])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.21/0.53    inference(resolution,[],[f58,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    r2_hidden(k2_mcart_1(sK0),sK4)),
% 0.21/0.53    inference(resolution,[],[f20,f26])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK4) | sK0 != k4_tarski(k1_mcart_1(sK0),X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f57,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3)),
% 0.21/0.53    inference(resolution,[],[f20,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.21/0.53    inference(resolution,[],[f19,f26])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0] : (sK0 != k4_tarski(k1_mcart_1(sK0),X0) | ~r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK3) | ~r2_hidden(X0,sK4)) )),
% 0.21/0.53    inference(superposition,[],[f55,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)))),
% 0.21/0.53    inference(backward_demodulation,[],[f43,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    k1_mcart_1(k1_mcart_1(sK0)) = sK5(k1_mcart_1(sK0))),
% 0.21/0.53    inference(superposition,[],[f15,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    k1_mcart_1(sK0) = k4_tarski(sK5(k1_mcart_1(sK0)),sK6(k1_mcart_1(sK0)))),
% 0.21/0.53    inference(resolution,[],[f21,f28])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    k1_mcart_1(sK0) = k4_tarski(sK5(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)))),
% 0.21/0.53    inference(backward_demodulation,[],[f35,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    k2_mcart_1(k1_mcart_1(sK0)) = sK6(k1_mcart_1(sK0))),
% 0.21/0.53    inference(superposition,[],[f16,f35])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK0 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),X0),X1) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK4)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f54,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK1)),
% 0.21/0.53    inference(resolution,[],[f29,f19])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),k2_zfmisc_1(sK1,sK2))),
% 0.21/0.53    inference(resolution,[],[f28,f19])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK1) | sK0 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),X0),X1) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK4)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f52,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    k1_mcart_1(k1_mcart_1(k1_mcart_1(sK0))) = sK5(k1_mcart_1(k1_mcart_1(sK0)))),
% 0.21/0.53    inference(superposition,[],[f15,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    k1_mcart_1(k1_mcart_1(sK0)) = k4_tarski(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK6(k1_mcart_1(k1_mcart_1(sK0))))),
% 0.21/0.53    inference(resolution,[],[f21,f29])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK0 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),X0),X1) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK4) | ~r2_hidden(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f50,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK2)),
% 0.21/0.53    inference(resolution,[],[f20,f29])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))),sK2) | sK0 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),X0),X1) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK4) | ~r2_hidden(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK1)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f47,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    k2_mcart_1(k1_mcart_1(k1_mcart_1(sK0))) = sK6(k1_mcart_1(k1_mcart_1(sK0)))),
% 0.21/0.53    inference(superposition,[],[f16,f36])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK0 != k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),X0),X1) | ~r2_hidden(sK6(k1_mcart_1(k1_mcart_1(sK0))),sK2) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK4) | ~r2_hidden(sK5(k1_mcart_1(k1_mcart_1(sK0))),sK1)) )),
% 0.21/0.53    inference(superposition,[],[f27,f36])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X6,X8,X7,X5] : (sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) | ~r2_hidden(X6,sK2) | ~r2_hidden(X7,sK3) | ~r2_hidden(X8,sK4) | ~r2_hidden(X5,sK1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f13,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f23,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ( ! [X6,X8,X7,X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(X6,sK2) | ~r2_hidden(X7,sK3) | ~r2_hidden(X8,sK4) | k4_mcart_1(X5,X6,X7,X8) != sK0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14641)------------------------------
% 0.21/0.53  % (14641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14641)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14641)Memory used [KB]: 6268
% 0.21/0.53  % (14641)Time elapsed: 0.011 s
% 0.21/0.53  % (14641)------------------------------
% 0.21/0.53  % (14641)------------------------------
% 0.21/0.53  % (14648)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (14634)Success in time 0.176 s
%------------------------------------------------------------------------------
