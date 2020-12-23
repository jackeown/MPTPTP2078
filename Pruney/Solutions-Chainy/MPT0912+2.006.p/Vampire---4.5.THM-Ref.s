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
% DateTime   : Thu Dec  3 12:59:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 217 expanded)
%              Number of leaves         :    8 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          :  127 ( 649 expanded)
%              Number of equality atoms :   30 ( 178 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f25,f26,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3)) ) ),
    inference(forward_demodulation,[],[f53,f35])).

fof(f35,plain,(
    k1_mcart_1(sK0) = sK4(sK0) ),
    inference(resolution,[],[f29,f25])).

fof(f29,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X4,X5))
      | sK4(X3) = k1_mcart_1(X3) ) ),
    inference(superposition,[],[f17,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK4(X0),sK5(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK4(X0),sK5(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK4(X0),sK5(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f17,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f52,f32])).

fof(f32,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1) ),
    inference(resolution,[],[f26,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1)
      | ~ r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3)) ) ),
    inference(forward_demodulation,[],[f51,f36])).

fof(f36,plain,(
    sK4(k1_mcart_1(sK0)) = k1_mcart_1(k1_mcart_1(sK0)) ),
    inference(resolution,[],[f29,f26])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(k1_mcart_1(sK0)),sK1)
      | ~ r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3)) ) ),
    inference(forward_demodulation,[],[f50,f35])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(sK4(sK0)),sK1)
      | ~ r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f49,f31])).

fof(f31,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2)
      | ~ r2_hidden(sK4(sK4(sK0)),sK1)
      | ~ r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3)) ) ),
    inference(forward_demodulation,[],[f48,f34])).

fof(f34,plain,(
    sK5(k1_mcart_1(sK0)) = k2_mcart_1(k1_mcart_1(sK0)) ),
    inference(resolution,[],[f28,f26])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k2_mcart_1(X0) = sK5(X0) ) ),
    inference(superposition,[],[f18,f23])).

fof(f18,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(k1_mcart_1(sK0)),sK2)
      | ~ r2_hidden(sK4(sK4(sK0)),sK1)
      | ~ r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3)) ) ),
    inference(forward_demodulation,[],[f47,f35])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(sK4(sK0)),sK2)
      | ~ r2_hidden(sK4(sK4(sK0)),sK1)
      | ~ r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f46,f27])).

fof(f27,plain,(
    r2_hidden(k2_mcart_1(sK0),sK3) ),
    inference(resolution,[],[f22,f25])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
      | ~ r2_hidden(sK5(sK4(sK0)),sK2)
      | ~ r2_hidden(sK4(sK4(sK0)),sK1)
      | ~ r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3)) ) ),
    inference(forward_demodulation,[],[f45,f33])).

fof(f33,plain,(
    k2_mcart_1(sK0) = sK5(sK0) ),
    inference(resolution,[],[f28,f25])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(sK0),sK3)
      | ~ r2_hidden(sK5(sK4(sK0)),sK2)
      | ~ r2_hidden(sK4(sK4(sK0)),sK1)
      | ~ r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK0 != X0
      | ~ r2_hidden(sK5(X0),sK3)
      | ~ r2_hidden(sK5(sK4(X0)),sK2)
      | ~ r2_hidden(sK4(sK4(X0)),sK1)
      | ~ r2_hidden(sK4(X0),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X4)) ) ),
    inference(superposition,[],[f30,f23])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != sK0
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(sK5(X0),sK2)
      | ~ r2_hidden(sK4(X0),sK1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(superposition,[],[f24,f23])).

fof(f24,plain,(
    ! [X6,X4,X5] :
      ( sK0 != k4_tarski(k4_tarski(X4,X5),X6)
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(definition_unfolding,[],[f16,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f16,plain,(
    ! [X6,X4,X5] :
      ( k3_mcart_1(X4,X5,X6) != sK0
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ! [X4,X5,X6] :
        ( k3_mcart_1(X4,X5,X6) != sK0
        | ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1) )
    & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5,X6] :
            ( k3_mcart_1(X4,X5,X6) != X0
            | ~ r2_hidden(X6,X3)
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) )
   => ( ! [X6,X5,X4] :
          ( k3_mcart_1(X4,X5,X6) != sK0
          | ~ r2_hidden(X6,sK3)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1) )
      & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) != X0
          | ~ r2_hidden(X6,X3)
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5,X6] :
              ~ ( k3_mcart_1(X4,X5,X6) = X0
                & r2_hidden(X6,X3)
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

fof(f26,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f21,f25])).

fof(f25,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f15,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f15,plain,(
    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:21:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.48  % (10652)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (10648)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (10642)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (10648)Refutation not found, incomplete strategy% (10648)------------------------------
% 0.20/0.52  % (10648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10648)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10648)Memory used [KB]: 10618
% 0.20/0.52  % (10648)Time elapsed: 0.117 s
% 0.20/0.52  % (10648)------------------------------
% 0.20/0.52  % (10648)------------------------------
% 0.20/0.52  % (10639)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (10668)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (10660)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (10668)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f25,f26,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f53,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    k1_mcart_1(sK0) = sK4(sK0)),
% 0.20/0.52    inference(resolution,[],[f29,f25])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (~r2_hidden(X3,k2_zfmisc_1(X4,X5)) | sK4(X3) = k1_mcart_1(X3)) )),
% 0.20/0.52    inference(superposition,[],[f17,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k4_tarski(sK4(X0),sK5(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k4_tarski(sK4(X0),sK5(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK4(X0),sK5(X0)) = X0)),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f52,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1)),
% 0.20/0.52    inference(resolution,[],[f26,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1) | ~r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f51,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    sK4(k1_mcart_1(sK0)) = k1_mcart_1(k1_mcart_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f29,f26])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4(k1_mcart_1(sK0)),sK1) | ~r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f50,f35])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4(sK4(sK0)),sK1) | ~r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f49,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2)),
% 0.20/0.52    inference(resolution,[],[f26,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2) | ~r2_hidden(sK4(sK4(sK0)),sK1) | ~r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f48,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    sK5(k1_mcart_1(sK0)) = k2_mcart_1(k1_mcart_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f28,f26])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k2_mcart_1(X0) = sK5(X0)) )),
% 0.20/0.52    inference(superposition,[],[f18,f23])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(k1_mcart_1(sK0)),sK2) | ~r2_hidden(sK4(sK4(sK0)),sK1) | ~r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f47,f35])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(sK4(sK0)),sK2) | ~r2_hidden(sK4(sK4(sK0)),sK1) | ~r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f46,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(sK0),sK3)),
% 0.20/0.52    inference(resolution,[],[f22,f25])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(sK0),sK3) | ~r2_hidden(sK5(sK4(sK0)),sK2) | ~r2_hidden(sK4(sK4(sK0)),sK1) | ~r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f45,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    k2_mcart_1(sK0) = sK5(sK0)),
% 0.20/0.52    inference(resolution,[],[f28,f25])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(sK0),sK3) | ~r2_hidden(sK5(sK4(sK0)),sK2) | ~r2_hidden(sK4(sK4(sK0)),sK1) | ~r2_hidden(sK4(sK0),k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.52    inference(equality_resolution,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (sK0 != X0 | ~r2_hidden(sK5(X0),sK3) | ~r2_hidden(sK5(sK4(X0)),sK2) | ~r2_hidden(sK4(sK4(X0)),sK1) | ~r2_hidden(sK4(X0),k2_zfmisc_1(X1,X2)) | ~r2_hidden(X0,k2_zfmisc_1(X3,X4))) )),
% 0.20/0.52    inference(superposition,[],[f30,f23])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != sK0 | ~r2_hidden(X1,sK3) | ~r2_hidden(sK5(X0),sK2) | ~r2_hidden(sK4(X0),sK1) | ~r2_hidden(X0,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.52    inference(superposition,[],[f24,f23])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (sK0 != k4_tarski(k4_tarski(X4,X5),X6) | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f16,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))) => (! [X6,X5,X4] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.20/0.52    inference(negated_conjecture,[],[f6])).
% 0.20/0.52  fof(f6,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(sK1,sK2))),
% 0.20/0.52    inference(resolution,[],[f21,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.20/0.52    inference(definition_unfolding,[],[f15,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (10668)------------------------------
% 0.20/0.52  % (10668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10668)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (10668)Memory used [KB]: 1663
% 0.20/0.52  % (10668)Time elapsed: 0.092 s
% 0.20/0.52  % (10668)------------------------------
% 0.20/0.52  % (10668)------------------------------
% 0.20/0.52  % (10638)Success in time 0.177 s
%------------------------------------------------------------------------------
