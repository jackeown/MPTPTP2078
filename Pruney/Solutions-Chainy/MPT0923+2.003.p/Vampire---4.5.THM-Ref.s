%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 145 expanded)
%              Number of leaves         :    6 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   74 ( 378 expanded)
%              Number of equality atoms :   29 ( 124 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f109,f34])).

fof(f34,plain,(
    sK0 = k4_tarski(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)) ),
    inference(unit_resulting_resolution,[],[f25,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f25,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(definition_unfolding,[],[f10,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f10,plain,(
    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

fof(f109,plain,(
    sK0 != k4_tarski(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)) ),
    inference(forward_demodulation,[],[f108,f44])).

fof(f44,plain,(
    sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0) = k4_tarski(sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK7(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))) ),
    inference(unit_resulting_resolution,[],[f32,f29])).

fof(f32,plain,(
    r2_hidden(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(unit_resulting_resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f108,plain,(
    sK0 != k4_tarski(k4_tarski(sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK7(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)) ),
    inference(forward_demodulation,[],[f92,f63])).

fof(f63,plain,(
    sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)) = k4_tarski(sK6(sK1,sK2,sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),sK7(sK1,sK2,sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)))) ),
    inference(unit_resulting_resolution,[],[f42,f29])).

fof(f42,plain,(
    r2_hidden(sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f32,f31])).

fof(f92,plain,(
    sK0 != k4_tarski(k4_tarski(k4_tarski(sK6(sK1,sK2,sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),sK7(sK1,sK2,sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)))),sK7(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)) ),
    inference(unit_resulting_resolution,[],[f61,f33,f43,f62,f26])).

fof(f26,plain,(
    ! [X6,X8,X7,X5] :
      ( sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(definition_unfolding,[],[f9,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f11,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f9,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X8,sK4)
      | k4_mcart_1(X5,X6,X7,X8) != sK0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f62,plain,(
    r2_hidden(sK7(sK1,sK2,sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),sK2) ),
    inference(unit_resulting_resolution,[],[f42,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f43,plain,(
    r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK3) ),
    inference(unit_resulting_resolution,[],[f32,f30])).

fof(f33,plain,(
    r2_hidden(sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK4) ),
    inference(unit_resulting_resolution,[],[f25,f30])).

fof(f61,plain,(
    r2_hidden(sK6(sK1,sK2,sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f42,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:37 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.52  % (17486)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (17477)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (17494)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (17494)Refutation not found, incomplete strategy% (17494)------------------------------
% 0.21/0.53  % (17494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17477)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (17488)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (17494)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17494)Memory used [KB]: 1791
% 0.21/0.54  % (17494)Time elapsed: 0.096 s
% 0.21/0.54  % (17494)------------------------------
% 0.21/0.54  % (17494)------------------------------
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f133])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    sK0 != sK0),
% 0.21/0.55    inference(superposition,[],[f109,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    sK0 = k4_tarski(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f25,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3) )),
% 0.21/0.55    inference(equality_resolution,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 0.21/0.55    inference(definition_unfolding,[],[f10,f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f20,f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.21/0.55    inference(negated_conjecture,[],[f6])).
% 0.21/0.55  fof(f6,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    sK0 != k4_tarski(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f108,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0) = k4_tarski(sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK7(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f32,f29])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    r2_hidden(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f25,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    sK0 != k4_tarski(k4_tarski(sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK7(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f92,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)) = k4_tarski(sK6(sK1,sK2,sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),sK7(sK1,sK2,sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f42,f29])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    r2_hidden(sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),k2_zfmisc_1(sK1,sK2))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f32,f31])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    sK0 != k4_tarski(k4_tarski(k4_tarski(sK6(sK1,sK2,sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),sK7(sK1,sK2,sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)))),sK7(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f61,f33,f43,f62,f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X6,X8,X7,X5] : (sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) | ~r2_hidden(X6,sK2) | ~r2_hidden(X7,sK3) | ~r2_hidden(X8,sK4) | ~r2_hidden(X5,sK1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f9,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f11,f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ( ! [X6,X8,X7,X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(X6,sK2) | ~r2_hidden(X7,sK3) | ~r2_hidden(X8,sK4) | k4_mcart_1(X5,X6,X7,X8) != sK0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    r2_hidden(sK7(sK1,sK2,sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),sK2)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f42,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    r2_hidden(sK7(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)),sK3)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f32,f30])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    r2_hidden(sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK4)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f25,f30])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    r2_hidden(sK6(sK1,sK2,sK6(k2_zfmisc_1(sK1,sK2),sK3,sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),sK1)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f42,f31])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (17477)------------------------------
% 0.21/0.55  % (17477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17477)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (17477)Memory used [KB]: 6396
% 0.21/0.55  % (17477)Time elapsed: 0.100 s
% 0.21/0.55  % (17477)------------------------------
% 0.21/0.55  % (17477)------------------------------
% 0.21/0.55  % (17465)Success in time 0.189 s
%------------------------------------------------------------------------------
