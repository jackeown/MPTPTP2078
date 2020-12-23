%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  72 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 240 expanded)
%              Number of equality atoms :   34 (  97 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(subsumption_resolution,[],[f81,f37])).

fof(f37,plain,(
    sK2 != k2_mcart_1(sK0) ),
    inference(resolution,[],[f28,f16])).

fof(f16,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | sK2 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ( sK3 != k2_mcart_1(sK0)
        & sK2 != k2_mcart_1(sK0) )
      | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) )
   => ( ( ( sK3 != k2_mcart_1(sK0)
          & sK2 != k2_mcart_1(sK0) )
        | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

% (6006)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f28,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(resolution,[],[f15,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f15,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f12])).

fof(f81,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f75,f44])).

fof(f44,plain,(
    sK3 != k2_mcart_1(sK0) ),
    inference(resolution,[],[f17,f28])).

fof(f17,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,
    ( sK3 = k2_mcart_1(sK0)
    | sK2 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f73,f29])).

fof(f29,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f15,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X8,k2_tarski(X9,X10))
      | X8 = X10
      | X8 = X9 ) ),
    inference(forward_demodulation,[],[f72,f19])).

fof(f19,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f72,plain,(
    ! [X10,X8,X9] :
      ( X8 = X10
      | ~ r2_hidden(X8,k2_tarski(X9,X10))
      | k1_mcart_1(k4_tarski(X8,k1_mcart_1(sK0))) = X9 ) ),
    inference(forward_demodulation,[],[f64,f19])).

fof(f64,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X8,k2_tarski(X9,X10))
      | k1_mcart_1(k4_tarski(X8,k1_mcart_1(sK0))) = X10
      | k1_mcart_1(k4_tarski(X8,k1_mcart_1(sK0))) = X9 ) ),
    inference(resolution,[],[f39,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(X0) = X2
      | k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) )
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f39,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,k1_mcart_1(sK0)),k2_zfmisc_1(X3,sK1))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:03:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (5982)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (5995)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (6004)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (5989)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (5989)Refutation not found, incomplete strategy% (5989)------------------------------
% 0.21/0.53  % (5989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5989)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5989)Memory used [KB]: 10618
% 0.21/0.53  % (5989)Time elapsed: 0.117 s
% 0.21/0.53  % (5989)------------------------------
% 0.21/0.53  % (5989)------------------------------
% 0.21/0.53  % (5997)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (6004)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (5987)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (5985)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f81,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    sK2 != k2_mcart_1(sK0)),
% 0.21/0.54    inference(resolution,[],[f28,f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ~r2_hidden(k1_mcart_1(sK0),sK1) | sK2 != k2_mcart_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))) => (((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f6])).
% 0.21/0.54  % (6006)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  fof(f6,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.21/0.54    inference(resolution,[],[f15,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3)))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    sK2 = k2_mcart_1(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f75,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    sK3 != k2_mcart_1(sK0)),
% 0.21/0.54    inference(resolution,[],[f17,f28])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ~r2_hidden(k1_mcart_1(sK0),sK1) | sK3 != k2_mcart_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    sK3 = k2_mcart_1(sK0) | sK2 = k2_mcart_1(sK0)),
% 0.21/0.54    inference(resolution,[],[f73,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK2,sK3))),
% 0.21/0.54    inference(resolution,[],[f15,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X10,X8,X9] : (~r2_hidden(X8,k2_tarski(X9,X10)) | X8 = X10 | X8 = X9) )),
% 0.21/0.54    inference(forward_demodulation,[],[f72,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X10,X8,X9] : (X8 = X10 | ~r2_hidden(X8,k2_tarski(X9,X10)) | k1_mcart_1(k4_tarski(X8,k1_mcart_1(sK0))) = X9) )),
% 0.21/0.54    inference(forward_demodulation,[],[f64,f19])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X10,X8,X9] : (~r2_hidden(X8,k2_tarski(X9,X10)) | k1_mcart_1(k4_tarski(X8,k1_mcart_1(sK0))) = X10 | k1_mcart_1(k4_tarski(X8,k1_mcart_1(sK0))) = X9) )),
% 0.21/0.54    inference(resolution,[],[f39,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)) | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,k1_mcart_1(sK0)),k2_zfmisc_1(X3,sK1)) | ~r2_hidden(X2,X3)) )),
% 0.21/0.54    inference(resolution,[],[f28,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (6004)------------------------------
% 0.21/0.54  % (6004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6004)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (6004)Memory used [KB]: 1791
% 0.21/0.54  % (6004)Time elapsed: 0.056 s
% 0.21/0.54  % (6004)------------------------------
% 0.21/0.54  % (6004)------------------------------
% 0.21/0.54  % (5984)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (5992)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (5975)Success in time 0.171 s
%------------------------------------------------------------------------------
