%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 973 expanded)
%              Number of leaves         :    8 ( 298 expanded)
%              Depth                    :   21
%              Number of atoms          :  110 (2753 expanded)
%              Number of equality atoms :   36 ( 918 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(subsumption_resolution,[],[f114,f48])).

fof(f48,plain,(
    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(forward_demodulation,[],[f46,f33])).

fof(f33,plain,(
    sK4(sK0) = k1_mcart_1(sK0) ),
    inference(superposition,[],[f18,f28])).

fof(f28,plain,(
    sK0 = k4_tarski(sK4(sK0),sK5(sK0)) ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f16,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f16,plain,(
    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ! [X4,X5,X6] :
        ( k3_mcart_1(X4,X5,X6) != sK0
        | ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1) )
    & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f10])).

fof(f10,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK4(X0),sK5(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK4(X0),sK5(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f9,f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK4(X0),sK5(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f18,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f46,plain,(
    sK0 = k4_tarski(sK4(sK0),k2_mcart_1(sK0)) ),
    inference(backward_demodulation,[],[f28,f32])).

fof(f32,plain,(
    sK5(sK0) = k2_mcart_1(sK0) ),
    inference(superposition,[],[f19,f28])).

fof(f19,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5])).

fof(f114,plain,(
    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(resolution,[],[f106,f54])).

fof(f54,plain,(
    r2_hidden(k2_mcart_1(sK0),sK3) ),
    inference(resolution,[],[f49,f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | r2_hidden(k2_mcart_1(sK0),X1) ) ),
    inference(superposition,[],[f24,f48])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f106,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK3)
      | sK0 != k4_tarski(k1_mcart_1(sK0),X4) ) ),
    inference(global_subsumption,[],[f102,f105])).

fof(f105,plain,(
    ! [X4] :
      ( sK0 != k4_tarski(k1_mcart_1(sK0),X4)
      | ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1) ) ),
    inference(subsumption_resolution,[],[f82,f94])).

fof(f94,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2) ),
    inference(resolution,[],[f80,f55])).

fof(f55,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f50,f27])).

fof(f50,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3))
      | r2_hidden(k1_mcart_1(sK0),X2) ) ),
    inference(superposition,[],[f23,f48])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(X0,X1))
      | r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),X1) ) ),
    inference(superposition,[],[f24,f79])).

fof(f79,plain,(
    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0))) ),
    inference(forward_demodulation,[],[f74,f61])).

fof(f61,plain,(
    sK4(k1_mcart_1(sK0)) = k1_mcart_1(k1_mcart_1(sK0)) ),
    inference(superposition,[],[f18,f56])).

fof(f56,plain,(
    k1_mcart_1(sK0) = k4_tarski(sK4(k1_mcart_1(sK0)),sK5(k1_mcart_1(sK0))) ),
    inference(resolution,[],[f55,f22])).

fof(f74,plain,(
    k1_mcart_1(sK0) = k4_tarski(sK4(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0))) ),
    inference(backward_demodulation,[],[f56,f60])).

fof(f60,plain,(
    sK5(k1_mcart_1(sK0)) = k2_mcart_1(k1_mcart_1(sK0)) ),
    inference(superposition,[],[f19,f56])).

fof(f82,plain,(
    ! [X4] :
      ( sK0 != k4_tarski(k1_mcart_1(sK0),X4)
      | ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1) ) ),
    inference(superposition,[],[f26,f79])).

fof(f26,plain,(
    ! [X6,X4,X5] :
      ( sK0 != k4_tarski(k4_tarski(X4,X5),X6)
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(definition_unfolding,[],[f17,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f17,plain,(
    ! [X6,X4,X5] :
      ( k3_mcart_1(X4,X5,X6) != sK0
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f102,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1) ),
    inference(resolution,[],[f81,f55])).

fof(f81,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(X2,X3))
      | r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),X2) ) ),
    inference(superposition,[],[f23,f79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:57:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (1956)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (1958)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (1971)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (1974)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (1956)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f114,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.21/0.56    inference(forward_demodulation,[],[f46,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    sK4(sK0) = k1_mcart_1(sK0)),
% 0.21/0.56    inference(superposition,[],[f18,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    sK0 = k4_tarski(sK4(sK0),sK5(sK0))),
% 0.21/0.56    inference(resolution,[],[f22,f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.21/0.56    inference(definition_unfolding,[],[f16,f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f10])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))) => (! [X6,X5,X4] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f8,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.21/0.56    inference(negated_conjecture,[],[f6])).
% 0.21/0.56  fof(f6,conjecture,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK4(X0),sK5(X0)) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k4_tarski(sK4(X0),sK5(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f9,f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK4(X0),sK5(X0)) = X0)),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f9,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    sK0 = k4_tarski(sK4(sK0),k2_mcart_1(sK0))),
% 0.21/0.56    inference(backward_demodulation,[],[f28,f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    sK5(sK0) = k2_mcart_1(sK0)),
% 0.21/0.56    inference(superposition,[],[f19,f28])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.21/0.56    inference(resolution,[],[f106,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    r2_hidden(k2_mcart_1(sK0),sK3)),
% 0.21/0.57    inference(resolution,[],[f49,f27])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | r2_hidden(k2_mcart_1(sK0),X1)) )),
% 0.21/0.57    inference(superposition,[],[f24,f48])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.57    inference(flattening,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.57    inference(nnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    ( ! [X4] : (~r2_hidden(X4,sK3) | sK0 != k4_tarski(k1_mcart_1(sK0),X4)) )),
% 0.21/0.57    inference(global_subsumption,[],[f102,f105])).
% 0.21/0.57  fof(f105,plain,(
% 0.21/0.57    ( ! [X4] : (sK0 != k4_tarski(k1_mcart_1(sK0),X4) | ~r2_hidden(X4,sK3) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f82,f94])).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2)),
% 0.21/0.57    inference(resolution,[],[f80,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(sK1,sK2))),
% 0.21/0.57    inference(resolution,[],[f50,f27])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r2_hidden(sK0,k2_zfmisc_1(X2,X3)) | r2_hidden(k1_mcart_1(sK0),X2)) )),
% 0.21/0.57    inference(superposition,[],[f23,f48])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(X0,X1)) | r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),X1)) )),
% 0.21/0.57    inference(superposition,[],[f24,f79])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)))),
% 0.21/0.57    inference(forward_demodulation,[],[f74,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    sK4(k1_mcart_1(sK0)) = k1_mcart_1(k1_mcart_1(sK0))),
% 0.21/0.57    inference(superposition,[],[f18,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    k1_mcart_1(sK0) = k4_tarski(sK4(k1_mcart_1(sK0)),sK5(k1_mcart_1(sK0)))),
% 0.21/0.57    inference(resolution,[],[f55,f22])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    k1_mcart_1(sK0) = k4_tarski(sK4(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)))),
% 0.21/0.57    inference(backward_demodulation,[],[f56,f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    sK5(k1_mcart_1(sK0)) = k2_mcart_1(k1_mcart_1(sK0))),
% 0.21/0.57    inference(superposition,[],[f19,f56])).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    ( ! [X4] : (sK0 != k4_tarski(k1_mcart_1(sK0),X4) | ~r2_hidden(X4,sK3) | ~r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1)) )),
% 0.21/0.57    inference(superposition,[],[f26,f79])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ( ! [X6,X4,X5] : (sK0 != k4_tarski(k4_tarski(X4,X5),X6) | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f17,f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ( ! [X6,X4,X5] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1)),
% 0.21/0.57    inference(resolution,[],[f81,f55])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(X2,X3)) | r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),X2)) )),
% 0.21/0.57    inference(superposition,[],[f23,f79])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (1956)------------------------------
% 0.21/0.57  % (1956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (1956)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (1956)Memory used [KB]: 10746
% 0.21/0.57  % (1956)Time elapsed: 0.128 s
% 0.21/0.57  % (1956)------------------------------
% 0.21/0.57  % (1956)------------------------------
% 0.21/0.57  % (1952)Success in time 0.203 s
%------------------------------------------------------------------------------
