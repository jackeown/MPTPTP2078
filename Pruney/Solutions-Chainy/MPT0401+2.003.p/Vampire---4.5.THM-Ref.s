%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:14 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 105 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  108 ( 286 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f358,plain,(
    $false ),
    inference(subsumption_resolution,[],[f355,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

% (23494)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f355,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(backward_demodulation,[],[f89,f338])).

fof(f338,plain,(
    sK0 = sK3(k1_tarski(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f186,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f186,plain,(
    r1_tarski(k1_tarski(sK3(k1_tarski(sK0),sK0)),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f90,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f90,plain,(
    r2_hidden(sK3(k1_tarski(sK0),sK0),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f74,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f74,plain,(
    ~ r1_tarski(k3_tarski(k1_tarski(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f52,f55,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f55,plain,(
    ~ r1_tarski(k3_tarski(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f50,f32,f33])).

fof(f32,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK2,sK0)
    & r2_hidden(sK2,sK1)
    & r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X0)
            & r2_hidden(X2,X1) )
        & r1_setfam_1(X1,k1_tarski(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK0)
          & r2_hidden(X2,sK1) )
      & r1_setfam_1(sK1,k1_tarski(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,sK0)
        & r2_hidden(X2,sK1) )
   => ( ~ r1_tarski(sK2,sK0)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

fof(f50,plain,(
    r1_tarski(sK2,k3_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f31,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f31,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    r1_tarski(k3_tarski(sK1),k3_tarski(k1_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f30,plain,(
    r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    ~ r1_tarski(sK3(k1_tarski(sK0),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f74,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK3(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 19:22:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.51  % (23474)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.52  % (23492)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.53  % (23484)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.53  % (23489)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.53  % (23469)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.53  % (23475)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.53  % (23481)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.53  % (23476)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.53  % (23485)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.53  % (23486)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.53  % (23473)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.54  % (23482)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.54  % (23469)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f358,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(subsumption_resolution,[],[f355,f44])).
% 0.23/0.54  fof(f44,plain,(
% 0.23/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.54    inference(equality_resolution,[],[f42])).
% 0.23/0.54  % (23494)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.54  fof(f42,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.54    inference(cnf_transformation,[],[f29])).
% 0.23/0.54  fof(f29,plain,(
% 0.23/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.54    inference(flattening,[],[f28])).
% 0.23/0.54  fof(f28,plain,(
% 0.23/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.54    inference(nnf_transformation,[],[f1])).
% 0.23/0.54  fof(f1,axiom,(
% 0.23/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.54  fof(f355,plain,(
% 0.23/0.54    ~r1_tarski(sK0,sK0)),
% 0.23/0.54    inference(backward_demodulation,[],[f89,f338])).
% 0.23/0.54  fof(f338,plain,(
% 0.23/0.54    sK0 = sK3(k1_tarski(sK0),sK0)),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f186,f37])).
% 0.23/0.54  fof(f37,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.23/0.54    inference(cnf_transformation,[],[f19])).
% 0.23/0.54  fof(f19,plain,(
% 0.23/0.54    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.54    inference(ennf_transformation,[],[f10])).
% 0.23/0.54  fof(f10,axiom,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.23/0.54  fof(f186,plain,(
% 0.23/0.54    r1_tarski(k1_tarski(sK3(k1_tarski(sK0),sK0)),k1_tarski(sK0))),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f90,f36])).
% 0.23/0.54  fof(f36,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f25])).
% 0.23/0.54  fof(f25,plain,(
% 0.23/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.23/0.54    inference(nnf_transformation,[],[f8])).
% 0.23/0.54  fof(f8,axiom,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.23/0.54  fof(f90,plain,(
% 0.23/0.54    r2_hidden(sK3(k1_tarski(sK0),sK0),k1_tarski(sK0))),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f74,f38])).
% 0.23/0.54  fof(f38,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f27])).
% 0.23/0.54  fof(f27,plain,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f26])).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f20,plain,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f11])).
% 0.23/0.54  fof(f11,axiom,(
% 0.23/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.23/0.54  fof(f74,plain,(
% 0.23/0.54    ~r1_tarski(k3_tarski(k1_tarski(sK0)),sK0)),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f52,f55,f33])).
% 0.23/0.54  fof(f33,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f17])).
% 0.23/0.54  fof(f17,plain,(
% 0.23/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.54    inference(flattening,[],[f16])).
% 0.23/0.54  fof(f16,plain,(
% 0.23/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.54    inference(ennf_transformation,[],[f4])).
% 0.23/0.54  fof(f4,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.23/0.54  fof(f55,plain,(
% 0.23/0.54    ~r1_tarski(k3_tarski(sK1),sK0)),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f50,f32,f33])).
% 0.23/0.54  fof(f32,plain,(
% 0.23/0.54    ~r1_tarski(sK2,sK0)),
% 0.23/0.54    inference(cnf_transformation,[],[f24])).
% 0.23/0.54  fof(f24,plain,(
% 0.23/0.54    (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22])).
% 0.23/0.54  fof(f22,plain,(
% 0.23/0.54    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0))) => (? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0)))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f23,plain,(
% 0.23/0.54    ? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) => (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f15,plain,(
% 0.23/0.54    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0)))),
% 0.23/0.54    inference(ennf_transformation,[],[f14])).
% 0.23/0.54  fof(f14,negated_conjecture,(
% 0.23/0.54    ~! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.23/0.54    inference(negated_conjecture,[],[f13])).
% 0.23/0.54  fof(f13,conjecture,(
% 0.23/0.54    ! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).
% 0.23/0.54  fof(f50,plain,(
% 0.23/0.54    r1_tarski(sK2,k3_tarski(sK1))),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f31,f40])).
% 0.23/0.54  fof(f40,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f21])).
% 0.23/0.54  fof(f21,plain,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f9])).
% 0.23/0.54  fof(f9,axiom,(
% 0.23/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.23/0.54  fof(f31,plain,(
% 0.23/0.54    r2_hidden(sK2,sK1)),
% 0.23/0.54    inference(cnf_transformation,[],[f24])).
% 0.23/0.54  fof(f52,plain,(
% 0.23/0.54    r1_tarski(k3_tarski(sK1),k3_tarski(k1_tarski(sK0)))),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f30,f34])).
% 0.23/0.54  fof(f34,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r1_setfam_1(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f18])).
% 0.23/0.54  fof(f18,plain,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f12])).
% 0.23/0.54  fof(f12,axiom,(
% 0.23/0.54    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.23/0.54  fof(f30,plain,(
% 0.23/0.54    r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.23/0.54    inference(cnf_transformation,[],[f24])).
% 0.23/0.54  fof(f89,plain,(
% 0.23/0.54    ~r1_tarski(sK3(k1_tarski(sK0),sK0),sK0)),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f74,f39])).
% 0.23/0.54  fof(f39,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r1_tarski(sK3(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f27])).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (23469)------------------------------
% 0.23/0.54  % (23469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (23469)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (23469)Memory used [KB]: 10746
% 0.23/0.54  % (23469)Time elapsed: 0.106 s
% 0.23/0.54  % (23469)------------------------------
% 0.23/0.54  % (23469)------------------------------
% 0.23/0.54  % (23487)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.54  % (23466)Success in time 0.166 s
%------------------------------------------------------------------------------
