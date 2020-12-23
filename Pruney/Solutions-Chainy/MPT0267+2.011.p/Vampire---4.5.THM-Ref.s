%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  75 expanded)
%              Number of leaves         :    3 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 194 expanded)
%              Number of equality atoms :   21 (  60 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(subsumption_resolution,[],[f38,f24])).

fof(f24,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f38,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f36,f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f36,plain,(
    r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f35,f33])).

fof(f33,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f32,f22])).

fof(f22,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f32,plain,
    ( sK0 = sK2
    | r2_hidden(sK0,k1_tarski(sK2)) ),
    inference(resolution,[],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK0,k4_xboole_0(sK1,X0))
      | r2_hidden(sK0,X0) ) ),
    inference(resolution,[],[f25,f19])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f7,f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f26,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
    | sK0 = sK2 ),
    inference(subsumption_resolution,[],[f6,f25])).

fof(f6,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f5])).

fof(f35,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0)))
    | sK0 != sK2 ),
    inference(backward_demodulation,[],[f8,f33])).

fof(f8,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:53:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (32423)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (32425)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (32425)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f38,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.21/0.51    inference(equality_resolution,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.21/0.51    inference(equality_resolution,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ~r2_hidden(sK0,k1_tarski(sK0))),
% 0.21/0.51    inference(resolution,[],[f36,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f35,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    sK0 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f32,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.21/0.51    inference(equality_resolution,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    sK0 = sK2 | r2_hidden(sK0,k1_tarski(sK2))),
% 0.21/0.51    inference(resolution,[],[f26,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK0,k4_xboole_0(sK1,X0)) | r2_hidden(sK0,X0)) )),
% 0.21/0.51    inference(resolution,[],[f25,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f7,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f3])).
% 0.21/0.51  fof(f3,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) | sK0 = sK2),
% 0.21/0.51    inference(subsumption_resolution,[],[f6,f25])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ~r2_hidden(sK0,sK1) | sK0 = sK2 | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0))) | sK0 != sK2),
% 0.21/0.51    inference(backward_demodulation,[],[f8,f33])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    sK0 != sK2 | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (32425)------------------------------
% 0.21/0.51  % (32425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32425)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (32425)Memory used [KB]: 6140
% 0.21/0.51  % (32425)Time elapsed: 0.095 s
% 0.21/0.51  % (32425)------------------------------
% 0.21/0.51  % (32425)------------------------------
% 0.21/0.51  % (32433)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (32444)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (32424)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (32432)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (32419)Success in time 0.151 s
%------------------------------------------------------------------------------
