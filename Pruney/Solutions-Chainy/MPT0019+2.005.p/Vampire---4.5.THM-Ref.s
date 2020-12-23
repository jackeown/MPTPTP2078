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
% DateTime   : Thu Dec  3 12:29:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  37 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  93 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(subsumption_resolution,[],[f83,f9])).

fof(f9,plain,(
    sK1 != k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(X0,X1) != X1
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => k2_xboole_0(X0,X1) = X1 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f83,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f78,f48])).

fof(f48,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK2(X4,X5,X5),X4)
      | k2_xboole_0(X4,X5) = X5 ) ),
    inference(subsumption_resolution,[],[f44,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f44,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK2(X4,X5,X5),X4)
      | r2_hidden(sK2(X4,X5,X5),X5)
      | k2_xboole_0(X4,X5) = X5 ) ),
    inference(factoring,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f78,plain,(
    ~ r2_hidden(sK2(sK0,sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f73,f9])).

fof(f73,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | sK1 = k2_xboole_0(sK0,sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK1),sK0) ),
    inference(resolution,[],[f48,f25])).

fof(f25,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK2(X8,X9,sK1),sK0)
      | sK1 = k2_xboole_0(X8,X9)
      | ~ r2_hidden(sK2(X8,X9,sK1),X8) ) ),
    inference(resolution,[],[f11,f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f10,f8])).

fof(f8,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

% (4003)Refutation not found, incomplete strategy% (4003)------------------------------
% (4003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:55:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (3983)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (3987)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (3987)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (3995)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (4003)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f83,f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    sK1 != k2_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0,X1] : (k2_xboole_0(X0,X1) != X1 & r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.51    inference(negated_conjecture,[],[f3])).
% 0.21/0.51  fof(f3,conjecture,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f78,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X4,X5] : (r2_hidden(sK2(X4,X5,X5),X4) | k2_xboole_0(X4,X5) = X5) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f44,f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X4,X5] : (r2_hidden(sK2(X4,X5,X5),X4) | r2_hidden(sK2(X4,X5,X5),X5) | k2_xboole_0(X4,X5) = X5) )),
% 0.21/0.51    inference(factoring,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~r2_hidden(sK2(sK0,sK1,sK1),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f73,f9])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(sK0,sK1) | ~r2_hidden(sK2(sK0,sK1,sK1),sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(sK0,sK1) | sK1 = k2_xboole_0(sK0,sK1) | ~r2_hidden(sK2(sK0,sK1,sK1),sK0)),
% 0.21/0.51    inference(resolution,[],[f48,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X8,X9] : (~r2_hidden(sK2(X8,X9,sK1),sK0) | sK1 = k2_xboole_0(X8,X9) | ~r2_hidden(sK2(X8,X9,sK1),X8)) )),
% 0.21/0.51    inference(resolution,[],[f11,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.51    inference(resolution,[],[f10,f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.51  % (4003)Refutation not found, incomplete strategy% (4003)------------------------------
% 0.21/0.51  % (4003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (3987)------------------------------
% 0.21/0.51  % (3987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3987)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (3987)Memory used [KB]: 6268
% 0.21/0.51  % (3987)Time elapsed: 0.098 s
% 0.21/0.51  % (3987)------------------------------
% 0.21/0.51  % (3987)------------------------------
% 0.21/0.52  % (3986)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (3981)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (3980)Success in time 0.152 s
%------------------------------------------------------------------------------
