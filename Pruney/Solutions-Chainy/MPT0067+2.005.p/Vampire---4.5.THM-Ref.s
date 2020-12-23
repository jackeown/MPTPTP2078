%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:23 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   24 (  39 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 104 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(subsumption_resolution,[],[f25,f24])).

fof(f24,plain,(
    ~ r2_hidden(sK3(sK1,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f17,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f7,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f17,plain,(
    r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( r2_xboole_0(sK1,sK0)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) )
   => ( r2_xboole_0(sK1,sK0)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( r2_xboole_0(X1,X0)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_xboole_0(X1,X0)
          & r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f25,plain,(
    r2_hidden(sK3(sK1,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f16,f23,f18])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f12])).

% (31887)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f23,plain,(
    r2_hidden(sK3(sK1,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f17,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:50:26 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.23/0.47  % (31884)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.23/0.48  % (31894)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.23/0.49  % (31896)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.23/0.49  % (31896)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(subsumption_resolution,[],[f25,f24])).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    ~r2_hidden(sK3(sK1,sK0),sK1)),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f17,f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f15])).
% 0.23/0.49  fof(f15,plain,(
% 0.23/0.49    ! [X0,X1] : ((~r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f7,f14])).
% 0.23/0.49  fof(f14,plain,(
% 0.23/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1)))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f7,plain,(
% 0.23/0.49    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    r2_xboole_0(sK1,sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f9])).
% 0.23/0.49  fof(f9,plain,(
% 0.23/0.49    r2_xboole_0(sK1,sK0) & r1_tarski(sK0,sK1)),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).
% 0.23/0.49  fof(f8,plain,(
% 0.23/0.49    ? [X0,X1] : (r2_xboole_0(X1,X0) & r1_tarski(X0,X1)) => (r2_xboole_0(sK1,sK0) & r1_tarski(sK0,sK1))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f5,plain,(
% 0.23/0.49    ? [X0,X1] : (r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,negated_conjecture,(
% 0.23/0.49    ~! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.23/0.49    inference(negated_conjecture,[],[f3])).
% 0.23/0.49  fof(f3,conjecture,(
% 0.23/0.49    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    r2_hidden(sK3(sK1,sK0),sK1)),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f16,f23,f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f13])).
% 0.23/0.49  fof(f13,plain,(
% 0.23/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f12])).
% 0.23/0.49  % (31887)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.23/0.49  fof(f12,plain,(
% 0.23/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f11,plain,(
% 0.23/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.49    inference(rectify,[],[f10])).
% 0.23/0.49  fof(f10,plain,(
% 0.23/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.23/0.49    inference(nnf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,plain,(
% 0.23/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    r2_hidden(sK3(sK1,sK0),sK0)),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f17,f21])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f15])).
% 0.23/0.49  fof(f16,plain,(
% 0.23/0.49    r1_tarski(sK0,sK1)),
% 0.23/0.49    inference(cnf_transformation,[],[f9])).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (31896)------------------------------
% 0.23/0.49  % (31896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (31896)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (31896)Memory used [KB]: 5373
% 0.23/0.49  % (31896)Time elapsed: 0.063 s
% 0.23/0.49  % (31896)------------------------------
% 0.23/0.49  % (31896)------------------------------
% 0.23/0.50  % (31881)Success in time 0.123 s
%------------------------------------------------------------------------------
