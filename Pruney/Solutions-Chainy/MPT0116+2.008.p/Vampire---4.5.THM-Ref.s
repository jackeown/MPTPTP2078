%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  41 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 (  99 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(subsumption_resolution,[],[f34,f15])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f34,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK2),sK0) ),
    inference(backward_demodulation,[],[f14,f31])).

fof(f31,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,
    ( r2_xboole_0(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f18,f13])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f29,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f26,f21])).

fof(f21,plain,(
    ~ r2_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f16,f14])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X2,X3,X1] :
      ( r2_xboole_0(k4_xboole_0(X1,X3),X2)
      | ~ r2_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f19,f15])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X2)
      | r2_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l58_xboole_1)).

fof(f14,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:19:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (21041)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.46  % (21041)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f34,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ~r1_tarski(k4_xboole_0(sK0,sK2),sK0)),
% 0.21/0.46    inference(backward_demodulation,[],[f14,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    sK0 = sK1),
% 0.21/0.46    inference(resolution,[],[f29,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    r2_xboole_0(sK0,sK1) | sK0 = sK1),
% 0.21/0.46    inference(resolution,[],[f18,f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    r1_tarski(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.21/0.46    inference(negated_conjecture,[],[f4])).
% 0.21/0.46  fof(f4,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ~r2_xboole_0(sK0,sK1)),
% 0.21/0.46    inference(resolution,[],[f26,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ~r2_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.46    inference(resolution,[],[f16,f14])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X2,X3,X1] : (r2_xboole_0(k4_xboole_0(X1,X3),X2) | ~r2_xboole_0(X1,X2)) )),
% 0.21/0.46    inference(resolution,[],[f19,f15])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X2) | r2_xboole_0(X0,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r2_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l58_xboole_1)).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (21041)------------------------------
% 0.21/0.46  % (21041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (21041)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (21041)Memory used [KB]: 1663
% 0.21/0.46  % (21041)Time elapsed: 0.057 s
% 0.21/0.46  % (21041)------------------------------
% 0.21/0.46  % (21041)------------------------------
% 0.21/0.46  % (21023)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (21022)Success in time 0.108 s
%------------------------------------------------------------------------------
