%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   12 (  17 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  34 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11,f9])).

fof(f9,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f6])).

fof(f6,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f11,plain,(
    r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f8,f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).

fof(f8,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:32:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (8076)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.45  % (8076)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f11,f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ~r2_hidden(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f6])).
% 0.21/0.45  fof(f6,plain,(
% 0.21/0.45    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f4,plain,(
% 0.21/0.45    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.21/0.45    inference(negated_conjecture,[],[f2])).
% 0.21/0.45  fof(f2,conjecture,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    r2_hidden(sK0,sK1)),
% 0.21/0.45    inference(resolution,[],[f8,f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,plain,(
% 0.21/0.45    ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (8076)------------------------------
% 0.21/0.45  % (8076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (8076)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (8076)Memory used [KB]: 9722
% 0.21/0.45  % (8076)Time elapsed: 0.033 s
% 0.21/0.45  % (8076)------------------------------
% 0.21/0.45  % (8076)------------------------------
% 0.21/0.46  % (8066)Success in time 0.096 s
%------------------------------------------------------------------------------
