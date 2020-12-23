%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:50 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   25 (  36 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 (  95 expanded)
%              Number of equality atoms :   38 (  50 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(subsumption_resolution,[],[f43,f41])).

fof(f41,plain,(
    r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f18,f19,f19])).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

fof(f18,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
        & X0 != X1 )
   => ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f19])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f43,plain,(
    ~ r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(extensionality_resolution,[],[f39,f17])).

fof(f17,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f24,f19])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:46:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (15343)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (15354)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.27/0.53  % (15346)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.27/0.53  % (15362)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.27/0.53  % (15343)Refutation found. Thanks to Tanya!
% 1.27/0.53  % SZS status Theorem for theBenchmark
% 1.27/0.54  % (15359)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.54  % SZS output start Proof for theBenchmark
% 1.27/0.54  fof(f46,plain,(
% 1.27/0.54    $false),
% 1.27/0.54    inference(subsumption_resolution,[],[f43,f41])).
% 1.27/0.54  fof(f41,plain,(
% 1.27/0.54    r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.27/0.54    inference(resolution,[],[f32,f28])).
% 1.27/0.54  fof(f28,plain,(
% 1.27/0.54    ~r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.27/0.54    inference(definition_unfolding,[],[f18,f19,f19])).
% 1.27/0.54  fof(f19,plain,(
% 1.27/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f2])).
% 1.27/0.54  fof(f2,axiom,(
% 1.27/0.54    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).
% 1.27/0.54  fof(f18,plain,(
% 1.27/0.54    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.27/0.54    inference(cnf_transformation,[],[f12])).
% 1.27/0.54  fof(f12,plain,(
% 1.27/0.54    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) & sK0 != sK1),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f11])).
% 1.27/0.54  fof(f11,plain,(
% 1.27/0.54    ? [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1) => (~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) & sK0 != sK1)),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f9,plain,(
% 1.27/0.54    ? [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1)),
% 1.27/0.54    inference(ennf_transformation,[],[f8])).
% 1.27/0.54  fof(f8,negated_conjecture,(
% 1.27/0.54    ~! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.27/0.54    inference(negated_conjecture,[],[f7])).
% 1.27/0.54  fof(f7,conjecture,(
% 1.27/0.54    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 1.27/0.54  fof(f32,plain,(
% 1.27/0.54    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.27/0.54    inference(definition_unfolding,[],[f23,f19])).
% 1.27/0.54  fof(f23,plain,(
% 1.27/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f10])).
% 1.27/0.54  fof(f10,plain,(
% 1.27/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f6])).
% 1.27/0.54  fof(f6,axiom,(
% 1.27/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.27/0.54  fof(f43,plain,(
% 1.27/0.54    ~r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.27/0.54    inference(extensionality_resolution,[],[f39,f17])).
% 1.27/0.54  fof(f17,plain,(
% 1.27/0.54    sK0 != sK1),
% 1.27/0.54    inference(cnf_transformation,[],[f12])).
% 1.27/0.54  fof(f39,plain,(
% 1.27/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.27/0.54    inference(equality_resolution,[],[f36])).
% 1.27/0.54  fof(f36,plain,(
% 1.27/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.27/0.54    inference(definition_unfolding,[],[f24,f19])).
% 1.27/0.54  fof(f24,plain,(
% 1.27/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.27/0.54    inference(cnf_transformation,[],[f16])).
% 1.27/0.54  fof(f16,plain,(
% 1.27/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).
% 1.27/0.54  fof(f15,plain,(
% 1.27/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f14,plain,(
% 1.27/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.27/0.54    inference(rectify,[],[f13])).
% 1.27/0.54  fof(f13,plain,(
% 1.27/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.27/0.54    inference(nnf_transformation,[],[f1])).
% 1.27/0.54  fof(f1,axiom,(
% 1.27/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.27/0.54  % SZS output end Proof for theBenchmark
% 1.27/0.54  % (15343)------------------------------
% 1.27/0.54  % (15343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (15343)Termination reason: Refutation
% 1.27/0.54  
% 1.27/0.54  % (15343)Memory used [KB]: 10618
% 1.27/0.54  % (15343)Time elapsed: 0.108 s
% 1.27/0.54  % (15343)------------------------------
% 1.27/0.54  % (15343)------------------------------
% 1.27/0.54  % (15353)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.27/0.54  % (15336)Success in time 0.17 s
%------------------------------------------------------------------------------
