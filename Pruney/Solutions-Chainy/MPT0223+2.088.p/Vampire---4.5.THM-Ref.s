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
% DateTime   : Thu Dec  3 12:36:02 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 131 expanded)
%              Number of leaves         :    9 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 ( 184 expanded)
%              Number of equality atoms :   30 ( 132 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f37,f75,f75,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

% (12207)Refutation not found, incomplete strategy% (12207)------------------------------
% (12207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

% (12207)Termination reason: Refutation not found, incomplete strategy

% (12207)Memory used [KB]: 10618
% (12207)Time elapsed: 0.106 s
% (12207)------------------------------
% (12207)------------------------------
fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f75,plain,(
    ! [X1] : r2_hidden(sK0,X1) ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r2_hidden(sK0,X1) ) ),
    inference(forward_demodulation,[],[f68,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f68,plain,(
    ! [X1] :
      ( k1_xboole_0 != k3_xboole_0(X1,k1_xboole_0)
      | r2_hidden(sK0,X1) ) ),
    inference(superposition,[],[f53,f60])).

fof(f60,plain,(
    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f50,f58])).

fof(f58,plain,(
    k1_xboole_0 = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f54,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f54,plain,(
    r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f29,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f35,f47,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f29,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f50,plain,(
    k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f28,f47,f47,f47])).

fof(f28,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) != k3_xboole_0(X0,k1_enumset1(X1,X1,X1))
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f44,f47,f47])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:34:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (12228)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.49  % (12208)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % (12208)Refutation not found, incomplete strategy% (12208)------------------------------
% 0.22/0.49  % (12208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12208)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (12208)Memory used [KB]: 10618
% 0.22/0.49  % (12208)Time elapsed: 0.052 s
% 0.22/0.49  % (12208)------------------------------
% 0.22/0.49  % (12208)------------------------------
% 0.22/0.50  % (12213)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (12204)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.17/0.51  % (12227)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.17/0.52  % (12202)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.52  % (12209)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.17/0.52  % (12203)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.52  % (12207)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.17/0.52  % (12209)Refutation not found, incomplete strategy% (12209)------------------------------
% 1.17/0.52  % (12209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (12209)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.52  
% 1.17/0.52  % (12209)Memory used [KB]: 10618
% 1.17/0.52  % (12209)Time elapsed: 0.106 s
% 1.17/0.52  % (12209)------------------------------
% 1.17/0.52  % (12209)------------------------------
% 1.17/0.52  % (12202)Refutation found. Thanks to Tanya!
% 1.17/0.52  % SZS status Theorem for theBenchmark
% 1.17/0.52  % SZS output start Proof for theBenchmark
% 1.17/0.52  fof(f80,plain,(
% 1.17/0.52    $false),
% 1.17/0.52    inference(unit_resulting_resolution,[],[f37,f75,f75,f38])).
% 1.17/0.52  fof(f38,plain,(
% 1.17/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f26])).
% 1.17/0.52  % (12207)Refutation not found, incomplete strategy% (12207)------------------------------
% 1.17/0.52  % (12207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  fof(f26,plain,(
% 1.17/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.17/0.52    inference(ennf_transformation,[],[f23])).
% 1.17/0.52  % (12207)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.52  
% 1.17/0.52  % (12207)Memory used [KB]: 10618
% 1.17/0.52  % (12207)Time elapsed: 0.106 s
% 1.17/0.52  % (12207)------------------------------
% 1.17/0.52  % (12207)------------------------------
% 1.17/0.52  fof(f23,plain,(
% 1.17/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.17/0.52    inference(rectify,[],[f2])).
% 1.17/0.52  fof(f2,axiom,(
% 1.17/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.17/0.52  fof(f75,plain,(
% 1.17/0.52    ( ! [X1] : (r2_hidden(sK0,X1)) )),
% 1.17/0.52    inference(trivial_inequality_removal,[],[f74])).
% 1.17/0.52  fof(f74,plain,(
% 1.17/0.52    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,X1)) )),
% 1.17/0.52    inference(forward_demodulation,[],[f68,f33])).
% 1.17/0.52  fof(f33,plain,(
% 1.17/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f6])).
% 1.17/0.52  fof(f6,axiom,(
% 1.17/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.17/0.52  fof(f68,plain,(
% 1.17/0.52    ( ! [X1] : (k1_xboole_0 != k3_xboole_0(X1,k1_xboole_0) | r2_hidden(sK0,X1)) )),
% 1.17/0.52    inference(superposition,[],[f53,f60])).
% 1.17/0.52  fof(f60,plain,(
% 1.17/0.52    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 1.17/0.52    inference(backward_demodulation,[],[f50,f58])).
% 1.17/0.52  fof(f58,plain,(
% 1.17/0.52    k1_xboole_0 = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 1.17/0.52    inference(unit_resulting_resolution,[],[f54,f31])).
% 1.17/0.52  fof(f31,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.17/0.52    inference(cnf_transformation,[],[f1])).
% 1.17/0.52  fof(f1,axiom,(
% 1.17/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.17/0.52  fof(f54,plain,(
% 1.17/0.52    r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 1.17/0.52    inference(unit_resulting_resolution,[],[f29,f51])).
% 1.17/0.52  fof(f51,plain,(
% 1.17/0.52    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 = X1) )),
% 1.17/0.52    inference(definition_unfolding,[],[f35,f47,f47])).
% 1.17/0.52  fof(f47,plain,(
% 1.17/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.17/0.52    inference(definition_unfolding,[],[f45,f42])).
% 1.17/0.52  fof(f42,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f13])).
% 1.17/0.52  fof(f13,axiom,(
% 1.17/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.17/0.52  fof(f45,plain,(
% 1.17/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f12])).
% 1.17/0.52  fof(f12,axiom,(
% 1.17/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.17/0.52  fof(f35,plain,(
% 1.17/0.52    ( ! [X0,X1] : (X0 = X1 | r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.17/0.52    inference(cnf_transformation,[],[f25])).
% 1.17/0.52  fof(f25,plain,(
% 1.17/0.52    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.17/0.52    inference(ennf_transformation,[],[f20])).
% 1.17/0.52  fof(f20,axiom,(
% 1.17/0.52    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 1.17/0.52  fof(f29,plain,(
% 1.17/0.52    sK0 != sK1),
% 1.17/0.52    inference(cnf_transformation,[],[f24])).
% 1.17/0.52  fof(f24,plain,(
% 1.17/0.52    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.17/0.52    inference(ennf_transformation,[],[f22])).
% 1.17/0.52  fof(f22,negated_conjecture,(
% 1.17/0.52    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.17/0.52    inference(negated_conjecture,[],[f21])).
% 1.17/0.52  fof(f21,conjecture,(
% 1.17/0.52    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 1.17/0.52  fof(f50,plain,(
% 1.17/0.52    k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 1.17/0.52    inference(definition_unfolding,[],[f28,f47,f47,f47])).
% 1.17/0.52  fof(f28,plain,(
% 1.17/0.52    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.17/0.52    inference(cnf_transformation,[],[f24])).
% 1.17/0.52  fof(f53,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) != k3_xboole_0(X0,k1_enumset1(X1,X1,X1)) | r2_hidden(X1,X0)) )),
% 1.17/0.52    inference(definition_unfolding,[],[f44,f47,f47])).
% 1.17/0.52  fof(f44,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) | r2_hidden(X1,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f27])).
% 1.17/0.52  fof(f27,plain,(
% 1.17/0.52    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 1.17/0.52    inference(ennf_transformation,[],[f19])).
% 1.17/0.52  fof(f19,axiom,(
% 1.17/0.52    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 1.17/0.52  fof(f37,plain,(
% 1.17/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f8])).
% 1.17/0.52  fof(f8,axiom,(
% 1.17/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.17/0.52  % SZS output end Proof for theBenchmark
% 1.17/0.52  % (12202)------------------------------
% 1.17/0.52  % (12202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (12202)Termination reason: Refutation
% 1.17/0.52  
% 1.17/0.52  % (12202)Memory used [KB]: 6268
% 1.17/0.52  % (12202)Time elapsed: 0.107 s
% 1.17/0.52  % (12202)------------------------------
% 1.17/0.52  % (12202)------------------------------
% 1.17/0.53  % (12224)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.17/0.54  % (12216)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.17/0.54  % (12216)Refutation not found, incomplete strategy% (12216)------------------------------
% 1.17/0.54  % (12216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.54  % (12216)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.54  
% 1.17/0.54  % (12216)Memory used [KB]: 10618
% 1.17/0.54  % (12216)Time elapsed: 0.123 s
% 1.17/0.54  % (12216)------------------------------
% 1.17/0.54  % (12216)------------------------------
% 1.17/0.54  % (12198)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.17/0.54  % (12198)Refutation not found, incomplete strategy% (12198)------------------------------
% 1.17/0.54  % (12198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.54  % (12198)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.54  
% 1.17/0.54  % (12198)Memory used [KB]: 1663
% 1.17/0.54  % (12198)Time elapsed: 0.117 s
% 1.17/0.54  % (12198)------------------------------
% 1.17/0.54  % (12198)------------------------------
% 1.17/0.54  % (12201)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.54  % (12200)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.54  % (12225)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (12226)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (12200)Refutation not found, incomplete strategy% (12200)------------------------------
% 1.36/0.54  % (12200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (12200)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (12200)Memory used [KB]: 10746
% 1.36/0.54  % (12200)Time elapsed: 0.128 s
% 1.36/0.54  % (12200)------------------------------
% 1.36/0.54  % (12200)------------------------------
% 1.36/0.54  % (12220)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.54  % (12220)Refutation not found, incomplete strategy% (12220)------------------------------
% 1.36/0.54  % (12220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (12220)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (12220)Memory used [KB]: 1663
% 1.36/0.54  % (12220)Time elapsed: 0.129 s
% 1.36/0.54  % (12220)------------------------------
% 1.36/0.54  % (12220)------------------------------
% 1.36/0.54  % (12197)Success in time 0.178 s
%------------------------------------------------------------------------------
