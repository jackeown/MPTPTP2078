%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:56 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 163 expanded)
%              Number of leaves         :    7 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :   83 ( 411 expanded)
%              Number of equality atoms :   42 ( 220 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f92])).

fof(f92,plain,(
    ! [X3] : sK1 = X3 ),
    inference(subsumption_resolution,[],[f90,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f90,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_xboole_0,k1_tarski(X3))
      | sK1 = X3 ) ),
    inference(superposition,[],[f39,f83])).

fof(f83,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f82,f63])).

fof(f82,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ r1_tarski(k1_xboole_0,k1_tarski(sK1)) ),
    inference(resolution,[],[f81,f38])).

% (8339)Refutation not found, incomplete strategy% (8339)------------------------------
% (8339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8339)Termination reason: Refutation not found, incomplete strategy

% (8339)Memory used [KB]: 1663
% (8339)Time elapsed: 0.131 s
% (8339)------------------------------
% (8339)------------------------------
fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f81,plain,(
    r1_tarski(k1_tarski(sK1),k1_xboole_0) ),
    inference(superposition,[],[f45,f77])).

fof(f77,plain,(
    k1_xboole_0 = k2_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f74,f35])).

fof(f35,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f16])).

% (8351)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f74,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK2)
    | sK1 = sK3 ),
    inference(resolution,[],[f71,f39])).

fof(f71,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tarski(sK3))
    | k1_xboole_0 = k2_tarski(sK1,sK2) ),
    inference(superposition,[],[f45,f68])).

fof(f68,plain,
    ( k2_tarski(sK1,sK2) = k1_tarski(sK3)
    | k1_xboole_0 = k2_tarski(sK1,sK2) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f34,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f127,plain,(
    ! [X0] : sK1 != X0 ),
    inference(superposition,[],[f35,f115])).

fof(f115,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(subsumption_resolution,[],[f101,f94])).

fof(f94,plain,(
    ! [X0] : r1_tarski(sK1,X0) ),
    inference(backward_demodulation,[],[f46,f92])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(backward_demodulation,[],[f39,f92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n018.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 17:38:12 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.47  % (8343)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.17/0.49  % (8366)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.17/0.49  % (8358)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.17/0.49  % (8360)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.17/0.50  % (8350)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.17/0.50  % (8352)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.17/0.50  % (8342)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.17/0.51  % (8365)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.17/0.51  % (8340)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.17/0.51  % (8357)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.17/0.51  % (8349)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.17/0.52  % (8350)Refutation not found, incomplete strategy% (8350)------------------------------
% 0.17/0.52  % (8350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.52  % (8350)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.52  
% 0.17/0.52  % (8350)Memory used [KB]: 10618
% 0.17/0.52  % (8350)Time elapsed: 0.146 s
% 0.17/0.52  % (8350)------------------------------
% 0.17/0.52  % (8350)------------------------------
% 0.17/0.52  % (8339)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.17/0.52  % (8352)Refutation found. Thanks to Tanya!
% 0.17/0.52  % SZS status Theorem for theBenchmark
% 0.17/0.52  % SZS output start Proof for theBenchmark
% 0.17/0.52  fof(f133,plain,(
% 0.17/0.52    $false),
% 0.17/0.52    inference(subsumption_resolution,[],[f127,f92])).
% 0.17/0.52  fof(f92,plain,(
% 0.17/0.52    ( ! [X3] : (sK1 = X3) )),
% 0.17/0.52    inference(subsumption_resolution,[],[f90,f63])).
% 0.17/0.52  fof(f63,plain,(
% 0.17/0.52    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 0.17/0.52    inference(equality_resolution,[],[f43])).
% 0.17/0.52  fof(f43,plain,(
% 0.17/0.52    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 0.17/0.52    inference(cnf_transformation,[],[f27])).
% 0.17/0.52  fof(f27,plain,(
% 0.17/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.17/0.52    inference(flattening,[],[f26])).
% 0.17/0.52  fof(f26,plain,(
% 0.17/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.17/0.52    inference(nnf_transformation,[],[f12])).
% 0.17/0.52  fof(f12,axiom,(
% 0.17/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.17/0.52  fof(f90,plain,(
% 0.17/0.52    ( ! [X3] : (~r1_tarski(k1_xboole_0,k1_tarski(X3)) | sK1 = X3) )),
% 0.17/0.52    inference(superposition,[],[f39,f83])).
% 0.17/0.52  fof(f83,plain,(
% 0.17/0.52    k1_xboole_0 = k1_tarski(sK1)),
% 0.17/0.52    inference(subsumption_resolution,[],[f82,f63])).
% 0.17/0.52  fof(f82,plain,(
% 0.17/0.52    k1_xboole_0 = k1_tarski(sK1) | ~r1_tarski(k1_xboole_0,k1_tarski(sK1))),
% 0.17/0.52    inference(resolution,[],[f81,f38])).
% 0.17/0.52  % (8339)Refutation not found, incomplete strategy% (8339)------------------------------
% 0.17/0.52  % (8339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.52  % (8339)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.52  
% 0.17/0.52  % (8339)Memory used [KB]: 1663
% 0.17/0.52  % (8339)Time elapsed: 0.131 s
% 0.17/0.52  % (8339)------------------------------
% 0.17/0.52  % (8339)------------------------------
% 0.17/0.52  fof(f38,plain,(
% 0.17/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.17/0.52    inference(cnf_transformation,[],[f25])).
% 0.17/0.52  fof(f25,plain,(
% 0.17/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.52    inference(flattening,[],[f24])).
% 0.17/0.52  fof(f24,plain,(
% 0.17/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.52    inference(nnf_transformation,[],[f3])).
% 0.17/0.52  fof(f3,axiom,(
% 0.17/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.17/0.52  fof(f81,plain,(
% 0.17/0.52    r1_tarski(k1_tarski(sK1),k1_xboole_0)),
% 0.17/0.52    inference(superposition,[],[f45,f77])).
% 0.17/0.52  fof(f77,plain,(
% 0.17/0.52    k1_xboole_0 = k2_tarski(sK1,sK2)),
% 0.17/0.52    inference(subsumption_resolution,[],[f74,f35])).
% 0.17/0.52  fof(f35,plain,(
% 0.17/0.52    sK1 != sK3),
% 0.17/0.52    inference(cnf_transformation,[],[f23])).
% 0.17/0.52  fof(f23,plain,(
% 0.17/0.52    sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3))),
% 0.17/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f22])).
% 0.17/0.52  fof(f22,plain,(
% 0.17/0.52    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 0.17/0.52    introduced(choice_axiom,[])).
% 0.17/0.52  fof(f17,plain,(
% 0.17/0.52    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.17/0.52    inference(ennf_transformation,[],[f16])).
% 0.17/0.52  % (8351)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.17/0.52  fof(f16,negated_conjecture,(
% 0.17/0.52    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.17/0.52    inference(negated_conjecture,[],[f15])).
% 0.17/0.52  fof(f15,conjecture,(
% 0.17/0.52    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.17/0.52  fof(f74,plain,(
% 0.17/0.52    k1_xboole_0 = k2_tarski(sK1,sK2) | sK1 = sK3),
% 0.17/0.52    inference(resolution,[],[f71,f39])).
% 0.17/0.52  fof(f71,plain,(
% 0.17/0.52    r1_tarski(k1_tarski(sK1),k1_tarski(sK3)) | k1_xboole_0 = k2_tarski(sK1,sK2)),
% 0.17/0.52    inference(superposition,[],[f45,f68])).
% 0.17/0.52  fof(f68,plain,(
% 0.17/0.52    k2_tarski(sK1,sK2) = k1_tarski(sK3) | k1_xboole_0 = k2_tarski(sK1,sK2)),
% 0.17/0.52    inference(resolution,[],[f34,f42])).
% 0.17/0.52  fof(f42,plain,(
% 0.17/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.17/0.52    inference(cnf_transformation,[],[f27])).
% 0.17/0.52  fof(f34,plain,(
% 0.17/0.52    r1_tarski(k2_tarski(sK1,sK2),k1_tarski(sK3))),
% 0.17/0.52    inference(cnf_transformation,[],[f23])).
% 0.17/0.52  fof(f45,plain,(
% 0.17/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.17/0.52    inference(cnf_transformation,[],[f13])).
% 0.17/0.52  fof(f13,axiom,(
% 0.17/0.52    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.17/0.52  fof(f39,plain,(
% 0.17/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.17/0.52    inference(cnf_transformation,[],[f18])).
% 0.17/0.52  fof(f18,plain,(
% 0.17/0.52    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.17/0.52    inference(ennf_transformation,[],[f14])).
% 0.17/0.52  fof(f14,axiom,(
% 0.17/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.17/0.52  fof(f127,plain,(
% 0.17/0.52    ( ! [X0] : (sK1 != X0) )),
% 0.17/0.52    inference(superposition,[],[f35,f115])).
% 0.17/0.52  fof(f115,plain,(
% 0.17/0.52    ( ! [X0,X1] : (X0 = X1) )),
% 0.17/0.52    inference(subsumption_resolution,[],[f101,f94])).
% 0.17/0.52  fof(f94,plain,(
% 0.17/0.52    ( ! [X0] : (r1_tarski(sK1,X0)) )),
% 0.17/0.52    inference(backward_demodulation,[],[f46,f92])).
% 0.17/0.52  fof(f46,plain,(
% 0.17/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.17/0.52    inference(cnf_transformation,[],[f6])).
% 0.17/0.52  fof(f6,axiom,(
% 0.17/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.17/0.52  fof(f101,plain,(
% 0.17/0.52    ( ! [X0,X1] : (~r1_tarski(sK1,k1_tarski(X1)) | X0 = X1) )),
% 0.17/0.52    inference(backward_demodulation,[],[f39,f92])).
% 0.17/0.52  % SZS output end Proof for theBenchmark
% 0.17/0.52  % (8352)------------------------------
% 0.17/0.52  % (8352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.52  % (8352)Termination reason: Refutation
% 0.17/0.52  
% 0.17/0.52  % (8352)Memory used [KB]: 1791
% 0.17/0.52  % (8352)Time elapsed: 0.075 s
% 0.17/0.52  % (8352)------------------------------
% 0.17/0.52  % (8352)------------------------------
% 0.17/0.52  % (8344)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.17/0.52  % (8337)Success in time 0.189 s
%------------------------------------------------------------------------------
