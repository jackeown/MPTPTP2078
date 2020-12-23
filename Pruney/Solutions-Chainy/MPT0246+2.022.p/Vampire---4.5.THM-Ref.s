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
% DateTime   : Thu Dec  3 12:37:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 189 expanded)
%              Number of leaves         :    7 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 326 expanded)
%              Number of equality atoms :   40 ( 257 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f42,f59,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f33])).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

% (19475)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f59,plain,(
    ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f50,f52])).

fof(f52,plain,(
    sK1 = sK2(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f49,f16])).

fof(f16,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f49,plain,(
    r2_hidden(sK2(sK0,k2_enumset1(sK1,sK1,sK1,sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f48,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f48,plain,(
    ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f18,f34,f34,f34,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f24,f33,f33,f32,f32])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f34,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f17,f33])).

fof(f17,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ~ r2_hidden(sK2(sK0,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f48,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) != X0
      | r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f28,f32,f32])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:32:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (19483)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (19487)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (19479)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (19479)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f42,f59,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f29,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f30,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  % (19475)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(backward_demodulation,[],[f50,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    sK1 = sK2(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f49,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    r2_hidden(sK2(sK0,k2_enumset1(sK1,sK1,sK1,sK1)),sK0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f48,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f18,f34,f34,f34,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X1,X1,X1,X1) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X2) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f24,f33,f33,f32,f32])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f17,f33])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    sK0 != k1_tarski(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ~r2_hidden(sK2(sK0,k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f48,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2))) )),
% 0.21/0.52    inference(equality_resolution,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) != X0 | r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f28,f32,f32])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (19479)------------------------------
% 0.21/0.52  % (19479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19479)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (19479)Memory used [KB]: 6268
% 0.21/0.52  % (19479)Time elapsed: 0.101 s
% 0.21/0.52  % (19479)------------------------------
% 0.21/0.52  % (19479)------------------------------
% 0.21/0.52  % (19474)Success in time 0.154 s
%------------------------------------------------------------------------------
