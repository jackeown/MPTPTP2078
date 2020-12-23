%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  73 expanded)
%              Number of leaves         :    4 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :   45 ( 187 expanded)
%              Number of equality atoms :   25 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (31815)Termination reason: Refutation not found, incomplete strategy
fof(f408,plain,(
    $false ),
    inference(subsumption_resolution,[],[f407,f8])).

fof(f8,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

% (31815)Memory used [KB]: 6140
fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f407,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f378,f389])).

fof(f389,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X9) = k4_xboole_0(k4_xboole_0(X10,X9),X9) ),
    inference(superposition,[],[f376,f376])).

fof(f376,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = X6 ),
    inference(duplicate_literal_removal,[],[f364])).

fof(f364,plain,(
    ! [X6,X7] :
      ( k4_xboole_0(X6,k4_xboole_0(X7,X6)) = X6
      | k4_xboole_0(X6,k4_xboole_0(X7,X6)) = X6 ) ),
    inference(resolution,[],[f183,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f11])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f183,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK2(X6,k4_xboole_0(X7,X8),X6),X8)
      | k4_xboole_0(X6,k4_xboole_0(X7,X8)) = X6 ) ),
    inference(resolution,[],[f179,f18])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f179,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK2(X5,X6,X5),X6)
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(subsumption_resolution,[],[f177,f26])).

fof(f177,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK2(X5,X6,X5),X6)
      | ~ r2_hidden(sK2(X5,X6,X5),X5)
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK2(X5,X6,X5),X6)
      | ~ r2_hidden(sK2(X5,X6,X5),X5)
      | k4_xboole_0(X5,X6) = X5
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(resolution,[],[f10,f26])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f378,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)) ),
    inference(backward_demodulation,[],[f16,f376])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)) ),
    inference(definition_unfolding,[],[f7,f9])).

fof(f9,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f7,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:35:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (31796)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (31804)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (31806)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (31803)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (31798)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (31798)Refutation not found, incomplete strategy% (31798)------------------------------
% 0.22/0.53  % (31798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31815)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (31815)Refutation not found, incomplete strategy% (31815)------------------------------
% 0.22/0.54  % (31815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31796)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  % (31815)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  fof(f408,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f407,f8])).
% 0.22/0.54  
% 0.22/0.54  fof(f8,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  % (31815)Memory used [KB]: 6140
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.54  fof(f407,plain,(
% 0.22/0.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.54    inference(backward_demodulation,[],[f378,f389])).
% 0.22/0.54  fof(f389,plain,(
% 0.22/0.54    ( ! [X10,X9] : (k4_xboole_0(X10,X9) = k4_xboole_0(k4_xboole_0(X10,X9),X9)) )),
% 0.22/0.54    inference(superposition,[],[f376,f376])).
% 0.22/0.54  fof(f376,plain,(
% 0.22/0.54    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X7,X6)) = X6) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f364])).
% 0.22/0.54  fof(f364,plain,(
% 0.22/0.54    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X7,X6)) = X6 | k4_xboole_0(X6,k4_xboole_0(X7,X6)) = X6) )),
% 0.22/0.54    inference(resolution,[],[f183,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.54    inference(factoring,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    ( ! [X6,X8,X7] : (~r2_hidden(sK2(X6,k4_xboole_0(X7,X8),X6),X8) | k4_xboole_0(X6,k4_xboole_0(X7,X8)) = X6) )),
% 0.22/0.54    inference(resolution,[],[f179,f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    ( ! [X6,X5] : (r2_hidden(sK2(X5,X6,X5),X6) | k4_xboole_0(X5,X6) = X5) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f177,f26])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    ( ! [X6,X5] : (r2_hidden(sK2(X5,X6,X5),X6) | ~r2_hidden(sK2(X5,X6,X5),X5) | k4_xboole_0(X5,X6) = X5) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f174])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    ( ! [X6,X5] : (r2_hidden(sK2(X5,X6,X5),X6) | ~r2_hidden(sK2(X5,X6,X5),X5) | k4_xboole_0(X5,X6) = X5 | k4_xboole_0(X5,X6) = X5) )),
% 0.22/0.54    inference(resolution,[],[f10,f26])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f378,plain,(
% 0.22/0.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0))),
% 0.22/0.54    inference(backward_demodulation,[],[f16,f376])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0))),
% 0.22/0.54    inference(definition_unfolding,[],[f7,f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.54  fof(f7,plain,(
% 0.22/0.54    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,plain,(
% 0.22/0.54    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.54    inference(negated_conjecture,[],[f4])).
% 0.22/0.54  fof(f4,conjecture,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (31796)------------------------------
% 0.22/0.54  % (31796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31796)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (31796)Memory used [KB]: 6396
% 0.22/0.54  % (31796)Time elapsed: 0.112 s
% 0.22/0.54  % (31796)------------------------------
% 0.22/0.54  % (31796)------------------------------
% 0.22/0.54  % (31815)Time elapsed: 0.109 s
% 0.22/0.54  % (31815)------------------------------
% 0.22/0.54  % (31815)------------------------------
% 0.22/0.54  % (31798)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31798)Memory used [KB]: 10618
% 0.22/0.54  % (31798)Time elapsed: 0.106 s
% 0.22/0.54  % (31798)------------------------------
% 0.22/0.54  % (31798)------------------------------
% 0.22/0.54  % (31814)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (31789)Success in time 0.173 s
%------------------------------------------------------------------------------
