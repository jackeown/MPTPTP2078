%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 163 expanded)
%              Number of leaves         :    6 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :   81 ( 337 expanded)
%              Number of equality atoms :   40 ( 212 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f77,f114])).

fof(f114,plain,(
    sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1 ),
    inference(resolution,[],[f108,f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f108,plain,(
    sP5(sK0,sK1,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f104,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f24,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f104,plain,(
    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f78,f49,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f49,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(unit_resulting_resolution,[],[f38,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f23,f18])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X4,X2,X0] : sP5(X4,X2,X4,X0) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f78,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f30,f76])).

fof(f76,plain,(
    sK1 = sK2 ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,
    ( sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2 ),
    inference(resolution,[],[f70,f22])).

fof(f70,plain,(
    sP5(sK1,sK2,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f55,f35])).

fof(f55,plain,(
    r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(unit_resulting_resolution,[],[f30,f48,f15])).

fof(f48,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f37,f36])).

fof(f37,plain,(
    ! [X4,X0,X1] : sP5(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f11,f27,f28])).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f27])).

fof(f13,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f14,f18])).

fof(f14,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f11,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f77,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f29,f76])).

fof(f29,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f12,f27,f28])).

fof(f12,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:40:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (20665)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.46  % (20649)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.46  % (20654)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.46  % (20649)Refutation not found, incomplete strategy% (20649)------------------------------
% 0.21/0.46  % (20649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (20649)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (20649)Memory used [KB]: 10618
% 0.21/0.46  % (20649)Time elapsed: 0.045 s
% 0.21/0.46  % (20649)------------------------------
% 0.21/0.46  % (20649)------------------------------
% 0.21/0.46  % (20665)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f116])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.46    inference(backward_demodulation,[],[f77,f114])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    sK0 = sK1),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f113])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    sK0 = sK1 | sK0 = sK1 | sK0 = sK1),
% 0.21/0.46    inference(resolution,[],[f108,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X1] : (~sP5(X4,X2,X1,X0) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    sP5(sK0,sK1,sK1,sK1)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f104,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | sP5(X4,X2,X1,X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.46    inference(definition_unfolding,[],[f24,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f78,f49,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X1,X1,X0,X2))) )),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f38,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | ~sP5(X4,X2,X1,X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.46    inference(definition_unfolding,[],[f23,f18])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X4,X2,X0] : (sP5(X4,X2,X4,X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X1] : (X1 != X4 | sP5(X4,X2,X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.46    inference(backward_demodulation,[],[f30,f76])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    sK1 = sK2),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    sK1 = sK2 | sK1 = sK2 | sK1 = sK2),
% 0.21/0.46    inference(resolution,[],[f70,f22])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    sP5(sK1,sK2,sK2,sK2)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f55,f35])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f30,f48,f15])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))) )),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f37,f36])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (sP5(X4,X4,X1,X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP5(X4,X2,X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.21/0.47    inference(definition_unfolding,[],[f11,f27,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f13,f27])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f14,f18])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.21/0.47    inference(backward_demodulation,[],[f29,f76])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK0,sK0,sK1) != k2_enumset1(sK2,sK2,sK2,sK2)),
% 0.21/0.47    inference(definition_unfolding,[],[f12,f27,f28])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    k2_tarski(sK0,sK1) != k1_tarski(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (20665)------------------------------
% 0.21/0.47  % (20665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20665)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (20665)Memory used [KB]: 6268
% 0.21/0.47  % (20665)Time elapsed: 0.059 s
% 0.21/0.47  % (20665)------------------------------
% 0.21/0.47  % (20665)------------------------------
% 0.21/0.47  % (20640)Success in time 0.11 s
%------------------------------------------------------------------------------
