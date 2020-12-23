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
% DateTime   : Thu Dec  3 12:38:24 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 149 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :   93 ( 219 expanded)
%              Number of equality atoms :   37 ( 143 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f61,f111,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | ~ sP4(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f111,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f23,f105,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f105,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f61,f102])).

fof(f102,plain,(
    ! [X6] :
      ( ~ sP4(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1)
      | r1_tarski(X6,sK1) ) ),
    inference(resolution,[],[f60,f86])).

fof(f86,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
      | r1_tarski(X2,sK1) ) ),
    inference(resolution,[],[f75,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f64,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f64,plain,(
    r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(backward_demodulation,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f25,f50,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f49])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f53,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f22,f52,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f50])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f50])).

fof(f27,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f22,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f23,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X4,X0,X1] : sP4(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP4(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:09:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (785186816)
% 0.22/0.37  ipcrm: permission denied for id (785219590)
% 0.22/0.38  ipcrm: permission denied for id (785252359)
% 0.22/0.38  ipcrm: permission denied for id (785317901)
% 0.22/0.39  ipcrm: permission denied for id (785416214)
% 0.22/0.40  ipcrm: permission denied for id (785448984)
% 0.22/0.41  ipcrm: permission denied for id (785580064)
% 0.22/0.41  ipcrm: permission denied for id (785612833)
% 0.22/0.42  ipcrm: permission denied for id (785678379)
% 0.22/0.42  ipcrm: permission denied for id (785711150)
% 0.22/0.43  ipcrm: permission denied for id (785743919)
% 0.22/0.44  ipcrm: permission denied for id (785809463)
% 0.22/0.46  ipcrm: permission denied for id (785940551)
% 0.22/0.46  ipcrm: permission denied for id (785973321)
% 0.22/0.46  ipcrm: permission denied for id (786006093)
% 0.22/0.47  ipcrm: permission denied for id (786038864)
% 0.22/0.47  ipcrm: permission denied for id (786071634)
% 0.22/0.48  ipcrm: permission denied for id (786104409)
% 0.22/0.49  ipcrm: permission denied for id (786137182)
% 0.22/0.50  ipcrm: permission denied for id (786169958)
% 0.22/0.52  ipcrm: permission denied for id (786333810)
% 0.22/0.53  ipcrm: permission denied for id (786399353)
% 0.22/0.54  ipcrm: permission denied for id (786464895)
% 0.40/0.72  % (16776)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.40/0.73  % (16768)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.40/0.73  % (16760)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.40/0.73  % (16761)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.40/0.74  % (16759)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.40/0.74  % (16759)Refutation not found, incomplete strategy% (16759)------------------------------
% 0.40/0.74  % (16759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.74  % (16759)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.74  
% 0.40/0.74  % (16759)Memory used [KB]: 10618
% 0.40/0.74  % (16759)Time elapsed: 0.116 s
% 0.40/0.74  % (16759)------------------------------
% 0.40/0.74  % (16759)------------------------------
% 0.40/0.74  % (16775)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.40/0.74  % (16767)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.40/0.75  % (16769)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.40/0.75  % (16777)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.47/0.75  % (16775)Refutation found. Thanks to Tanya!
% 0.47/0.75  % SZS status Theorem for theBenchmark
% 0.47/0.75  % SZS output start Proof for theBenchmark
% 0.47/0.75  fof(f116,plain,(
% 0.47/0.75    $false),
% 0.47/0.75    inference(unit_resulting_resolution,[],[f61,f111,f60])).
% 0.47/0.75  fof(f60,plain,(
% 0.47/0.75    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | ~sP4(X4,X2,X1,X0)) )),
% 0.47/0.75    inference(equality_resolution,[],[f58])).
% 0.47/0.75  fof(f58,plain,(
% 0.47/0.75    ( ! [X4,X2,X0,X3,X1] : (~sP4(X4,X2,X1,X0) | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.47/0.75    inference(definition_unfolding,[],[f39,f49])).
% 0.47/0.75  fof(f49,plain,(
% 0.47/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.47/0.75    inference(definition_unfolding,[],[f32,f48])).
% 0.47/0.75  fof(f48,plain,(
% 0.47/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.47/0.75    inference(definition_unfolding,[],[f34,f47])).
% 0.47/0.75  fof(f47,plain,(
% 0.47/0.75    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.47/0.75    inference(definition_unfolding,[],[f43,f46])).
% 0.47/0.75  fof(f46,plain,(
% 0.47/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.47/0.75    inference(definition_unfolding,[],[f44,f45])).
% 0.47/0.75  fof(f45,plain,(
% 0.47/0.75    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.47/0.75    inference(cnf_transformation,[],[f11])).
% 0.47/0.75  fof(f11,axiom,(
% 0.47/0.75    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.47/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.47/0.75  fof(f44,plain,(
% 0.47/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.47/0.75    inference(cnf_transformation,[],[f10])).
% 0.47/0.75  fof(f10,axiom,(
% 0.47/0.75    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.47/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.47/0.75  fof(f43,plain,(
% 0.47/0.75    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.47/0.75    inference(cnf_transformation,[],[f9])).
% 0.47/0.75  fof(f9,axiom,(
% 0.47/0.75    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.47/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.47/0.75  fof(f34,plain,(
% 0.47/0.75    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.47/0.75    inference(cnf_transformation,[],[f8])).
% 0.47/0.75  fof(f8,axiom,(
% 0.47/0.75    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.47/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.47/0.75  fof(f32,plain,(
% 0.47/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.47/0.75    inference(cnf_transformation,[],[f7])).
% 0.47/0.75  fof(f7,axiom,(
% 0.47/0.75    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.47/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.47/0.75  fof(f39,plain,(
% 0.47/0.75    ( ! [X4,X2,X0,X3,X1] : (~sP4(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.47/0.75    inference(cnf_transformation,[],[f21])).
% 0.47/0.75  fof(f21,plain,(
% 0.47/0.75    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.47/0.75    inference(ennf_transformation,[],[f4])).
% 0.47/0.75  fof(f4,axiom,(
% 0.47/0.75    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.47/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.47/0.75  fof(f111,plain,(
% 0.47/0.75    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.47/0.75    inference(unit_resulting_resolution,[],[f23,f105,f29])).
% 0.47/0.75  fof(f29,plain,(
% 0.47/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.47/0.75    inference(cnf_transformation,[],[f18])).
% 0.47/0.75  fof(f18,plain,(
% 0.47/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.47/0.75    inference(ennf_transformation,[],[f1])).
% 0.47/0.75  fof(f1,axiom,(
% 0.47/0.75    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.47/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.47/0.75  fof(f105,plain,(
% 0.47/0.75    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.47/0.75    inference(unit_resulting_resolution,[],[f61,f102])).
% 0.47/0.75  fof(f102,plain,(
% 0.47/0.75    ( ! [X6] : (~sP4(X6,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1) | r1_tarski(X6,sK1)) )),
% 0.47/0.75    inference(resolution,[],[f60,f86])).
% 0.47/0.75  fof(f86,plain,(
% 0.47/0.75    ( ! [X2] : (~r2_hidden(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | r1_tarski(X2,sK1)) )),
% 0.47/0.75    inference(resolution,[],[f75,f28])).
% 0.47/0.75  fof(f28,plain,(
% 0.47/0.75    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.47/0.75    inference(cnf_transformation,[],[f17])).
% 0.47/0.75  fof(f17,plain,(
% 0.47/0.75    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.47/0.75    inference(ennf_transformation,[],[f12])).
% 0.47/0.75  fof(f12,axiom,(
% 0.47/0.75    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.47/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.47/0.75  fof(f75,plain,(
% 0.47/0.75    ( ! [X0] : (~r1_tarski(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | r1_tarski(X0,sK1)) )),
% 0.47/0.75    inference(resolution,[],[f64,f33])).
% 0.47/0.76  fof(f33,plain,(
% 0.47/0.76    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 0.47/0.76    inference(cnf_transformation,[],[f20])).
% 0.47/0.76  fof(f20,plain,(
% 0.47/0.76    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.47/0.76    inference(flattening,[],[f19])).
% 0.47/0.76  fof(f19,plain,(
% 0.47/0.76    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.47/0.76    inference(ennf_transformation,[],[f2])).
% 0.47/0.76  fof(f2,axiom,(
% 0.47/0.76    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.47/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.47/0.76  fof(f64,plain,(
% 0.47/0.76    r1_tarski(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 0.47/0.76    inference(backward_demodulation,[],[f53,f54])).
% 0.47/0.76  fof(f54,plain,(
% 0.47/0.76    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 0.47/0.76    inference(definition_unfolding,[],[f25,f50,f50])).
% 0.47/0.76  fof(f50,plain,(
% 0.47/0.76    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.47/0.76    inference(definition_unfolding,[],[f26,f49])).
% 0.47/0.76  fof(f26,plain,(
% 0.47/0.76    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.47/0.76    inference(cnf_transformation,[],[f6])).
% 0.47/0.76  fof(f6,axiom,(
% 0.47/0.76    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.47/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.47/0.76  fof(f25,plain,(
% 0.47/0.76    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.47/0.76    inference(cnf_transformation,[],[f3])).
% 0.47/0.76  fof(f3,axiom,(
% 0.47/0.76    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.47/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.47/0.76  fof(f53,plain,(
% 0.47/0.76    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 0.47/0.76    inference(definition_unfolding,[],[f22,f52,f51])).
% 0.47/0.76  fof(f51,plain,(
% 0.47/0.76    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.47/0.76    inference(definition_unfolding,[],[f24,f50])).
% 0.47/0.76  fof(f24,plain,(
% 0.47/0.76    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.47/0.76    inference(cnf_transformation,[],[f5])).
% 0.47/0.76  fof(f5,axiom,(
% 0.47/0.76    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.47/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.47/0.76  fof(f52,plain,(
% 0.47/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.47/0.76    inference(definition_unfolding,[],[f27,f50])).
% 0.47/0.76  fof(f27,plain,(
% 0.47/0.76    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.47/0.76    inference(cnf_transformation,[],[f13])).
% 0.47/0.76  fof(f13,axiom,(
% 0.47/0.76    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.47/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.47/0.76  fof(f22,plain,(
% 0.47/0.76    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.47/0.76    inference(cnf_transformation,[],[f16])).
% 0.47/0.76  fof(f16,plain,(
% 0.47/0.76    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 0.47/0.76    inference(ennf_transformation,[],[f15])).
% 0.47/0.76  fof(f15,negated_conjecture,(
% 0.47/0.76    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.47/0.76    inference(negated_conjecture,[],[f14])).
% 0.47/0.76  fof(f14,conjecture,(
% 0.47/0.76    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.47/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 0.47/0.76  fof(f23,plain,(
% 0.47/0.76    ~r2_hidden(sK0,sK1)),
% 0.47/0.76    inference(cnf_transformation,[],[f16])).
% 0.47/0.76  fof(f61,plain,(
% 0.47/0.76    ( ! [X4,X0,X1] : (sP4(X4,X4,X1,X0)) )),
% 0.47/0.76    inference(equality_resolution,[],[f37])).
% 0.47/0.76  fof(f37,plain,(
% 0.47/0.76    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP4(X4,X2,X1,X0)) )),
% 0.47/0.76    inference(cnf_transformation,[],[f21])).
% 0.47/0.76  % SZS output end Proof for theBenchmark
% 0.47/0.76  % (16775)------------------------------
% 0.47/0.76  % (16775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.47/0.76  % (16775)Termination reason: Refutation
% 0.47/0.76  
% 0.47/0.76  % (16775)Memory used [KB]: 6268
% 0.47/0.76  % (16775)Time elapsed: 0.134 s
% 0.47/0.76  % (16775)------------------------------
% 0.47/0.76  % (16775)------------------------------
% 0.47/0.76  % (16592)Success in time 0.394 s
%------------------------------------------------------------------------------
