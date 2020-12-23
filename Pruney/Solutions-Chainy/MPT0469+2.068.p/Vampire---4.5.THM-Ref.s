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
% DateTime   : Thu Dec  3 12:47:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 142 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  117 ( 313 expanded)
%              Number of equality atoms :   55 ( 137 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(global_subsumption,[],[f15,f157,f168])).

fof(f168,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f126,f157])).

fof(f126,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f125,f16])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f125,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k2_relat_1(k1_xboole_0))
    | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(k4_tarski(sK0(k1_xboole_0),sK3(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK3(k1_xboole_0,sK0(k1_xboole_0))))) ),
    inference(resolution,[],[f122,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f30,f17])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f122,plain,
    ( r2_hidden(k4_tarski(sK0(k1_xboole_0),sK3(k1_xboole_0,sK0(k1_xboole_0))),k1_xboole_0)
    | k2_relat_1(k1_xboole_0) = k1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f121,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f121,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k2_relat_1(k1_xboole_0) = k1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k2_relat_1(k1_xboole_0) = k1_relat_1(k2_relat_1(k1_xboole_0))
    | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f110,f37])).

fof(f37,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f18,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f18,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f110,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))
      | k2_relat_1(X3) = k1_relat_1(k2_relat_1(k1_xboole_0))
      | r2_hidden(sK0(X3),k1_relat_1(X3)) ) ),
    inference(resolution,[],[f107,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(sK0(X1),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f107,plain,(
    ! [X3] :
      ( r2_hidden(sK2(k2_relat_1(k1_xboole_0),X3),X3)
      | k1_relat_1(k2_relat_1(k1_xboole_0)) = X3
      | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f70,f37])).

fof(f70,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | k1_relat_1(k2_relat_1(X4)) = X5
      | r2_hidden(sK2(k2_relat_1(X4),X5),X5)
      | r2_hidden(sK0(X4),k1_relat_1(X4)) ) ),
    inference(resolution,[],[f24,f19])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f157,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f156,f16])).

fof(f156,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(k4_tarski(sK0(k1_xboole_0),sK3(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK3(k1_xboole_0,sK0(k1_xboole_0))))) ),
    inference(resolution,[],[f151,f31])).

fof(f151,plain,
    ( r2_hidden(k4_tarski(sK0(k1_xboole_0),sK3(k1_xboole_0,sK0(k1_xboole_0))),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f149,f33])).

fof(f149,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f143,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k2_relat_1(k1_xboole_0),X0),k2_relat_1(k1_xboole_0))
      | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))
      | k2_relat_1(k1_xboole_0) = X0 ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( k2_relat_1(k1_xboole_0) = X0
      | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(sK1(k2_relat_1(k1_xboole_0),X0),k2_relat_1(k1_xboole_0))
      | k2_relat_1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f89,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f89,plain,(
    ! [X3] :
      ( r2_hidden(sK1(k2_relat_1(k1_xboole_0),X3),X3)
      | k2_relat_1(k1_xboole_0) = X3
      | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f49,f37])).

fof(f49,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(X2) = X3
      | r2_hidden(sK1(k2_relat_1(X2),X3),X3)
      | r2_hidden(sK0(X2),k1_relat_1(X2)) ) ),
    inference(resolution,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f143,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(trivial_inequality_removal,[],[f142])).

fof(f142,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = X0
      | r2_hidden(sK1(X0,k1_xboole_0),X0) ) ),
    inference(superposition,[],[f45,f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k2_tarski(sK1(X0,X1),sK1(X0,X1))) != X1
      | X0 = X1
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(resolution,[],[f20,f31])).

fof(f15,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:18:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.50  % (24825)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (24809)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (24825)Refutation not found, incomplete strategy% (24825)------------------------------
% 0.20/0.50  % (24825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24808)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (24825)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  % (24812)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  
% 0.20/0.50  % (24825)Memory used [KB]: 10618
% 0.20/0.50  % (24825)Time elapsed: 0.027 s
% 0.20/0.50  % (24825)------------------------------
% 0.20/0.50  % (24825)------------------------------
% 0.20/0.50  % (24806)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (24831)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (24808)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(global_subsumption,[],[f15,f157,f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(backward_demodulation,[],[f126,f157])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    k2_relat_1(k1_xboole_0) = k1_relat_1(k2_relat_1(k1_xboole_0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f125,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    k2_relat_1(k1_xboole_0) = k1_relat_1(k2_relat_1(k1_xboole_0)) | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(k4_tarski(sK0(k1_xboole_0),sK3(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK3(k1_xboole_0,sK0(k1_xboole_0)))))),
% 0.20/0.51    inference(resolution,[],[f122,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f30,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK0(k1_xboole_0),sK3(k1_xboole_0,sK0(k1_xboole_0))),k1_xboole_0) | k2_relat_1(k1_xboole_0) = k1_relat_1(k2_relat_1(k1_xboole_0))),
% 0.20/0.51    inference(resolution,[],[f121,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) | k2_relat_1(k1_xboole_0) = k1_relat_1(k2_relat_1(k1_xboole_0))),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f120])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) | k2_relat_1(k1_xboole_0) = k1_relat_1(k2_relat_1(k1_xboole_0)) | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 0.20/0.51    inference(resolution,[],[f110,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    v1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(superposition,[],[f18,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ( ! [X3] : (~v1_relat_1(X3) | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) | k2_relat_1(X3) = k1_relat_1(k2_relat_1(k1_xboole_0)) | r2_hidden(sK0(X3),k1_relat_1(X3))) )),
% 0.20/0.51    inference(resolution,[],[f107,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | r2_hidden(sK0(X1),k1_relat_1(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(sK2(k2_relat_1(k1_xboole_0),X3),X3) | k1_relat_1(k2_relat_1(k1_xboole_0)) = X3 | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))) )),
% 0.20/0.51    inference(resolution,[],[f70,f37])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X4,X5] : (~v1_relat_1(X4) | k1_relat_1(k2_relat_1(X4)) = X5 | r2_hidden(sK2(k2_relat_1(X4),X5),X5) | r2_hidden(sK0(X4),k1_relat_1(X4))) )),
% 0.20/0.51    inference(resolution,[],[f24,f19])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f156,f16])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(k4_tarski(sK0(k1_xboole_0),sK3(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK3(k1_xboole_0,sK0(k1_xboole_0)))))),
% 0.20/0.51    inference(resolution,[],[f151,f31])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK0(k1_xboole_0),sK3(k1_xboole_0,sK0(k1_xboole_0))),k1_xboole_0) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(resolution,[],[f149,f33])).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f145])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(resolution,[],[f143,f94])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK1(k2_relat_1(k1_xboole_0),X0),k2_relat_1(k1_xboole_0)) | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) | k2_relat_1(k1_xboole_0) = X0) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(k1_xboole_0) = X0 | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~r2_hidden(sK1(k2_relat_1(k1_xboole_0),X0),k2_relat_1(k1_xboole_0)) | k2_relat_1(k1_xboole_0) = X0) )),
% 0.20/0.51    inference(resolution,[],[f89,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(sK1(k2_relat_1(k1_xboole_0),X3),X3) | k2_relat_1(k1_xboole_0) = X3 | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))) )),
% 0.20/0.51    inference(resolution,[],[f49,f37])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~v1_relat_1(X2) | k2_relat_1(X2) = X3 | r2_hidden(sK1(k2_relat_1(X2),X3),X3) | r2_hidden(sK0(X2),k1_relat_1(X2))) )),
% 0.20/0.51    inference(resolution,[],[f20,f19])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f143,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f142])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X0 | r2_hidden(sK1(X0,k1_xboole_0),X0)) )),
% 0.20/0.51    inference(superposition,[],[f45,f16])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X1,k2_tarski(sK1(X0,X1),sK1(X0,X1))) != X1 | X0 = X1 | r2_hidden(sK1(X0,X1),X0)) )),
% 0.20/0.51    inference(resolution,[],[f20,f31])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (24808)------------------------------
% 0.20/0.51  % (24808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24808)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (24808)Memory used [KB]: 6396
% 0.20/0.51  % (24808)Time elapsed: 0.037 s
% 0.20/0.51  % (24808)------------------------------
% 0.20/0.51  % (24808)------------------------------
% 0.20/0.51  % (24798)Success in time 0.149 s
%------------------------------------------------------------------------------
