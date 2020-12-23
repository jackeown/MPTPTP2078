%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:26 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 163 expanded)
%              Number of leaves         :   11 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 269 expanded)
%              Number of equality atoms :   47 ( 175 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f717,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f295,f380,f392,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f392,plain,(
    ! [X2] : ~ r2_hidden(X2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(global_subsumption,[],[f391,f390])).

fof(f390,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ) ),
    inference(duplicate_literal_removal,[],[f388])).

fof(f388,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ) ),
    inference(superposition,[],[f48,f83])).

fof(f83,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(backward_demodulation,[],[f64,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f64,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f23,f63,f60,f63,f63])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f391,plain,(
    ! [X1] :
      ( r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ) ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,(
    ! [X1] :
      ( r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ) ),
    inference(superposition,[],[f49,f83])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f380,plain,(
    ! [X0] : ~ r2_hidden(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(unit_resulting_resolution,[],[f357,f188])).

fof(f188,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,k3_xboole_0(X8,X7))
      | r2_hidden(X6,X8) ) ),
    inference(global_subsumption,[],[f41,f179])).

fof(f179,plain,(
    ! [X6,X8,X7] :
      ( sP4(X6,X7,X8)
      | r2_hidden(X6,X8)
      | ~ r2_hidden(X6,k3_xboole_0(X8,X7)) ) ),
    inference(resolution,[],[f76,f49])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f31])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f357,plain,(
    ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f346,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | sP6(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP6(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f61])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP6(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f346,plain,(
    ~ sP6(sK1,sK0,sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f24,f24,f24,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f24,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f295,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f80,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | ~ sP6(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f56,f61])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    ! [X4,X0,X1] : sP6(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP6(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (13063)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (13054)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (13056)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (13061)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (13051)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (13075)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (13053)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (13052)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (13066)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (13070)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (13050)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (13075)Refutation not found, incomplete strategy% (13075)------------------------------
% 0.21/0.54  % (13075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13075)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13075)Memory used [KB]: 1663
% 0.21/0.54  % (13075)Time elapsed: 0.084 s
% 0.21/0.54  % (13075)------------------------------
% 0.21/0.54  % (13075)------------------------------
% 0.21/0.54  % (13081)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (13074)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (13055)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (13065)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (13060)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (13077)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (13059)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (13078)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (13080)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (13071)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (13073)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (13061)Refutation not found, incomplete strategy% (13061)------------------------------
% 0.21/0.55  % (13061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13061)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13061)Memory used [KB]: 10618
% 0.21/0.55  % (13061)Time elapsed: 0.136 s
% 0.21/0.55  % (13061)------------------------------
% 0.21/0.55  % (13061)------------------------------
% 0.21/0.55  % (13073)Refutation not found, incomplete strategy% (13073)------------------------------
% 0.21/0.55  % (13073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13073)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13073)Memory used [KB]: 1663
% 0.21/0.55  % (13073)Time elapsed: 0.132 s
% 0.21/0.55  % (13073)------------------------------
% 0.21/0.55  % (13073)------------------------------
% 0.21/0.55  % (13072)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (13068)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (13072)Refutation not found, incomplete strategy% (13072)------------------------------
% 0.21/0.55  % (13072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13072)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13072)Memory used [KB]: 10746
% 0.21/0.55  % (13072)Time elapsed: 0.146 s
% 0.21/0.55  % (13072)------------------------------
% 0.21/0.55  % (13072)------------------------------
% 0.21/0.55  % (13064)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (13076)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (13062)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (13062)Refutation not found, incomplete strategy% (13062)------------------------------
% 0.21/0.56  % (13062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13062)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (13062)Memory used [KB]: 10618
% 0.21/0.56  % (13062)Time elapsed: 0.148 s
% 0.21/0.56  % (13062)------------------------------
% 0.21/0.56  % (13062)------------------------------
% 1.58/0.56  % (13067)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.58/0.58  % (13057)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.58/0.58  % (13079)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.73/0.59  % (13076)Refutation found. Thanks to Tanya!
% 1.73/0.59  % SZS status Theorem for theBenchmark
% 1.73/0.61  % SZS output start Proof for theBenchmark
% 1.73/0.61  fof(f717,plain,(
% 1.73/0.61    $false),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f295,f380,f392,f50])).
% 1.73/0.61  fof(f50,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f21])).
% 1.73/0.61  fof(f21,plain,(
% 1.73/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.73/0.61    inference(ennf_transformation,[],[f4])).
% 1.73/0.61  fof(f4,axiom,(
% 1.73/0.61    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.73/0.61  fof(f392,plain,(
% 1.73/0.61    ( ! [X2] : (~r2_hidden(X2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))))) )),
% 1.73/0.61    inference(global_subsumption,[],[f391,f390])).
% 1.73/0.61  fof(f390,plain,(
% 1.73/0.61    ( ! [X2] : (~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))))) )),
% 1.73/0.61    inference(duplicate_literal_removal,[],[f388])).
% 1.73/0.61  fof(f388,plain,(
% 1.73/0.61    ( ! [X2] : (~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))))) )),
% 1.73/0.61    inference(superposition,[],[f48,f83])).
% 1.73/0.61  fof(f83,plain,(
% 1.73/0.61    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 1.73/0.61    inference(backward_demodulation,[],[f64,f28])).
% 1.73/0.61  fof(f28,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f1])).
% 1.73/0.61  fof(f1,axiom,(
% 1.73/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.73/0.61  fof(f64,plain,(
% 1.73/0.61    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 1.73/0.61    inference(definition_unfolding,[],[f23,f63,f60,f63,f63])).
% 1.73/0.61  fof(f60,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.73/0.61    inference(definition_unfolding,[],[f30,f31])).
% 1.73/0.61  fof(f31,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.73/0.61    inference(cnf_transformation,[],[f6])).
% 1.73/0.61  fof(f6,axiom,(
% 1.73/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.73/0.61  fof(f30,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.73/0.61    inference(cnf_transformation,[],[f10])).
% 1.73/0.61  fof(f10,axiom,(
% 1.73/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.73/0.61  fof(f63,plain,(
% 1.73/0.61    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.73/0.61    inference(definition_unfolding,[],[f27,f62])).
% 1.73/0.61  fof(f62,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.73/0.61    inference(definition_unfolding,[],[f29,f61])).
% 1.73/0.61  fof(f61,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.73/0.61    inference(definition_unfolding,[],[f39,f51])).
% 1.73/0.61  fof(f51,plain,(
% 1.73/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f15])).
% 1.73/0.61  fof(f15,axiom,(
% 1.73/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.73/0.61  fof(f39,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f14])).
% 1.73/0.61  fof(f14,axiom,(
% 1.73/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.73/0.61  fof(f29,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f13])).
% 1.73/0.61  fof(f13,axiom,(
% 1.73/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.73/0.61  fof(f27,plain,(
% 1.73/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f12])).
% 1.73/0.61  fof(f12,axiom,(
% 1.73/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.73/0.61  fof(f23,plain,(
% 1.73/0.61    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.73/0.61    inference(cnf_transformation,[],[f18])).
% 1.73/0.61  fof(f18,plain,(
% 1.73/0.61    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.73/0.61    inference(ennf_transformation,[],[f17])).
% 1.73/0.61  fof(f17,negated_conjecture,(
% 1.73/0.61    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.73/0.61    inference(negated_conjecture,[],[f16])).
% 1.73/0.61  fof(f16,conjecture,(
% 1.73/0.61    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 1.73/0.61  fof(f48,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f21])).
% 1.73/0.61  fof(f391,plain,(
% 1.73/0.61    ( ! [X1] : (r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))))) )),
% 1.73/0.61    inference(duplicate_literal_removal,[],[f387])).
% 1.73/0.61  fof(f387,plain,(
% 1.73/0.61    ( ! [X1] : (r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))))) )),
% 1.73/0.61    inference(superposition,[],[f49,f83])).
% 1.73/0.61  fof(f49,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f21])).
% 1.73/0.61  fof(f380,plain,(
% 1.73/0.61    ( ! [X0] : (~r2_hidden(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0))) )),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f357,f188])).
% 1.73/0.61  fof(f188,plain,(
% 1.73/0.61    ( ! [X6,X8,X7] : (~r2_hidden(X6,k3_xboole_0(X8,X7)) | r2_hidden(X6,X8)) )),
% 1.73/0.61    inference(global_subsumption,[],[f41,f179])).
% 1.73/0.61  fof(f179,plain,(
% 1.73/0.61    ( ! [X6,X8,X7] : (sP4(X6,X7,X8) | r2_hidden(X6,X8) | ~r2_hidden(X6,k3_xboole_0(X8,X7))) )),
% 1.73/0.61    inference(resolution,[],[f76,f49])).
% 1.73/0.61  fof(f76,plain,(
% 1.73/0.61    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | sP4(X3,X1,X0)) )),
% 1.73/0.61    inference(equality_resolution,[],[f68])).
% 1.73/0.61  fof(f68,plain,(
% 1.73/0.61    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.73/0.61    inference(definition_unfolding,[],[f44,f31])).
% 1.73/0.61  fof(f44,plain,(
% 1.73/0.61    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.73/0.61    inference(cnf_transformation,[],[f3])).
% 1.73/0.61  fof(f3,axiom,(
% 1.73/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.73/0.61  fof(f41,plain,(
% 1.73/0.61    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f3])).
% 1.73/0.61  fof(f357,plain,(
% 1.73/0.61    ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f346,f78])).
% 1.73/0.61  fof(f78,plain,(
% 1.73/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | sP6(X4,X2,X1,X0)) )),
% 1.73/0.61    inference(equality_resolution,[],[f72])).
% 1.73/0.61  fof(f72,plain,(
% 1.73/0.61    ( ! [X4,X2,X0,X3,X1] : (sP6(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.73/0.61    inference(definition_unfolding,[],[f57,f61])).
% 1.73/0.61  fof(f57,plain,(
% 1.73/0.61    ( ! [X4,X2,X0,X3,X1] : (sP6(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.73/0.61    inference(cnf_transformation,[],[f22])).
% 1.73/0.61  fof(f22,plain,(
% 1.73/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.73/0.61    inference(ennf_transformation,[],[f11])).
% 1.73/0.61  fof(f11,axiom,(
% 1.73/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.73/0.61  fof(f346,plain,(
% 1.73/0.61    ~sP6(sK1,sK0,sK0,sK0)),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f24,f24,f24,f55])).
% 1.73/0.61  fof(f55,plain,(
% 1.73/0.61    ( ! [X4,X2,X0,X1] : (~sP6(X4,X2,X1,X0) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.73/0.61    inference(cnf_transformation,[],[f22])).
% 1.73/0.61  fof(f24,plain,(
% 1.73/0.61    sK0 != sK1),
% 1.73/0.61    inference(cnf_transformation,[],[f18])).
% 1.73/0.61  fof(f295,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0))) )),
% 1.73/0.61    inference(unit_resulting_resolution,[],[f80,f79])).
% 1.73/0.61  fof(f79,plain,(
% 1.73/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | ~sP6(X4,X2,X1,X0)) )),
% 1.73/0.61    inference(equality_resolution,[],[f73])).
% 1.73/0.61  fof(f73,plain,(
% 1.73/0.61    ( ! [X4,X2,X0,X3,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.73/0.61    inference(definition_unfolding,[],[f56,f61])).
% 1.73/0.61  fof(f56,plain,(
% 1.73/0.61    ( ! [X4,X2,X0,X3,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.73/0.61    inference(cnf_transformation,[],[f22])).
% 1.73/0.61  fof(f80,plain,(
% 1.73/0.61    ( ! [X4,X0,X1] : (sP6(X4,X4,X1,X0)) )),
% 1.73/0.61    inference(equality_resolution,[],[f54])).
% 1.73/0.61  fof(f54,plain,(
% 1.73/0.61    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP6(X4,X2,X1,X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f22])).
% 1.73/0.61  % SZS output end Proof for theBenchmark
% 1.73/0.61  % (13076)------------------------------
% 1.73/0.61  % (13076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (13076)Termination reason: Refutation
% 1.73/0.61  
% 1.73/0.61  % (13076)Memory used [KB]: 6780
% 1.73/0.61  % (13076)Time elapsed: 0.181 s
% 1.73/0.61  % (13076)------------------------------
% 1.73/0.61  % (13076)------------------------------
% 1.73/0.61  % (13047)Success in time 0.245 s
%------------------------------------------------------------------------------
