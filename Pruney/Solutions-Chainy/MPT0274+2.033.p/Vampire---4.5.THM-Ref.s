%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:25 EST 2020

% Result     : Theorem 3.55s
% Output     : Refutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 403 expanded)
%              Number of leaves         :    5 ( 112 expanded)
%              Depth                    :   16
%              Number of atoms          :  149 ( 944 expanded)
%              Number of equality atoms :   56 ( 439 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4079,plain,(
    $false ),
    inference(global_subsumption,[],[f115,f4074])).

fof(f4074,plain,(
    r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f1855,f4071])).

fof(f4071,plain,(
    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(global_subsumption,[],[f69,f116,f4070])).

fof(f4070,plain,
    ( r2_hidden(sK1,sK2)
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f4031])).

fof(f4031,plain,
    ( r2_hidden(sK1,sK2)
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f1855,f1169])).

fof(f1169,plain,(
    ! [X10,X8,X7,X9] :
      ( sK3(k2_enumset1(X7,X7,X8,X9),X10,k2_enumset1(X7,X7,X8,X9)) = X9
      | sK3(k2_enumset1(X7,X7,X8,X9),X10,k2_enumset1(X7,X7,X8,X9)) = X8
      | k2_enumset1(X7,X7,X8,X9) = k4_xboole_0(k2_enumset1(X7,X7,X8,X9),X10)
      | sK3(k2_enumset1(X7,X7,X8,X9),X10,k2_enumset1(X7,X7,X8,X9)) = X7 ) ),
    inference(resolution,[],[f428,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f428,plain,(
    ! [X10,X8,X11,X9] :
      ( sP6(sK3(k2_enumset1(X8,X8,X9,X10),X11,k2_enumset1(X8,X8,X9,X10)),X10,X9,X8)
      | k2_enumset1(X8,X8,X9,X10) = k4_xboole_0(k2_enumset1(X8,X8,X9,X10),X11) ) ),
    inference(resolution,[],[f257,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | sP6(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP6(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f26,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP6(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f257,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f75])).

fof(f75,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK3(X3,X4,X5),X5)
      | k4_xboole_0(X3,X4) = X5
      | r2_hidden(sK3(X3,X4,X5),X3) ) ),
    inference(resolution,[],[f19,f15])).

fof(f15,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( sP4(sK3(X0,X1,X2),X1,X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f116,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f69,f115,f32])).

fof(f32,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(definition_unfolding,[],[f9,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f12,f13])).

fof(f12,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f9,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f69,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f60,f41])).

fof(f41,plain,(
    ! [X4,X0,X1] : sP6(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP6(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0] :
      ( ~ sP6(X0,sK1,sK0,sK0)
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f40,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1))
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f45,f16])).

fof(f16,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X1] :
      ( sP4(X1,sK2,k2_enumset1(sK0,sK0,sK0,sK1))
      | ~ r2_hidden(X1,k2_enumset1(sK0,sK0,sK0,sK1))
      | ~ r2_hidden(sK1,sK2) ) ),
    inference(superposition,[],[f37,f30])).

fof(f30,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f11,f29,f29])).

fof(f11,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | ~ sP6(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f25,f13])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1855,plain,(
    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) ),
    inference(unit_resulting_resolution,[],[f116,f1021])).

fof(f1021,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X3,X2),X3)
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(duplicate_literal_removal,[],[f1018])).

fof(f1018,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X3,X2),X3)
      | k4_xboole_0(X2,X3) = X2
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f429,f257])).

fof(f429,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK3(X1,X2,X1),X1)
      | r2_hidden(sK3(X1,X2,X1),X2)
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(duplicate_literal_removal,[],[f424])).

fof(f424,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = X1
      | k4_xboole_0(X1,X2) = X1
      | r2_hidden(sK3(X1,X2,X1),X2)
      | ~ r2_hidden(sK3(X1,X2,X1),X1) ) ),
    inference(resolution,[],[f257,f92])).

fof(f92,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(sK3(X5,X6,X7),X7)
      | k4_xboole_0(X5,X6) = X7
      | r2_hidden(sK3(X5,X6,X7),X6)
      | ~ r2_hidden(sK3(X5,X6,X7),X5) ) ),
    inference(resolution,[],[f20,f14])).

fof(f14,plain,(
    ! [X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(sK3(X0,X1,X2),X1,X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f115,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f61,f42])).

fof(f42,plain,(
    ! [X4,X2,X0] : sP6(X4,X2,X4,X0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | sP6(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X1] :
      ( ~ sP6(X1,sK1,sK0,sK0)
      | ~ r2_hidden(sK0,sK2)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f40,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1))
      | ~ r2_hidden(sK0,sK2)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f44,f16])).

fof(f44,plain,(
    ! [X0] :
      ( sP4(X0,sK2,k2_enumset1(sK0,sK0,sK0,sK1))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1))
      | ~ r2_hidden(sK0,sK2) ) ),
    inference(superposition,[],[f37,f31])).

fof(f31,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(definition_unfolding,[],[f10,f29,f29])).

fof(f10,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (20011)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.50  % (19984)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (20003)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (19995)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (20003)Refutation not found, incomplete strategy% (20003)------------------------------
% 0.20/0.51  % (20003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19992)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (19994)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (19983)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (19984)Refutation not found, incomplete strategy% (19984)------------------------------
% 0.20/0.52  % (19984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19984)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19984)Memory used [KB]: 10618
% 0.20/0.52  % (19984)Time elapsed: 0.102 s
% 0.20/0.52  % (19984)------------------------------
% 0.20/0.52  % (19984)------------------------------
% 0.20/0.52  % (20005)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (20003)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20003)Memory used [KB]: 1663
% 0.20/0.52  % (20003)Time elapsed: 0.102 s
% 0.20/0.52  % (20003)------------------------------
% 0.20/0.52  % (20003)------------------------------
% 0.20/0.52  % (19998)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (20000)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (20010)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (19982)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (19985)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (19987)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (19997)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (20006)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (19988)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (19993)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (19990)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (19990)Refutation not found, incomplete strategy% (19990)------------------------------
% 0.20/0.53  % (19990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19990)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19990)Memory used [KB]: 10618
% 0.20/0.53  % (19990)Time elapsed: 0.120 s
% 0.20/0.53  % (19990)------------------------------
% 0.20/0.53  % (19990)------------------------------
% 0.20/0.53  % (19986)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (20001)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (20008)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (20007)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (20009)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (20004)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (20004)Refutation not found, incomplete strategy% (20004)------------------------------
% 0.20/0.54  % (20004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (20004)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (20004)Memory used [KB]: 10746
% 0.20/0.54  % (20004)Time elapsed: 0.131 s
% 0.20/0.54  % (20004)------------------------------
% 0.20/0.54  % (20004)------------------------------
% 0.20/0.54  % (19991)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (19989)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (19996)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (20002)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (20002)Refutation not found, incomplete strategy% (20002)------------------------------
% 0.20/0.55  % (20002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20002)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (20002)Memory used [KB]: 10746
% 0.20/0.55  % (20002)Time elapsed: 0.142 s
% 0.20/0.55  % (20002)------------------------------
% 0.20/0.55  % (20002)------------------------------
% 0.20/0.55  % (19999)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.55  % (19999)Refutation not found, incomplete strategy% (19999)------------------------------
% 1.49/0.55  % (19999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (19999)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (19999)Memory used [KB]: 10746
% 1.49/0.55  % (19999)Time elapsed: 0.143 s
% 1.49/0.55  % (19999)------------------------------
% 1.49/0.55  % (19999)------------------------------
% 1.98/0.65  % (20018)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.98/0.65  % (20017)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.23/0.67  % (20019)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.23/0.69  % (20028)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.23/0.70  % (20020)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.75/0.75  % (20026)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.06/0.83  % (19987)Time limit reached!
% 3.06/0.83  % (19987)------------------------------
% 3.06/0.83  % (19987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.85  % (19987)Termination reason: Time limit
% 3.55/0.85  
% 3.55/0.85  % (19987)Memory used [KB]: 9850
% 3.55/0.85  % (19987)Time elapsed: 0.428 s
% 3.55/0.85  % (19987)------------------------------
% 3.55/0.85  % (19987)------------------------------
% 3.55/0.86  % (20006)Refutation found. Thanks to Tanya!
% 3.55/0.86  % SZS status Theorem for theBenchmark
% 3.55/0.86  % SZS output start Proof for theBenchmark
% 3.55/0.86  fof(f4079,plain,(
% 3.55/0.86    $false),
% 3.55/0.86    inference(global_subsumption,[],[f115,f4074])).
% 3.55/0.86  fof(f4074,plain,(
% 3.55/0.86    r2_hidden(sK0,sK2)),
% 3.55/0.86    inference(backward_demodulation,[],[f1855,f4071])).
% 3.55/0.86  fof(f4071,plain,(
% 3.55/0.86    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.55/0.86    inference(global_subsumption,[],[f69,f116,f4070])).
% 3.55/0.86  fof(f4070,plain,(
% 3.55/0.86    r2_hidden(sK1,sK2) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 3.55/0.86    inference(duplicate_literal_removal,[],[f4031])).
% 3.55/0.86  fof(f4031,plain,(
% 3.55/0.86    r2_hidden(sK1,sK2) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.55/0.86    inference(superposition,[],[f1855,f1169])).
% 3.55/0.86  fof(f1169,plain,(
% 3.55/0.86    ( ! [X10,X8,X7,X9] : (sK3(k2_enumset1(X7,X7,X8,X9),X10,k2_enumset1(X7,X7,X8,X9)) = X9 | sK3(k2_enumset1(X7,X7,X8,X9),X10,k2_enumset1(X7,X7,X8,X9)) = X8 | k2_enumset1(X7,X7,X8,X9) = k4_xboole_0(k2_enumset1(X7,X7,X8,X9),X10) | sK3(k2_enumset1(X7,X7,X8,X9),X10,k2_enumset1(X7,X7,X8,X9)) = X7) )),
% 3.55/0.86    inference(resolution,[],[f428,f24])).
% 3.55/0.86  fof(f24,plain,(
% 3.55/0.86    ( ! [X4,X2,X0,X1] : (~sP6(X4,X2,X1,X0) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 3.55/0.86    inference(cnf_transformation,[],[f8])).
% 3.55/0.86  fof(f8,plain,(
% 3.55/0.86    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.55/0.86    inference(ennf_transformation,[],[f2])).
% 3.55/0.86  fof(f2,axiom,(
% 3.55/0.86    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.55/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 3.55/0.86  fof(f428,plain,(
% 3.55/0.86    ( ! [X10,X8,X11,X9] : (sP6(sK3(k2_enumset1(X8,X8,X9,X10),X11,k2_enumset1(X8,X8,X9,X10)),X10,X9,X8) | k2_enumset1(X8,X8,X9,X10) = k4_xboole_0(k2_enumset1(X8,X8,X9,X10),X11)) )),
% 3.55/0.86    inference(resolution,[],[f257,f39])).
% 3.55/0.86  fof(f39,plain,(
% 3.55/0.86    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | sP6(X4,X2,X1,X0)) )),
% 3.55/0.86    inference(equality_resolution,[],[f35])).
% 3.55/0.86  fof(f35,plain,(
% 3.55/0.86    ( ! [X4,X2,X0,X3,X1] : (sP6(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.55/0.86    inference(definition_unfolding,[],[f26,f13])).
% 3.55/0.86  fof(f13,plain,(
% 3.55/0.86    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.55/0.86    inference(cnf_transformation,[],[f4])).
% 3.55/0.86  fof(f4,axiom,(
% 3.55/0.86    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.55/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.55/0.86  fof(f26,plain,(
% 3.55/0.86    ( ! [X4,X2,X0,X3,X1] : (sP6(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.55/0.86    inference(cnf_transformation,[],[f8])).
% 3.55/0.86  fof(f257,plain,(
% 3.55/0.86    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 3.55/0.86    inference(factoring,[],[f75])).
% 3.55/0.86  fof(f75,plain,(
% 3.55/0.86    ( ! [X4,X5,X3] : (r2_hidden(sK3(X3,X4,X5),X5) | k4_xboole_0(X3,X4) = X5 | r2_hidden(sK3(X3,X4,X5),X3)) )),
% 3.55/0.86    inference(resolution,[],[f19,f15])).
% 3.55/0.86  fof(f15,plain,(
% 3.55/0.86    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 3.55/0.86    inference(cnf_transformation,[],[f1])).
% 3.55/0.86  fof(f1,axiom,(
% 3.55/0.86    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.55/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.55/0.86  fof(f19,plain,(
% 3.55/0.86    ( ! [X2,X0,X1] : (sP4(sK3(X0,X1,X2),X1,X0) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 3.55/0.86    inference(cnf_transformation,[],[f1])).
% 3.55/0.86  fof(f116,plain,(
% 3.55/0.86    k2_enumset1(sK0,sK0,sK0,sK1) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 3.55/0.86    inference(unit_resulting_resolution,[],[f69,f115,f32])).
% 3.55/0.86  fof(f32,plain,(
% 3.55/0.86    k2_enumset1(sK0,sK0,sK0,sK1) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 3.55/0.86    inference(definition_unfolding,[],[f9,f29,f29])).
% 3.55/0.86  fof(f29,plain,(
% 3.55/0.86    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.55/0.86    inference(definition_unfolding,[],[f12,f13])).
% 3.55/0.86  fof(f12,plain,(
% 3.55/0.86    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.55/0.86    inference(cnf_transformation,[],[f3])).
% 3.55/0.86  fof(f3,axiom,(
% 3.55/0.86    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.55/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.55/0.86  fof(f9,plain,(
% 3.55/0.86    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.55/0.86    inference(cnf_transformation,[],[f7])).
% 3.55/0.86  fof(f7,plain,(
% 3.55/0.86    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.55/0.86    inference(ennf_transformation,[],[f6])).
% 3.55/0.86  fof(f6,negated_conjecture,(
% 3.55/0.86    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.55/0.86    inference(negated_conjecture,[],[f5])).
% 3.55/0.86  fof(f5,conjecture,(
% 3.55/0.86    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.55/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 3.55/0.86  fof(f69,plain,(
% 3.55/0.86    ~r2_hidden(sK1,sK2)),
% 3.55/0.86    inference(duplicate_literal_removal,[],[f66])).
% 3.55/0.86  fof(f66,plain,(
% 3.55/0.86    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK2)),
% 3.55/0.86    inference(resolution,[],[f60,f41])).
% 3.55/0.86  fof(f41,plain,(
% 3.55/0.86    ( ! [X4,X0,X1] : (sP6(X4,X4,X1,X0)) )),
% 3.55/0.86    inference(equality_resolution,[],[f23])).
% 3.55/0.86  fof(f23,plain,(
% 3.55/0.86    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP6(X4,X2,X1,X0)) )),
% 3.55/0.86    inference(cnf_transformation,[],[f8])).
% 3.55/0.86  fof(f60,plain,(
% 3.55/0.86    ( ! [X0] : (~sP6(X0,sK1,sK0,sK0) | ~r2_hidden(sK1,sK2) | ~r2_hidden(X0,sK2)) )),
% 3.55/0.86    inference(resolution,[],[f40,f53])).
% 3.55/0.86  fof(f53,plain,(
% 3.55/0.86    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2) | ~r2_hidden(X0,sK2)) )),
% 3.55/0.86    inference(resolution,[],[f45,f16])).
% 3.55/0.86  fof(f16,plain,(
% 3.55/0.86    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 3.55/0.86    inference(cnf_transformation,[],[f1])).
% 3.55/0.86  fof(f45,plain,(
% 3.55/0.86    ( ! [X1] : (sP4(X1,sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(X1,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2)) )),
% 3.55/0.86    inference(superposition,[],[f37,f30])).
% 3.55/0.86  fof(f30,plain,(
% 3.55/0.86    k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 3.55/0.86    inference(definition_unfolding,[],[f11,f29,f29])).
% 3.55/0.86  fof(f11,plain,(
% 3.55/0.86    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.55/0.86    inference(cnf_transformation,[],[f7])).
% 3.55/0.86  fof(f37,plain,(
% 3.55/0.86    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | sP4(X3,X1,X0)) )),
% 3.55/0.86    inference(equality_resolution,[],[f18])).
% 3.55/0.86  fof(f18,plain,(
% 3.55/0.86    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.55/0.86    inference(cnf_transformation,[],[f1])).
% 3.55/0.86  fof(f40,plain,(
% 3.55/0.86    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | ~sP6(X4,X2,X1,X0)) )),
% 3.55/0.86    inference(equality_resolution,[],[f36])).
% 3.55/0.86  fof(f36,plain,(
% 3.55/0.86    ( ! [X4,X2,X0,X3,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.55/0.86    inference(definition_unfolding,[],[f25,f13])).
% 3.55/0.86  fof(f25,plain,(
% 3.55/0.86    ( ! [X4,X2,X0,X3,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.55/0.86    inference(cnf_transformation,[],[f8])).
% 3.55/0.86  fof(f1855,plain,(
% 3.55/0.86    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)),
% 3.55/0.86    inference(unit_resulting_resolution,[],[f116,f1021])).
% 3.55/0.86  fof(f1021,plain,(
% 3.55/0.86    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,X2),X3) | k4_xboole_0(X2,X3) = X2) )),
% 3.55/0.86    inference(duplicate_literal_removal,[],[f1018])).
% 3.55/0.86  fof(f1018,plain,(
% 3.55/0.86    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,X2),X3) | k4_xboole_0(X2,X3) = X2 | k4_xboole_0(X2,X3) = X2) )),
% 3.55/0.86    inference(resolution,[],[f429,f257])).
% 3.55/0.86  fof(f429,plain,(
% 3.55/0.86    ( ! [X2,X1] : (~r2_hidden(sK3(X1,X2,X1),X1) | r2_hidden(sK3(X1,X2,X1),X2) | k4_xboole_0(X1,X2) = X1) )),
% 3.55/0.86    inference(duplicate_literal_removal,[],[f424])).
% 3.55/0.86  fof(f424,plain,(
% 3.55/0.86    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | k4_xboole_0(X1,X2) = X1 | r2_hidden(sK3(X1,X2,X1),X2) | ~r2_hidden(sK3(X1,X2,X1),X1)) )),
% 3.55/0.86    inference(resolution,[],[f257,f92])).
% 3.55/0.86  fof(f92,plain,(
% 3.55/0.86    ( ! [X6,X7,X5] : (~r2_hidden(sK3(X5,X6,X7),X7) | k4_xboole_0(X5,X6) = X7 | r2_hidden(sK3(X5,X6,X7),X6) | ~r2_hidden(sK3(X5,X6,X7),X5)) )),
% 3.55/0.86    inference(resolution,[],[f20,f14])).
% 3.55/0.86  fof(f14,plain,(
% 3.55/0.86    ( ! [X0,X3,X1] : (sP4(X3,X1,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 3.55/0.86    inference(cnf_transformation,[],[f1])).
% 3.55/0.86  fof(f20,plain,(
% 3.55/0.86    ( ! [X2,X0,X1] : (~sP4(sK3(X0,X1,X2),X1,X0) | ~r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 3.55/0.86    inference(cnf_transformation,[],[f1])).
% 3.55/0.86  fof(f115,plain,(
% 3.55/0.86    ~r2_hidden(sK0,sK2)),
% 3.55/0.86    inference(duplicate_literal_removal,[],[f112])).
% 3.55/0.86  fof(f112,plain,(
% 3.55/0.86    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK2)),
% 3.55/0.86    inference(resolution,[],[f61,f42])).
% 3.55/0.86  fof(f42,plain,(
% 3.55/0.86    ( ! [X4,X2,X0] : (sP6(X4,X2,X4,X0)) )),
% 3.55/0.86    inference(equality_resolution,[],[f22])).
% 3.55/0.86  fof(f22,plain,(
% 3.55/0.86    ( ! [X4,X2,X0,X1] : (X1 != X4 | sP6(X4,X2,X1,X0)) )),
% 3.55/0.86    inference(cnf_transformation,[],[f8])).
% 3.55/0.86  fof(f61,plain,(
% 3.55/0.86    ( ! [X1] : (~sP6(X1,sK1,sK0,sK0) | ~r2_hidden(sK0,sK2) | ~r2_hidden(X1,sK2)) )),
% 3.55/0.86    inference(resolution,[],[f40,f51])).
% 3.55/0.86  fof(f51,plain,(
% 3.55/0.86    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2) | ~r2_hidden(X0,sK2)) )),
% 3.55/0.86    inference(resolution,[],[f44,f16])).
% 3.55/0.86  fof(f44,plain,(
% 3.55/0.86    ( ! [X0] : (sP4(X0,sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2)) )),
% 3.55/0.86    inference(superposition,[],[f37,f31])).
% 3.55/0.86  fof(f31,plain,(
% 3.55/0.86    k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK0,sK2)),
% 3.55/0.86    inference(definition_unfolding,[],[f10,f29,f29])).
% 3.55/0.86  fof(f10,plain,(
% 3.55/0.86    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.55/0.86    inference(cnf_transformation,[],[f7])).
% 3.55/0.86  % SZS output end Proof for theBenchmark
% 3.55/0.86  % (20006)------------------------------
% 3.55/0.86  % (20006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.55/0.86  % (20006)Termination reason: Refutation
% 3.55/0.86  
% 3.55/0.86  % (20006)Memory used [KB]: 9978
% 3.55/0.86  % (20006)Time elapsed: 0.434 s
% 3.55/0.86  % (20006)------------------------------
% 3.55/0.86  % (20006)------------------------------
% 3.55/0.86  % (19981)Success in time 0.497 s
%------------------------------------------------------------------------------
