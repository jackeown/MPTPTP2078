%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:06 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 109 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 190 expanded)
%              Number of equality atoms :   43 ( 128 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f377,plain,(
    $false ),
    inference(resolution,[],[f360,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(unit_resulting_resolution,[],[f47,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f31,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X1] : sP5(X4,X2,X1,X4) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f360,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK2,sK3)) ),
    inference(backward_demodulation,[],[f195,f346])).

fof(f346,plain,(
    k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK2,sK3) ),
    inference(forward_demodulation,[],[f344,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f25,f24,f36,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f35])).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f344,plain,(
    k2_enumset1(sK2,sK2,sK2,sK3) = k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f332,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f332,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f184,f276])).

fof(f276,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k2_enumset1(sK0,sK0,sK0,sK1))
      | r1_tarski(X3,k2_enumset1(sK2,sK2,sK2,sK3)) ) ),
    inference(superposition,[],[f83,f54])).

fof(f54,plain,(
    k2_enumset1(sK2,sK2,sK2,sK3) = k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f37,f23])).

fof(f37,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f16,f35,f35])).

fof(f16,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f83,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(X5,k2_xboole_0(X4,X3))
      | ~ r1_tarski(X5,X4) ) ),
    inference(superposition,[],[f26,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f184,plain,(
    ! [X2,X3,X1] : r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X2,X3)) ),
    inference(superposition,[],[f20,f38])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f195,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f156,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f32,f24])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f156,plain,(
    ~ sP5(sK0,sK3,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f17,f18,f17,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f18,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f12])).

fof(f17,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (4153)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (4145)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (4144)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (4137)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (4153)Refutation not found, incomplete strategy% (4153)------------------------------
% 0.20/0.50  % (4153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4153)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (4153)Memory used [KB]: 10746
% 0.20/0.50  % (4153)Time elapsed: 0.058 s
% 0.20/0.50  % (4153)------------------------------
% 0.20/0.50  % (4153)------------------------------
% 0.20/0.51  % (4158)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (4160)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (4139)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (4139)Refutation not found, incomplete strategy% (4139)------------------------------
% 0.20/0.52  % (4139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4135)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (4152)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (4140)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (4136)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (4138)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (4148)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (4131)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (4156)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (4134)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (4133)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (4133)Refutation not found, incomplete strategy% (4133)------------------------------
% 0.20/0.53  % (4133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4133)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4133)Memory used [KB]: 10618
% 0.20/0.53  % (4133)Time elapsed: 0.128 s
% 0.20/0.53  % (4133)------------------------------
% 0.20/0.53  % (4133)------------------------------
% 0.20/0.53  % (4132)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (4141)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (4151)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (4148)Refutation not found, incomplete strategy% (4148)------------------------------
% 0.20/0.54  % (4148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (4148)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (4148)Memory used [KB]: 10618
% 0.20/0.54  % (4148)Time elapsed: 0.132 s
% 0.20/0.54  % (4148)------------------------------
% 0.20/0.54  % (4148)------------------------------
% 0.20/0.54  % (4142)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (4157)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (4155)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (4139)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (4139)Memory used [KB]: 10618
% 0.20/0.54  % (4139)Time elapsed: 0.108 s
% 0.20/0.54  % (4139)------------------------------
% 0.20/0.54  % (4139)------------------------------
% 0.20/0.54  % (4150)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (4147)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (4154)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (4159)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.55  % (4149)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.51/0.55  % (4143)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.56  % (4146)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.56  % (4146)Refutation not found, incomplete strategy% (4146)------------------------------
% 1.51/0.56  % (4146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (4155)Refutation found. Thanks to Tanya!
% 1.51/0.57  % SZS status Theorem for theBenchmark
% 1.64/0.57  % (4146)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.57  
% 1.64/0.57  % (4146)Memory used [KB]: 6140
% 1.64/0.57  % (4146)Time elapsed: 0.162 s
% 1.64/0.57  % (4146)------------------------------
% 1.64/0.57  % (4146)------------------------------
% 1.64/0.57  % SZS output start Proof for theBenchmark
% 1.64/0.57  fof(f377,plain,(
% 1.64/0.57    $false),
% 1.64/0.57    inference(resolution,[],[f360,f144])).
% 1.64/0.57  fof(f144,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))) )),
% 1.64/0.57    inference(unit_resulting_resolution,[],[f47,f44])).
% 1.64/0.57  fof(f44,plain,(
% 1.64/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | ~sP5(X4,X2,X1,X0)) )),
% 1.64/0.57    inference(equality_resolution,[],[f42])).
% 1.64/0.57  fof(f42,plain,(
% 1.64/0.57    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.64/0.57    inference(definition_unfolding,[],[f31,f24])).
% 1.64/0.57  fof(f24,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f9])).
% 1.64/0.57  fof(f9,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.64/0.57  fof(f31,plain,(
% 1.64/0.57    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.64/0.57    inference(cnf_transformation,[],[f15])).
% 1.64/0.57  fof(f15,plain,(
% 1.64/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.64/0.57    inference(ennf_transformation,[],[f5])).
% 1.64/0.57  fof(f5,axiom,(
% 1.64/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.64/0.57  fof(f47,plain,(
% 1.64/0.57    ( ! [X4,X2,X1] : (sP5(X4,X2,X1,X4)) )),
% 1.64/0.57    inference(equality_resolution,[],[f27])).
% 1.64/0.57  fof(f27,plain,(
% 1.64/0.57    ( ! [X4,X2,X0,X1] : (X0 != X4 | sP5(X4,X2,X1,X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f15])).
% 1.64/0.57  fof(f360,plain,(
% 1.64/0.57    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK2,sK3))),
% 1.64/0.57    inference(backward_demodulation,[],[f195,f346])).
% 1.64/0.57  fof(f346,plain,(
% 1.64/0.57    k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK2,sK3)),
% 1.64/0.57    inference(forward_demodulation,[],[f344,f38])).
% 1.64/0.57  fof(f38,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))) )),
% 1.64/0.57    inference(definition_unfolding,[],[f25,f24,f36,f35])).
% 1.64/0.57  fof(f35,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f22,f24])).
% 1.64/0.57  fof(f22,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f8])).
% 1.64/0.57  fof(f8,axiom,(
% 1.64/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.64/0.57  fof(f36,plain,(
% 1.64/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f19,f35])).
% 1.64/0.57  fof(f19,plain,(
% 1.64/0.57    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f7])).
% 1.64/0.57  fof(f7,axiom,(
% 1.64/0.57    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.64/0.57  fof(f25,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f6])).
% 1.64/0.57  fof(f6,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 1.64/0.57  fof(f344,plain,(
% 1.64/0.57    k2_enumset1(sK2,sK2,sK2,sK3) = k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.64/0.57    inference(unit_resulting_resolution,[],[f332,f23])).
% 1.64/0.57  fof(f23,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f13])).
% 1.64/0.57  fof(f13,plain,(
% 1.64/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f3])).
% 1.64/0.57  fof(f3,axiom,(
% 1.64/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.64/0.57  fof(f332,plain,(
% 1.64/0.57    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.64/0.57    inference(unit_resulting_resolution,[],[f184,f276])).
% 1.64/0.57  fof(f276,plain,(
% 1.64/0.57    ( ! [X3] : (~r1_tarski(X3,k2_enumset1(sK0,sK0,sK0,sK1)) | r1_tarski(X3,k2_enumset1(sK2,sK2,sK2,sK3))) )),
% 1.64/0.57    inference(superposition,[],[f83,f54])).
% 1.64/0.57  fof(f54,plain,(
% 1.64/0.57    k2_enumset1(sK2,sK2,sK2,sK3) = k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.64/0.57    inference(unit_resulting_resolution,[],[f37,f23])).
% 1.64/0.57  fof(f37,plain,(
% 1.64/0.57    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.64/0.57    inference(definition_unfolding,[],[f16,f35,f35])).
% 1.64/0.57  fof(f16,plain,(
% 1.64/0.57    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.64/0.57    inference(cnf_transformation,[],[f12])).
% 1.64/0.57  fof(f12,plain,(
% 1.64/0.57    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.64/0.57    inference(ennf_transformation,[],[f11])).
% 1.64/0.57  fof(f11,negated_conjecture,(
% 1.64/0.57    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.64/0.57    inference(negated_conjecture,[],[f10])).
% 1.64/0.57  fof(f10,conjecture,(
% 1.64/0.57    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.64/0.57  fof(f83,plain,(
% 1.64/0.57    ( ! [X4,X5,X3] : (r1_tarski(X5,k2_xboole_0(X4,X3)) | ~r1_tarski(X5,X4)) )),
% 1.64/0.57    inference(superposition,[],[f26,f21])).
% 1.64/0.57  fof(f21,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f1])).
% 1.64/0.57  fof(f1,axiom,(
% 1.64/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.64/0.57  fof(f26,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f14])).
% 1.64/0.57  fof(f14,plain,(
% 1.64/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f2])).
% 1.64/0.57  fof(f2,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.64/0.57  fof(f184,plain,(
% 1.64/0.57    ( ! [X2,X3,X1] : (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X2,X3))) )),
% 1.64/0.57    inference(superposition,[],[f20,f38])).
% 1.64/0.57  fof(f20,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f4])).
% 1.64/0.57  fof(f4,axiom,(
% 1.64/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.64/0.57  fof(f195,plain,(
% 1.64/0.57    ~r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.64/0.57    inference(unit_resulting_resolution,[],[f156,f43])).
% 1.64/0.57  fof(f43,plain,(
% 1.64/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | sP5(X4,X2,X1,X0)) )),
% 1.64/0.57    inference(equality_resolution,[],[f41])).
% 1.64/0.57  fof(f41,plain,(
% 1.64/0.57    ( ! [X4,X2,X0,X3,X1] : (sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.64/0.57    inference(definition_unfolding,[],[f32,f24])).
% 1.64/0.57  fof(f32,plain,(
% 1.64/0.57    ( ! [X4,X2,X0,X3,X1] : (sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.64/0.57    inference(cnf_transformation,[],[f15])).
% 1.64/0.57  fof(f156,plain,(
% 1.64/0.57    ~sP5(sK0,sK3,sK2,sK2)),
% 1.64/0.57    inference(unit_resulting_resolution,[],[f17,f18,f17,f30])).
% 1.64/0.57  fof(f30,plain,(
% 1.64/0.57    ( ! [X4,X2,X0,X1] : (~sP5(X4,X2,X1,X0) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.64/0.57    inference(cnf_transformation,[],[f15])).
% 1.64/0.57  fof(f18,plain,(
% 1.64/0.57    sK0 != sK3),
% 1.64/0.57    inference(cnf_transformation,[],[f12])).
% 1.64/0.57  fof(f17,plain,(
% 1.64/0.57    sK0 != sK2),
% 1.64/0.57    inference(cnf_transformation,[],[f12])).
% 1.64/0.57  % SZS output end Proof for theBenchmark
% 1.64/0.57  % (4155)------------------------------
% 1.64/0.57  % (4155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (4155)Termination reason: Refutation
% 1.64/0.57  
% 1.64/0.57  % (4155)Memory used [KB]: 6524
% 1.64/0.57  % (4155)Time elapsed: 0.149 s
% 1.64/0.57  % (4155)------------------------------
% 1.64/0.57  % (4155)------------------------------
% 1.64/0.57  % (4130)Success in time 0.217 s
%------------------------------------------------------------------------------
