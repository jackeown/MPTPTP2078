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
% DateTime   : Thu Dec  3 12:30:53 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 182 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   19
%              Number of atoms          :  105 ( 398 expanded)
%              Number of equality atoms :   64 ( 226 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1058,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1057,f25])).

fof(f25,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f1057,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1051,f807])).

fof(f807,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f774,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f774,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f769,f43])).

fof(f43,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f27,f22])).

fof(f22,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f769,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_xboole_0(sK0,X0))
      | k2_xboole_0(sK2,X0) = X0 ) ),
    inference(resolution,[],[f723,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f723,plain,(
    ! [X0] :
      ( r1_tarski(sK2,X0)
      | ~ r1_tarski(sK2,k2_xboole_0(sK0,X0)) ) ),
    inference(superposition,[],[f38,f716])).

fof(f716,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f690,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f690,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f40,f149])).

fof(f149,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f42,f23])).

fof(f23,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f35,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1051,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f54,f1016])).

fof(f1016,plain,(
    sK1 = k4_xboole_0(sK2,sK3) ),
    inference(backward_demodulation,[],[f75,f976])).

fof(f976,plain,(
    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(forward_demodulation,[],[f963,f715])).

fof(f715,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f689,f26])).

fof(f689,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f40,f492])).

fof(f492,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f39,f150])).

fof(f150,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f42,f24])).

fof(f24,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f31,f31])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f963,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f33,f890])).

fof(f890,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f880,f55])).

fof(f55,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = X6 ),
    inference(resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f880,plain,(
    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f775,f319])).

fof(f319,plain,(
    ! [X0] : k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f313,f30])).

fof(f313,plain,(
    ! [X24] : k2_xboole_0(sK2,k2_xboole_0(sK3,X24)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X24)) ),
    inference(forward_demodulation,[],[f288,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f288,plain,(
    ! [X24] : k2_xboole_0(sK2,k2_xboole_0(sK3,X24)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X24) ),
    inference(superposition,[],[f37,f22])).

fof(f775,plain,(
    ! [X0] : k2_xboole_0(sK1,X0) = k2_xboole_0(sK2,k2_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f769,f323])).

fof(f323,plain,(
    ! [X0] : r1_tarski(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X0))) ),
    inference(superposition,[],[f27,f313])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f75,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f33,f22])).

fof(f54,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),X4) = X4 ),
    inference(resolution,[],[f34,f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:17:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (1157)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.49  % (1149)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.49  % (1148)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (1140)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.18/0.51  % (1139)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.18/0.51  % (1158)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.18/0.52  % (1147)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.18/0.52  % (1150)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.18/0.52  % (1136)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.18/0.52  % (1153)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.18/0.52  % (1154)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.18/0.52  % (1137)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.18/0.52  % (1142)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.18/0.52  % (1144)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.18/0.52  % (1164)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.18/0.52  % (1135)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.18/0.52  % (1163)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.18/0.53  % (1141)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.18/0.53  % (1146)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.18/0.53  % (1138)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.53  % (1160)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.53  % (1152)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.53  % (1156)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.53  % (1162)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.53  % (1161)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.53  % (1155)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.54  % (1159)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.54  % (1145)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.54  % (1151)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.54  % (1165)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.54  % (1151)Refutation not found, incomplete strategy% (1151)------------------------------
% 1.29/0.54  % (1151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (1151)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (1151)Memory used [KB]: 6140
% 1.29/0.54  % (1151)Time elapsed: 0.002 s
% 1.29/0.54  % (1151)------------------------------
% 1.29/0.54  % (1151)------------------------------
% 1.29/0.55  % (1153)Refutation not found, incomplete strategy% (1153)------------------------------
% 1.29/0.55  % (1153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (1153)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (1153)Memory used [KB]: 10618
% 1.29/0.55  % (1153)Time elapsed: 0.144 s
% 1.29/0.55  % (1153)------------------------------
% 1.29/0.55  % (1153)------------------------------
% 1.29/0.56  % (1138)Refutation found. Thanks to Tanya!
% 1.29/0.56  % SZS status Theorem for theBenchmark
% 1.29/0.56  % SZS output start Proof for theBenchmark
% 1.29/0.56  fof(f1058,plain,(
% 1.29/0.56    $false),
% 1.29/0.56    inference(subsumption_resolution,[],[f1057,f25])).
% 1.29/0.56  fof(f25,plain,(
% 1.29/0.56    sK1 != sK2),
% 1.29/0.56    inference(cnf_transformation,[],[f20])).
% 1.29/0.56  fof(f20,plain,(
% 1.29/0.56    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.29/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f19])).
% 1.29/0.56  fof(f19,plain,(
% 1.29/0.56    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f16,plain,(
% 1.29/0.56    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.29/0.56    inference(flattening,[],[f15])).
% 1.29/0.56  fof(f15,plain,(
% 1.29/0.56    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.29/0.56    inference(ennf_transformation,[],[f14])).
% 1.29/0.56  fof(f14,negated_conjecture,(
% 1.29/0.56    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.29/0.56    inference(negated_conjecture,[],[f13])).
% 1.29/0.56  fof(f13,conjecture,(
% 1.29/0.56    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.29/0.56  fof(f1057,plain,(
% 1.29/0.56    sK1 = sK2),
% 1.29/0.56    inference(forward_demodulation,[],[f1051,f807])).
% 1.29/0.56  fof(f807,plain,(
% 1.29/0.56    sK1 = k2_xboole_0(sK1,sK2)),
% 1.29/0.56    inference(superposition,[],[f774,f30])).
% 1.29/0.56  fof(f30,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f1])).
% 1.29/0.56  fof(f1,axiom,(
% 1.29/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.29/0.56  fof(f774,plain,(
% 1.29/0.56    sK1 = k2_xboole_0(sK2,sK1)),
% 1.29/0.56    inference(resolution,[],[f769,f43])).
% 1.29/0.56  fof(f43,plain,(
% 1.29/0.56    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 1.29/0.56    inference(superposition,[],[f27,f22])).
% 1.29/0.56  fof(f22,plain,(
% 1.29/0.56    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.29/0.56    inference(cnf_transformation,[],[f20])).
% 1.29/0.56  fof(f27,plain,(
% 1.29/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f12])).
% 1.29/0.56  fof(f12,axiom,(
% 1.29/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.29/0.56  fof(f769,plain,(
% 1.29/0.56    ( ! [X0] : (~r1_tarski(sK2,k2_xboole_0(sK0,X0)) | k2_xboole_0(sK2,X0) = X0) )),
% 1.29/0.56    inference(resolution,[],[f723,f34])).
% 1.29/0.56  fof(f34,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.29/0.56    inference(cnf_transformation,[],[f17])).
% 1.29/0.56  fof(f17,plain,(
% 1.29/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.29/0.56    inference(ennf_transformation,[],[f4])).
% 1.29/0.56  fof(f4,axiom,(
% 1.29/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.29/0.56  fof(f723,plain,(
% 1.29/0.56    ( ! [X0] : (r1_tarski(sK2,X0) | ~r1_tarski(sK2,k2_xboole_0(sK0,X0))) )),
% 1.29/0.56    inference(superposition,[],[f38,f716])).
% 1.29/0.56  fof(f716,plain,(
% 1.29/0.56    sK2 = k4_xboole_0(sK2,sK0)),
% 1.29/0.56    inference(forward_demodulation,[],[f690,f26])).
% 1.29/0.56  fof(f26,plain,(
% 1.29/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.29/0.56    inference(cnf_transformation,[],[f6])).
% 1.29/0.56  fof(f6,axiom,(
% 1.29/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.29/0.56  fof(f690,plain,(
% 1.29/0.56    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.29/0.56    inference(superposition,[],[f40,f149])).
% 1.29/0.56  fof(f149,plain,(
% 1.29/0.56    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.29/0.56    inference(resolution,[],[f42,f23])).
% 1.29/0.56  fof(f23,plain,(
% 1.29/0.56    r1_xboole_0(sK2,sK0)),
% 1.29/0.56    inference(cnf_transformation,[],[f20])).
% 1.29/0.56  fof(f42,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.29/0.56    inference(definition_unfolding,[],[f35,f31])).
% 1.29/0.56  fof(f31,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f10])).
% 1.29/0.56  fof(f10,axiom,(
% 1.29/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.29/0.56  fof(f35,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f21])).
% 1.29/0.56  fof(f21,plain,(
% 1.29/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.29/0.56    inference(nnf_transformation,[],[f3])).
% 1.29/0.56  fof(f3,axiom,(
% 1.29/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.29/0.56  fof(f40,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.29/0.56    inference(definition_unfolding,[],[f32,f31])).
% 1.29/0.56  fof(f32,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f9])).
% 1.29/0.56  fof(f9,axiom,(
% 1.29/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.29/0.56  fof(f38,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f18])).
% 1.29/0.56  fof(f18,plain,(
% 1.29/0.56    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.29/0.56    inference(ennf_transformation,[],[f8])).
% 1.29/0.56  fof(f8,axiom,(
% 1.29/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.29/0.56  fof(f1051,plain,(
% 1.29/0.56    sK2 = k2_xboole_0(sK1,sK2)),
% 1.29/0.56    inference(superposition,[],[f54,f1016])).
% 1.29/0.56  fof(f1016,plain,(
% 1.29/0.56    sK1 = k4_xboole_0(sK2,sK3)),
% 1.29/0.56    inference(backward_demodulation,[],[f75,f976])).
% 1.29/0.56  fof(f976,plain,(
% 1.29/0.56    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.29/0.56    inference(forward_demodulation,[],[f963,f715])).
% 1.29/0.56  fof(f715,plain,(
% 1.29/0.56    sK1 = k4_xboole_0(sK1,sK3)),
% 1.29/0.56    inference(forward_demodulation,[],[f689,f26])).
% 1.29/0.56  fof(f689,plain,(
% 1.29/0.56    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK3)),
% 1.29/0.56    inference(superposition,[],[f40,f492])).
% 1.29/0.56  fof(f492,plain,(
% 1.29/0.56    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.29/0.56    inference(superposition,[],[f39,f150])).
% 1.29/0.56  fof(f150,plain,(
% 1.29/0.56    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.29/0.56    inference(resolution,[],[f42,f24])).
% 1.29/0.56  fof(f24,plain,(
% 1.29/0.56    r1_xboole_0(sK3,sK1)),
% 1.29/0.56    inference(cnf_transformation,[],[f20])).
% 1.29/0.56  fof(f39,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.29/0.56    inference(definition_unfolding,[],[f29,f31,f31])).
% 1.29/0.56  fof(f29,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f2])).
% 1.29/0.56  fof(f2,axiom,(
% 1.29/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.29/0.56  fof(f963,plain,(
% 1.29/0.56    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3)),
% 1.29/0.56    inference(superposition,[],[f33,f890])).
% 1.29/0.56  fof(f890,plain,(
% 1.29/0.56    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)),
% 1.29/0.56    inference(forward_demodulation,[],[f880,f55])).
% 1.29/0.56  fof(f55,plain,(
% 1.29/0.56    ( ! [X6] : (k2_xboole_0(X6,X6) = X6) )),
% 1.29/0.56    inference(resolution,[],[f34,f44])).
% 1.29/0.56  fof(f44,plain,(
% 1.29/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.29/0.56    inference(superposition,[],[f28,f26])).
% 1.29/0.56  fof(f28,plain,(
% 1.29/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f5])).
% 1.29/0.56  fof(f5,axiom,(
% 1.29/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.29/0.56  fof(f880,plain,(
% 1.29/0.56    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK1))),
% 1.29/0.56    inference(superposition,[],[f775,f319])).
% 1.29/0.56  fof(f319,plain,(
% 1.29/0.56    ( ! [X0] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3))) )),
% 1.29/0.56    inference(superposition,[],[f313,f30])).
% 1.29/0.56  fof(f313,plain,(
% 1.29/0.56    ( ! [X24] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X24)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X24))) )),
% 1.29/0.56    inference(forward_demodulation,[],[f288,f37])).
% 1.29/0.56  fof(f37,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f11])).
% 1.29/0.56  fof(f11,axiom,(
% 1.29/0.56    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.29/0.56  fof(f288,plain,(
% 1.29/0.56    ( ! [X24] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X24)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X24)) )),
% 1.29/0.56    inference(superposition,[],[f37,f22])).
% 1.29/0.56  fof(f775,plain,(
% 1.29/0.56    ( ! [X0] : (k2_xboole_0(sK1,X0) = k2_xboole_0(sK2,k2_xboole_0(sK1,X0))) )),
% 1.29/0.56    inference(resolution,[],[f769,f323])).
% 1.29/0.56  fof(f323,plain,(
% 1.29/0.56    ( ! [X0] : (r1_tarski(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X0)))) )),
% 1.29/0.56    inference(superposition,[],[f27,f313])).
% 1.29/0.56  fof(f33,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f7])).
% 1.29/0.56  fof(f7,axiom,(
% 1.29/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.29/0.56  fof(f75,plain,(
% 1.29/0.56    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.29/0.56    inference(superposition,[],[f33,f22])).
% 1.29/0.56  fof(f54,plain,(
% 1.29/0.56    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),X4) = X4) )),
% 1.29/0.56    inference(resolution,[],[f34,f28])).
% 1.29/0.56  % SZS output end Proof for theBenchmark
% 1.29/0.56  % (1138)------------------------------
% 1.29/0.56  % (1138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (1138)Termination reason: Refutation
% 1.29/0.56  
% 1.29/0.56  % (1138)Memory used [KB]: 11129
% 1.29/0.56  % (1138)Time elapsed: 0.143 s
% 1.29/0.56  % (1138)------------------------------
% 1.29/0.56  % (1138)------------------------------
% 1.29/0.57  % (1134)Success in time 0.21 s
%------------------------------------------------------------------------------
