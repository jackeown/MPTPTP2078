%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:58 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   54 (  86 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  112 ( 235 expanded)
%              Number of equality atoms :   47 ( 106 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f659,plain,(
    $false ),
    inference(subsumption_resolution,[],[f658,f33])).

fof(f33,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f27])).

fof(f27,plain,
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

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f658,plain,(
    ~ r1_xboole_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f647,f519])).

fof(f519,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f508,f34])).

fof(f34,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f508,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | sK1 = sK2 ),
    inference(superposition,[],[f40,f135])).

fof(f135,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f88,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f88,plain,(
    r1_tarski(sK2,sK1) ),
    inference(backward_demodulation,[],[f75,f87])).

fof(f87,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f84,f35])).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f84,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f39,f52])).

fof(f52,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f75,plain,(
    r1_tarski(k4_xboole_0(sK2,sK0),sK1) ),
    inference(resolution,[],[f46,f50])).

fof(f50,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f36,f31])).

fof(f31,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f647,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f373,f82])).

fof(f82,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k4_xboole_0(X4,X5),X3)
      | k1_xboole_0 = k4_xboole_0(X4,X5)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f373,plain,(
    r1_tarski(k4_xboole_0(sK1,sK2),sK3) ),
    inference(superposition,[],[f164,f35])).

fof(f164,plain,(
    ! [X3] : r1_tarski(k4_xboole_0(k4_xboole_0(sK1,X3),sK2),sK3) ),
    inference(resolution,[],[f59,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK0,sK1))
      | r1_tarski(k4_xboole_0(X0,sK2),sK3) ) ),
    inference(superposition,[],[f46,f31])).

fof(f59,plain,(
    ! [X4,X5,X3] : r1_tarski(k4_xboole_0(X3,X4),k2_xboole_0(X5,X3)) ),
    inference(resolution,[],[f45,f37])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:33:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (28230)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (28212)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (28214)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (28228)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (28229)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (28222)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (28213)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (28221)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (28220)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.38/0.55  % (28224)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.38/0.55  % (28206)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.38/0.55  % (28222)Refutation not found, incomplete strategy% (28222)------------------------------
% 1.38/0.55  % (28222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (28222)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (28222)Memory used [KB]: 10618
% 1.38/0.55  % (28222)Time elapsed: 0.129 s
% 1.38/0.55  % (28222)------------------------------
% 1.38/0.55  % (28222)------------------------------
% 1.38/0.55  % (28210)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.38/0.55  % (28215)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.55  % (28227)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.55  % (28223)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.55  % (28219)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.38/0.55  % (28234)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.55  % (28233)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.56  % (28235)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.56  % (28216)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.38/0.56  % (28208)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.38/0.56  % (28231)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.56  % (28217)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.56  % (28218)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.56  % (28216)Refutation not found, incomplete strategy% (28216)------------------------------
% 1.38/0.56  % (28216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (28216)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (28216)Memory used [KB]: 10746
% 1.38/0.56  % (28216)Time elapsed: 0.153 s
% 1.38/0.56  % (28216)------------------------------
% 1.38/0.56  % (28216)------------------------------
% 1.38/0.56  % (28232)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.38/0.56  % (28211)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.51/0.57  % (28226)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.51/0.57  % (28207)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.51/0.57  % (28209)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.51/0.57  % (28225)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.51/0.58  % (28234)Refutation not found, incomplete strategy% (28234)------------------------------
% 1.51/0.58  % (28234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (28213)Refutation found. Thanks to Tanya!
% 1.51/0.58  % SZS status Theorem for theBenchmark
% 1.51/0.59  % (28234)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.59  
% 1.51/0.59  % (28234)Memory used [KB]: 10746
% 1.51/0.59  % (28234)Time elapsed: 0.168 s
% 1.51/0.59  % (28234)------------------------------
% 1.51/0.59  % (28234)------------------------------
% 1.51/0.60  % SZS output start Proof for theBenchmark
% 1.51/0.60  fof(f659,plain,(
% 1.51/0.60    $false),
% 1.51/0.60    inference(subsumption_resolution,[],[f658,f33])).
% 1.51/0.60  fof(f33,plain,(
% 1.51/0.60    r1_xboole_0(sK3,sK1)),
% 1.51/0.60    inference(cnf_transformation,[],[f28])).
% 1.51/0.60  fof(f28,plain,(
% 1.51/0.60    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.51/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f27])).
% 1.51/0.60  fof(f27,plain,(
% 1.51/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.51/0.60    introduced(choice_axiom,[])).
% 1.51/0.60  fof(f17,plain,(
% 1.51/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.51/0.60    inference(flattening,[],[f16])).
% 1.51/0.60  fof(f16,plain,(
% 1.51/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.51/0.60    inference(ennf_transformation,[],[f15])).
% 1.51/0.60  fof(f15,negated_conjecture,(
% 1.51/0.60    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.51/0.60    inference(negated_conjecture,[],[f14])).
% 1.51/0.60  fof(f14,conjecture,(
% 1.51/0.60    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.51/0.60  fof(f658,plain,(
% 1.51/0.60    ~r1_xboole_0(sK3,sK1)),
% 1.51/0.60    inference(subsumption_resolution,[],[f647,f519])).
% 1.51/0.60  fof(f519,plain,(
% 1.51/0.60    k1_xboole_0 != k4_xboole_0(sK1,sK2)),
% 1.51/0.60    inference(subsumption_resolution,[],[f508,f34])).
% 1.51/0.60  fof(f34,plain,(
% 1.51/0.60    sK1 != sK2),
% 1.51/0.60    inference(cnf_transformation,[],[f28])).
% 1.51/0.60  fof(f508,plain,(
% 1.51/0.60    k1_xboole_0 != k4_xboole_0(sK1,sK2) | sK1 = sK2),
% 1.51/0.60    inference(superposition,[],[f40,f135])).
% 1.51/0.60  fof(f135,plain,(
% 1.51/0.60    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.51/0.60    inference(resolution,[],[f88,f44])).
% 1.51/0.60  fof(f44,plain,(
% 1.51/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f30])).
% 1.51/0.60  fof(f30,plain,(
% 1.51/0.60    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.51/0.60    inference(nnf_transformation,[],[f2])).
% 1.51/0.60  fof(f2,axiom,(
% 1.51/0.60    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.51/0.60  fof(f88,plain,(
% 1.51/0.60    r1_tarski(sK2,sK1)),
% 1.51/0.60    inference(backward_demodulation,[],[f75,f87])).
% 1.51/0.60  fof(f87,plain,(
% 1.51/0.60    sK2 = k4_xboole_0(sK2,sK0)),
% 1.51/0.60    inference(forward_demodulation,[],[f84,f35])).
% 1.51/0.60  fof(f35,plain,(
% 1.51/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.51/0.60    inference(cnf_transformation,[],[f6])).
% 1.51/0.60  fof(f6,axiom,(
% 1.51/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.51/0.60  fof(f84,plain,(
% 1.51/0.60    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.51/0.60    inference(superposition,[],[f39,f52])).
% 1.51/0.60  fof(f52,plain,(
% 1.51/0.60    k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 1.51/0.60    inference(resolution,[],[f41,f32])).
% 1.51/0.60  fof(f32,plain,(
% 1.51/0.60    r1_xboole_0(sK2,sK0)),
% 1.51/0.60    inference(cnf_transformation,[],[f28])).
% 1.51/0.60  fof(f41,plain,(
% 1.51/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.51/0.60    inference(cnf_transformation,[],[f29])).
% 1.51/0.60  fof(f29,plain,(
% 1.51/0.60    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.51/0.60    inference(nnf_transformation,[],[f1])).
% 1.51/0.60  fof(f1,axiom,(
% 1.51/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.51/0.60  fof(f39,plain,(
% 1.51/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.51/0.60    inference(cnf_transformation,[],[f8])).
% 1.51/0.60  fof(f8,axiom,(
% 1.51/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.51/0.60  fof(f75,plain,(
% 1.51/0.60    r1_tarski(k4_xboole_0(sK2,sK0),sK1)),
% 1.51/0.60    inference(resolution,[],[f46,f50])).
% 1.51/0.60  fof(f50,plain,(
% 1.51/0.60    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 1.51/0.60    inference(superposition,[],[f36,f31])).
% 1.51/0.60  fof(f31,plain,(
% 1.51/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.51/0.60    inference(cnf_transformation,[],[f28])).
% 1.51/0.60  fof(f36,plain,(
% 1.51/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.51/0.60    inference(cnf_transformation,[],[f12])).
% 1.51/0.60  fof(f12,axiom,(
% 1.51/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.51/0.60  fof(f46,plain,(
% 1.51/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f20])).
% 1.51/0.60  fof(f20,plain,(
% 1.51/0.60    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.51/0.60    inference(ennf_transformation,[],[f7])).
% 1.51/0.60  fof(f7,axiom,(
% 1.51/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.51/0.60  fof(f40,plain,(
% 1.51/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 1.51/0.60    inference(cnf_transformation,[],[f18])).
% 1.51/0.60  fof(f18,plain,(
% 1.51/0.60    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 1.51/0.60    inference(ennf_transformation,[],[f4])).
% 1.51/0.60  fof(f4,axiom,(
% 1.51/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 1.51/0.60  fof(f647,plain,(
% 1.51/0.60    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~r1_xboole_0(sK3,sK1)),
% 1.51/0.60    inference(resolution,[],[f373,f82])).
% 1.51/0.60  fof(f82,plain,(
% 1.51/0.60    ( ! [X4,X5,X3] : (~r1_tarski(k4_xboole_0(X4,X5),X3) | k1_xboole_0 = k4_xboole_0(X4,X5) | ~r1_xboole_0(X3,X4)) )),
% 1.51/0.60    inference(resolution,[],[f47,f37])).
% 1.51/0.60  fof(f37,plain,(
% 1.51/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f5])).
% 1.51/0.60  fof(f5,axiom,(
% 1.51/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.51/0.60  fof(f47,plain,(
% 1.51/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f22])).
% 1.51/0.60  fof(f22,plain,(
% 1.51/0.60    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.51/0.60    inference(flattening,[],[f21])).
% 1.51/0.60  fof(f21,plain,(
% 1.51/0.60    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.51/0.60    inference(ennf_transformation,[],[f11])).
% 1.51/0.60  fof(f11,axiom,(
% 1.51/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 1.51/0.60  fof(f373,plain,(
% 1.51/0.60    r1_tarski(k4_xboole_0(sK1,sK2),sK3)),
% 1.51/0.60    inference(superposition,[],[f164,f35])).
% 1.51/0.60  fof(f164,plain,(
% 1.51/0.60    ( ! [X3] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK1,X3),sK2),sK3)) )),
% 1.51/0.60    inference(resolution,[],[f59,f76])).
% 1.51/0.60  fof(f76,plain,(
% 1.51/0.60    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK0,sK1)) | r1_tarski(k4_xboole_0(X0,sK2),sK3)) )),
% 1.51/0.60    inference(superposition,[],[f46,f31])).
% 1.51/0.60  fof(f59,plain,(
% 1.51/0.60    ( ! [X4,X5,X3] : (r1_tarski(k4_xboole_0(X3,X4),k2_xboole_0(X5,X3))) )),
% 1.51/0.60    inference(resolution,[],[f45,f37])).
% 1.51/0.60  fof(f45,plain,(
% 1.51/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.51/0.60    inference(cnf_transformation,[],[f19])).
% 1.51/0.60  fof(f19,plain,(
% 1.51/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.51/0.60    inference(ennf_transformation,[],[f3])).
% 1.51/0.60  fof(f3,axiom,(
% 1.51/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.51/0.60  % SZS output end Proof for theBenchmark
% 1.51/0.60  % (28213)------------------------------
% 1.51/0.60  % (28213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.60  % (28213)Termination reason: Refutation
% 1.51/0.60  
% 1.51/0.60  % (28213)Memory used [KB]: 2302
% 1.51/0.60  % (28213)Time elapsed: 0.163 s
% 1.51/0.60  % (28213)------------------------------
% 1.51/0.60  % (28213)------------------------------
% 1.51/0.60  % (28205)Success in time 0.228 s
%------------------------------------------------------------------------------
