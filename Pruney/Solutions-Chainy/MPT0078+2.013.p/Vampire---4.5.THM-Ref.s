%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:49 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 262 expanded)
%              Number of leaves         :   12 (  80 expanded)
%              Depth                    :   16
%              Number of atoms          :  112 ( 378 expanded)
%              Number of equality atoms :   69 ( 275 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1753,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1752,f23])).

fof(f23,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f1752,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f1751,f692])).

fof(f692,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(backward_demodulation,[],[f53,f668])).

fof(f668,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(backward_demodulation,[],[f117,f667])).

fof(f667,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(subsumption_resolution,[],[f649,f88])).

fof(f88,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f78,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f78,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f26,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f39,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f33,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f649,plain,(
    ! [X2] :
      ( k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,X2))
      | k2_xboole_0(k1_xboole_0,X2) = X2 ) ),
    inference(superposition,[],[f28,f178])).

fof(f178,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X3),X3) ),
    inference(superposition,[],[f74,f40])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f26,f32])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f117,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f53,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f53,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f29,f40])).

fof(f1751,plain,(
    sK2 = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1750,f688])).

fof(f688,plain,(
    sK2 = k2_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f622,f667])).

fof(f622,plain,(
    k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f621,f31])).

fof(f621,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f620,f31])).

fof(f620,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f611,f399])).

fof(f399,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f379,f88])).

fof(f379,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))
    | sK0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f81,f96])).

fof(f96,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f36,f73,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f73,plain,(
    v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f67,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f67,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f21,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f21,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f81,plain,(
    ! [X6,X8,X7] :
      ( k4_xboole_0(X6,k2_xboole_0(X7,X8)) != k4_xboole_0(X8,k4_xboole_0(X6,X7))
      | k4_xboole_0(X6,X7) = X8 ) ),
    inference(superposition,[],[f28,f26])).

fof(f611,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f224,f129])).

fof(f129,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f88,f31])).

fof(f224,plain,(
    ! [X18] : k2_xboole_0(sK2,k4_xboole_0(X18,sK1)) = k2_xboole_0(sK2,k4_xboole_0(X18,k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f83,f49])).

fof(f49,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f31,f20])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X14,X12,X13] : k2_xboole_0(X14,k4_xboole_0(X12,X13)) = k2_xboole_0(X14,k4_xboole_0(X12,k2_xboole_0(X13,X14))) ),
    inference(superposition,[],[f29,f26])).

fof(f1750,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f1693,f405])).

fof(f405,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f380,f88])).

fof(f380,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | sK2 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f81,f109])).

fof(f109,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f36,f104,f27])).

fof(f104,plain,(
    v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f68,f34])).

fof(f68,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f22,f38])).

fof(f22,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f1693,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f219,f133])).

fof(f133,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f88,f49])).

fof(f219,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X4,k4_xboole_0(X5,X3)) = k2_xboole_0(X4,k4_xboole_0(X5,k2_xboole_0(X4,X3))) ),
    inference(superposition,[],[f83,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (12237)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (12232)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (12233)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (12234)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (12253)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (12239)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (12252)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (12231)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (12244)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (12238)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (12230)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (12244)Refutation not found, incomplete strategy% (12244)------------------------------
% 0.21/0.54  % (12244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12244)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12244)Memory used [KB]: 1663
% 0.21/0.54  % (12244)Time elapsed: 0.093 s
% 0.21/0.54  % (12244)------------------------------
% 0.21/0.54  % (12244)------------------------------
% 0.21/0.54  % (12258)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (12258)Refutation not found, incomplete strategy% (12258)------------------------------
% 0.21/0.54  % (12258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12258)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12258)Memory used [KB]: 10618
% 0.21/0.54  % (12258)Time elapsed: 0.137 s
% 0.21/0.54  % (12258)------------------------------
% 0.21/0.54  % (12258)------------------------------
% 0.21/0.54  % (12255)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (12235)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (12236)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (12240)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (12259)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (12242)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (12248)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (12250)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (12242)Refutation not found, incomplete strategy% (12242)------------------------------
% 0.21/0.55  % (12242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12251)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (12242)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12242)Memory used [KB]: 10618
% 0.21/0.55  % (12242)Time elapsed: 0.151 s
% 0.21/0.55  % (12242)------------------------------
% 0.21/0.55  % (12242)------------------------------
% 0.21/0.55  % (12249)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (12256)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (12247)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (12240)Refutation not found, incomplete strategy% (12240)------------------------------
% 0.21/0.55  % (12240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12231)Refutation not found, incomplete strategy% (12231)------------------------------
% 0.21/0.55  % (12231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12231)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12231)Memory used [KB]: 1663
% 0.21/0.55  % (12231)Time elapsed: 0.143 s
% 0.21/0.55  % (12231)------------------------------
% 0.21/0.55  % (12231)------------------------------
% 0.21/0.56  % (12245)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (12257)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (12257)Refutation not found, incomplete strategy% (12257)------------------------------
% 0.21/0.56  % (12257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12257)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12257)Memory used [KB]: 6140
% 0.21/0.56  % (12257)Time elapsed: 0.153 s
% 0.21/0.56  % (12257)------------------------------
% 0.21/0.56  % (12257)------------------------------
% 0.21/0.56  % (12256)Refutation not found, incomplete strategy% (12256)------------------------------
% 0.21/0.56  % (12256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12243)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (12248)Refutation not found, incomplete strategy% (12248)------------------------------
% 0.21/0.56  % (12248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12240)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12240)Memory used [KB]: 10746
% 0.21/0.56  % (12240)Time elapsed: 0.148 s
% 0.21/0.56  % (12240)------------------------------
% 0.21/0.56  % (12240)------------------------------
% 0.21/0.56  % (12256)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12256)Memory used [KB]: 6268
% 0.21/0.56  % (12256)Time elapsed: 0.158 s
% 0.21/0.56  % (12256)------------------------------
% 0.21/0.56  % (12256)------------------------------
% 0.21/0.56  % (12248)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12248)Memory used [KB]: 1663
% 0.21/0.56  % (12248)Time elapsed: 0.159 s
% 0.21/0.56  % (12248)------------------------------
% 0.21/0.56  % (12248)------------------------------
% 1.55/0.57  % (12246)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.55/0.58  % (12241)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.55/0.58  % (12246)Refutation not found, incomplete strategy% (12246)------------------------------
% 1.55/0.58  % (12246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (12246)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (12246)Memory used [KB]: 10618
% 1.55/0.58  % (12246)Time elapsed: 0.146 s
% 1.55/0.58  % (12246)------------------------------
% 1.55/0.58  % (12246)------------------------------
% 1.82/0.59  % (12254)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.19/0.67  % (12233)Refutation not found, incomplete strategy% (12233)------------------------------
% 2.19/0.67  % (12233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (12233)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.67  
% 2.19/0.67  % (12233)Memory used [KB]: 6140
% 2.19/0.67  % (12233)Time elapsed: 0.237 s
% 2.19/0.67  % (12233)------------------------------
% 2.19/0.67  % (12233)------------------------------
% 2.19/0.67  % (12249)Refutation found. Thanks to Tanya!
% 2.19/0.67  % SZS status Theorem for theBenchmark
% 2.19/0.67  % SZS output start Proof for theBenchmark
% 2.19/0.67  fof(f1753,plain,(
% 2.19/0.67    $false),
% 2.19/0.67    inference(subsumption_resolution,[],[f1752,f23])).
% 2.19/0.67  fof(f23,plain,(
% 2.19/0.67    sK0 != sK2),
% 2.19/0.67    inference(cnf_transformation,[],[f16])).
% 2.19/0.67  fof(f16,plain,(
% 2.19/0.67    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 2.19/0.67    inference(flattening,[],[f15])).
% 2.19/0.67  fof(f15,plain,(
% 2.19/0.67    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 2.19/0.67    inference(ennf_transformation,[],[f13])).
% 2.19/0.67  fof(f13,negated_conjecture,(
% 2.19/0.67    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 2.19/0.67    inference(negated_conjecture,[],[f12])).
% 2.19/0.67  fof(f12,conjecture,(
% 2.19/0.67    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).
% 2.19/0.67  fof(f1752,plain,(
% 2.19/0.67    sK0 = sK2),
% 2.19/0.67    inference(forward_demodulation,[],[f1751,f692])).
% 2.19/0.67  fof(f692,plain,(
% 2.19/0.67    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.19/0.67    inference(backward_demodulation,[],[f53,f668])).
% 2.19/0.67  fof(f668,plain,(
% 2.19/0.67    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 2.19/0.67    inference(backward_demodulation,[],[f117,f667])).
% 2.19/0.67  fof(f667,plain,(
% 2.19/0.67    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) )),
% 2.19/0.67    inference(subsumption_resolution,[],[f649,f88])).
% 2.19/0.67  fof(f88,plain,(
% 2.19/0.67    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 2.19/0.67    inference(forward_demodulation,[],[f78,f29])).
% 2.19/0.67  fof(f29,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.19/0.67    inference(cnf_transformation,[],[f7])).
% 2.19/0.67  fof(f7,axiom,(
% 2.19/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.19/0.67  fof(f78,plain,(
% 2.19/0.67    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 2.19/0.67    inference(superposition,[],[f26,f40])).
% 2.19/0.67  fof(f40,plain,(
% 2.19/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.19/0.67    inference(forward_demodulation,[],[f39,f32])).
% 2.19/0.67  fof(f32,plain,(
% 2.19/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.19/0.67    inference(cnf_transformation,[],[f8])).
% 2.19/0.67  fof(f8,axiom,(
% 2.19/0.67    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.19/0.67  fof(f39,plain,(
% 2.19/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.19/0.67    inference(definition_unfolding,[],[f33,f30])).
% 2.19/0.67  fof(f30,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.19/0.67    inference(cnf_transformation,[],[f10])).
% 2.19/0.67  fof(f10,axiom,(
% 2.19/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.19/0.67  fof(f33,plain,(
% 2.19/0.67    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f5])).
% 2.19/0.67  fof(f5,axiom,(
% 2.19/0.67    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.19/0.67  fof(f26,plain,(
% 2.19/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.19/0.67    inference(cnf_transformation,[],[f9])).
% 2.19/0.67  fof(f9,axiom,(
% 2.19/0.67    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.19/0.67  fof(f649,plain,(
% 2.19/0.67    ( ! [X2] : (k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,X2)) | k2_xboole_0(k1_xboole_0,X2) = X2) )),
% 2.19/0.67    inference(superposition,[],[f28,f178])).
% 2.19/0.67  fof(f178,plain,(
% 2.19/0.67    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X3),X3)) )),
% 2.19/0.67    inference(superposition,[],[f74,f40])).
% 2.19/0.67  fof(f74,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 2.19/0.67    inference(superposition,[],[f26,f32])).
% 2.19/0.67  fof(f28,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 2.19/0.67    inference(cnf_transformation,[],[f19])).
% 2.19/0.67  fof(f19,plain,(
% 2.19/0.67    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 2.19/0.67    inference(ennf_transformation,[],[f6])).
% 2.19/0.67  fof(f6,axiom,(
% 2.19/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 2.19/0.67  fof(f117,plain,(
% 2.19/0.67    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(k1_xboole_0,X1)) )),
% 2.19/0.67    inference(superposition,[],[f53,f31])).
% 2.19/0.67  fof(f31,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f1])).
% 2.19/0.67  fof(f1,axiom,(
% 2.19/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.19/0.67  fof(f53,plain,(
% 2.19/0.67    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) )),
% 2.19/0.67    inference(superposition,[],[f29,f40])).
% 2.19/0.67  fof(f1751,plain,(
% 2.19/0.67    sK2 = k2_xboole_0(sK0,k1_xboole_0)),
% 2.19/0.67    inference(forward_demodulation,[],[f1750,f688])).
% 2.19/0.67  fof(f688,plain,(
% 2.19/0.67    sK2 = k2_xboole_0(sK0,sK2)),
% 2.19/0.67    inference(backward_demodulation,[],[f622,f667])).
% 2.19/0.67  fof(f622,plain,(
% 2.19/0.67    k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK0,sK2)),
% 2.19/0.67    inference(forward_demodulation,[],[f621,f31])).
% 2.19/0.67  fof(f621,plain,(
% 2.19/0.67    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK0,sK2)),
% 2.19/0.67    inference(forward_demodulation,[],[f620,f31])).
% 2.19/0.67  fof(f620,plain,(
% 2.19/0.67    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK0)),
% 2.19/0.67    inference(forward_demodulation,[],[f611,f399])).
% 2.19/0.67  fof(f399,plain,(
% 2.19/0.67    sK0 = k4_xboole_0(sK0,sK1)),
% 2.19/0.67    inference(subsumption_resolution,[],[f379,f88])).
% 2.19/0.67  fof(f379,plain,(
% 2.19/0.67    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) | sK0 = k4_xboole_0(sK0,sK1)),
% 2.19/0.67    inference(superposition,[],[f81,f96])).
% 2.19/0.67  fof(f96,plain,(
% 2.19/0.67    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.19/0.67    inference(unit_resulting_resolution,[],[f36,f73,f27])).
% 2.19/0.67  fof(f27,plain,(
% 2.19/0.67    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f18])).
% 2.19/0.67  fof(f18,plain,(
% 2.19/0.67    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.19/0.67    inference(ennf_transformation,[],[f11])).
% 2.19/0.67  fof(f11,axiom,(
% 2.19/0.67    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 2.19/0.67  fof(f73,plain,(
% 2.19/0.67    v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.19/0.67    inference(unit_resulting_resolution,[],[f67,f34])).
% 2.19/0.67  fof(f34,plain,(
% 2.19/0.67    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f2])).
% 2.19/0.67  fof(f2,axiom,(
% 2.19/0.67    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.19/0.67  fof(f67,plain,(
% 2.19/0.67    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) )),
% 2.19/0.67    inference(unit_resulting_resolution,[],[f21,f38])).
% 2.19/0.67  fof(f38,plain,(
% 2.19/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.19/0.67    inference(definition_unfolding,[],[f24,f30])).
% 2.19/0.67  fof(f24,plain,(
% 2.19/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f17])).
% 2.19/0.67  fof(f17,plain,(
% 2.19/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.19/0.67    inference(ennf_transformation,[],[f14])).
% 2.19/0.67  fof(f14,plain,(
% 2.19/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.19/0.67    inference(rectify,[],[f4])).
% 2.19/0.67  fof(f4,axiom,(
% 2.19/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.19/0.67  fof(f21,plain,(
% 2.19/0.67    r1_xboole_0(sK0,sK1)),
% 2.19/0.67    inference(cnf_transformation,[],[f16])).
% 2.19/0.67  fof(f36,plain,(
% 2.19/0.67    v1_xboole_0(k1_xboole_0)),
% 2.19/0.67    inference(cnf_transformation,[],[f3])).
% 2.19/0.67  fof(f3,axiom,(
% 2.19/0.67    v1_xboole_0(k1_xboole_0)),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.19/0.67  fof(f81,plain,(
% 2.19/0.67    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(X7,X8)) != k4_xboole_0(X8,k4_xboole_0(X6,X7)) | k4_xboole_0(X6,X7) = X8) )),
% 2.19/0.67    inference(superposition,[],[f28,f26])).
% 2.19/0.67  fof(f611,plain,(
% 2.19/0.67    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 2.19/0.67    inference(superposition,[],[f224,f129])).
% 2.19/0.67  fof(f129,plain,(
% 2.19/0.67    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X1))) )),
% 2.19/0.67    inference(superposition,[],[f88,f31])).
% 2.19/0.67  fof(f224,plain,(
% 2.19/0.67    ( ! [X18] : (k2_xboole_0(sK2,k4_xboole_0(X18,sK1)) = k2_xboole_0(sK2,k4_xboole_0(X18,k2_xboole_0(sK0,sK1)))) )),
% 2.19/0.67    inference(superposition,[],[f83,f49])).
% 2.19/0.67  fof(f49,plain,(
% 2.19/0.67    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)),
% 2.19/0.67    inference(superposition,[],[f31,f20])).
% 2.19/0.67  fof(f20,plain,(
% 2.19/0.67    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 2.19/0.67    inference(cnf_transformation,[],[f16])).
% 2.19/0.67  fof(f83,plain,(
% 2.19/0.67    ( ! [X14,X12,X13] : (k2_xboole_0(X14,k4_xboole_0(X12,X13)) = k2_xboole_0(X14,k4_xboole_0(X12,k2_xboole_0(X13,X14)))) )),
% 2.19/0.67    inference(superposition,[],[f29,f26])).
% 2.19/0.67  fof(f1750,plain,(
% 2.19/0.67    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK2)),
% 2.19/0.67    inference(forward_demodulation,[],[f1693,f405])).
% 2.19/0.67  fof(f405,plain,(
% 2.19/0.67    sK2 = k4_xboole_0(sK2,sK1)),
% 2.19/0.67    inference(subsumption_resolution,[],[f380,f88])).
% 2.19/0.67  fof(f380,plain,(
% 2.19/0.67    k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK1,sK2)) | sK2 = k4_xboole_0(sK2,sK1)),
% 2.19/0.67    inference(superposition,[],[f81,f109])).
% 2.19/0.67  fof(f109,plain,(
% 2.19/0.67    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 2.19/0.67    inference(unit_resulting_resolution,[],[f36,f104,f27])).
% 2.19/0.67  fof(f104,plain,(
% 2.19/0.67    v1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 2.19/0.67    inference(unit_resulting_resolution,[],[f68,f34])).
% 2.19/0.67  fof(f68,plain,(
% 2.19/0.67    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) )),
% 2.19/0.67    inference(unit_resulting_resolution,[],[f22,f38])).
% 2.19/0.67  fof(f22,plain,(
% 2.19/0.67    r1_xboole_0(sK2,sK1)),
% 2.19/0.67    inference(cnf_transformation,[],[f16])).
% 2.19/0.67  fof(f1693,plain,(
% 2.19/0.67    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 2.19/0.67    inference(superposition,[],[f219,f133])).
% 2.19/0.67  fof(f133,plain,(
% 2.19/0.67    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.19/0.67    inference(superposition,[],[f88,f49])).
% 2.19/0.67  fof(f219,plain,(
% 2.19/0.67    ( ! [X4,X5,X3] : (k2_xboole_0(X4,k4_xboole_0(X5,X3)) = k2_xboole_0(X4,k4_xboole_0(X5,k2_xboole_0(X4,X3)))) )),
% 2.19/0.67    inference(superposition,[],[f83,f31])).
% 2.19/0.67  % SZS output end Proof for theBenchmark
% 2.19/0.67  % (12249)------------------------------
% 2.19/0.67  % (12249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (12249)Termination reason: Refutation
% 2.19/0.67  
% 2.19/0.67  % (12249)Memory used [KB]: 3070
% 2.19/0.67  % (12249)Time elapsed: 0.240 s
% 2.19/0.67  % (12249)------------------------------
% 2.19/0.67  % (12249)------------------------------
% 2.19/0.67  % (12229)Success in time 0.311 s
%------------------------------------------------------------------------------
