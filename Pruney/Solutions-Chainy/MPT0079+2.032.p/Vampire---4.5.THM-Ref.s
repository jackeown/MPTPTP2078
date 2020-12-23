%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:56 EST 2020

% Result     : Theorem 4.64s
% Output     : Refutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 235 expanded)
%              Number of leaves         :   12 (  68 expanded)
%              Depth                    :   22
%              Number of atoms          :  133 ( 410 expanded)
%              Number of equality atoms :   69 ( 248 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3631,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3630,f1660])).

fof(f1660,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f1632,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1632,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f56,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f37,f45])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f36,f38])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f3630,plain,(
    ~ r1_xboole_0(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f3605,f1107])).

fof(f1107,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f52,f877])).

fof(f877,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f876,f45])).

fof(f876,plain,(
    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f875,f36])).

fof(f875,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f796,f837])).

fof(f837,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f623,f827])).

fof(f827,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f793,f38])).

fof(f793,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f150,f52])).

fof(f150,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f35,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f623,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f23,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(forward_demodulation,[],[f83,f36])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f82,f45])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f78,f36])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f35,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f796,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f150,f50])).

fof(f50,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f37,f22])).

fof(f22,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f37,f36])).

fof(f3605,plain,(
    ~ r1_xboole_0(sK3,k4_xboole_0(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f24,f3427,f105])).

fof(f105,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_xboole_0(X11,X9)
      | r1_xboole_0(X11,k2_xboole_0(X9,X10))
      | ~ r1_xboole_0(X11,k4_xboole_0(X10,X9)) ) ),
    inference(superposition,[],[f29,f35])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f3427,plain,(
    ! [X0] : ~ r1_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f3404,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3404,plain,(
    ~ r1_xboole_0(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f3393,f32])).

fof(f3393,plain,(
    ~ r1_xboole_0(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f25,f22,f2439])).

fof(f2439,plain,(
    ! [X19] :
      ( ~ r1_xboole_0(X19,sK3)
      | k2_xboole_0(sK0,sK1) != k2_xboole_0(X19,sK3)
      | sK1 = X19 ) ),
    inference(backward_demodulation,[],[f185,f2417])).

fof(f2417,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f2247,f36])).

fof(f2247,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f2246,f36])).

fof(f2246,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f2184,f335])).

fof(f335,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f65,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f64,f38])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f59,f33])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f35,f37])).

fof(f2184,plain,(
    k2_xboole_0(sK3,sK1) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f463,f877])).

fof(f463,plain,(
    ! [X32] : k2_xboole_0(sK3,k2_xboole_0(X32,sK2)) = k2_xboole_0(X32,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f115,f22])).

fof(f115,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f33,f36])).

fof(f185,plain,(
    ! [X19] :
      ( k2_xboole_0(sK1,sK3) != k2_xboole_0(X19,sK3)
      | ~ r1_xboole_0(X19,sK3)
      | sK1 = X19 ) ),
    inference(resolution,[],[f26,f43])).

fof(f43,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f24,f32])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1)
      | ~ r1_xboole_0(X2,X1)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f25,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f24,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:44:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (26792)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (26785)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (26777)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.26/0.54  % (26772)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.26/0.54  % (26770)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.26/0.54  % (26775)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.26/0.54  % (26773)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.26/0.55  % (26776)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.55  % (26795)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.55  % (26784)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.38/0.55  % (26798)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.55  % (26788)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.38/0.55  % (26786)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.55  % (26796)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.38/0.55  % (26786)Refutation not found, incomplete strategy% (26786)------------------------------
% 1.38/0.55  % (26786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (26786)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (26786)Memory used [KB]: 10618
% 1.38/0.55  % (26786)Time elapsed: 0.137 s
% 1.38/0.55  % (26786)------------------------------
% 1.38/0.55  % (26786)------------------------------
% 1.38/0.56  % (26771)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.38/0.56  % (26790)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.56  % (26780)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.38/0.56  % (26789)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.38/0.56  % (26778)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.56  % (26799)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.56  % (26783)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.38/0.56  % (26781)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.56  % (26791)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.57  % (26793)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.38/0.57  % (26794)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.58  % (26774)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.38/0.58  % (26787)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.59  % (26779)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.59  % (26797)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.60  % (26782)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.45/0.75  % (26807)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.36/0.82  % (26772)Time limit reached!
% 3.36/0.82  % (26772)------------------------------
% 3.36/0.82  % (26772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.82  % (26772)Termination reason: Time limit
% 3.36/0.82  % (26772)Termination phase: Saturation
% 3.36/0.82  
% 3.36/0.82  % (26772)Memory used [KB]: 6524
% 3.36/0.82  % (26772)Time elapsed: 0.400 s
% 3.36/0.82  % (26772)------------------------------
% 3.36/0.82  % (26772)------------------------------
% 3.66/0.85  % (26794)Time limit reached!
% 3.66/0.85  % (26794)------------------------------
% 3.66/0.85  % (26794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.85  % (26794)Termination reason: Time limit
% 3.66/0.85  
% 3.66/0.85  % (26794)Memory used [KB]: 12537
% 3.66/0.85  % (26794)Time elapsed: 0.429 s
% 3.66/0.85  % (26794)------------------------------
% 3.66/0.85  % (26794)------------------------------
% 3.66/0.92  % (26784)Time limit reached!
% 3.66/0.92  % (26784)------------------------------
% 3.66/0.92  % (26784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.92  % (26799)Time limit reached!
% 3.66/0.92  % (26799)------------------------------
% 3.66/0.92  % (26799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.93  % (26776)Time limit reached!
% 4.26/0.93  % (26776)------------------------------
% 4.26/0.93  % (26776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.93  % (26784)Termination reason: Time limit
% 4.26/0.93  % (26784)Termination phase: Saturation
% 4.26/0.93  
% 4.26/0.93  % (26784)Memory used [KB]: 3837
% 4.26/0.93  % (26784)Time elapsed: 0.500 s
% 4.26/0.93  % (26784)------------------------------
% 4.26/0.93  % (26784)------------------------------
% 4.26/0.94  % (26799)Termination reason: Time limit
% 4.26/0.94  
% 4.26/0.94  % (26799)Memory used [KB]: 2046
% 4.26/0.94  % (26799)Time elapsed: 0.509 s
% 4.26/0.94  % (26799)------------------------------
% 4.26/0.94  % (26799)------------------------------
% 4.26/0.95  % (26776)Termination reason: Time limit
% 4.26/0.95  % (26776)Termination phase: Saturation
% 4.26/0.95  
% 4.26/0.95  % (26776)Memory used [KB]: 15095
% 4.26/0.95  % (26776)Time elapsed: 0.500 s
% 4.26/0.95  % (26776)------------------------------
% 4.26/0.95  % (26776)------------------------------
% 4.26/0.96  % (26835)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.64/1.00  % (26836)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.64/1.03  % (26837)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.64/1.03  % (26838)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.64/1.03  % (26789)Refutation found. Thanks to Tanya!
% 4.64/1.03  % SZS status Theorem for theBenchmark
% 4.64/1.03  % SZS output start Proof for theBenchmark
% 4.64/1.03  fof(f3631,plain,(
% 4.64/1.03    $false),
% 4.64/1.03    inference(subsumption_resolution,[],[f3630,f1660])).
% 4.64/1.03  fof(f1660,plain,(
% 4.64/1.03    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 4.64/1.03    inference(unit_resulting_resolution,[],[f1632,f32])).
% 4.64/1.03  fof(f32,plain,(
% 4.64/1.03    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 4.64/1.03    inference(cnf_transformation,[],[f21])).
% 4.64/1.03  fof(f21,plain,(
% 4.64/1.03    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 4.64/1.03    inference(ennf_transformation,[],[f3])).
% 4.64/1.03  fof(f3,axiom,(
% 4.64/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 4.64/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 4.64/1.03  fof(f1632,plain,(
% 4.64/1.03    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 4.64/1.03    inference(unit_resulting_resolution,[],[f56,f41])).
% 4.64/1.03  fof(f41,plain,(
% 4.64/1.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.64/1.03    inference(definition_unfolding,[],[f30,f39])).
% 4.64/1.03  fof(f39,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.64/1.03    inference(cnf_transformation,[],[f9])).
% 4.64/1.03  fof(f9,axiom,(
% 4.64/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.64/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.64/1.03  fof(f30,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 4.64/1.03    inference(cnf_transformation,[],[f2])).
% 4.64/1.03  fof(f2,axiom,(
% 4.64/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.64/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 4.64/1.03  fof(f56,plain,(
% 4.64/1.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 4.64/1.03    inference(superposition,[],[f37,f45])).
% 4.64/1.03  fof(f45,plain,(
% 4.64/1.03    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 4.64/1.03    inference(superposition,[],[f36,f38])).
% 4.64/1.03  fof(f38,plain,(
% 4.64/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.64/1.03    inference(cnf_transformation,[],[f5])).
% 4.64/1.03  fof(f5,axiom,(
% 4.64/1.03    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.64/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 4.64/1.03  fof(f36,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.64/1.03    inference(cnf_transformation,[],[f1])).
% 4.64/1.03  fof(f1,axiom,(
% 4.64/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.64/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.64/1.03  fof(f37,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.64/1.03    inference(cnf_transformation,[],[f8])).
% 4.64/1.03  fof(f8,axiom,(
% 4.64/1.03    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.64/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 4.64/1.03  fof(f3630,plain,(
% 4.64/1.03    ~r1_xboole_0(sK3,k1_xboole_0)),
% 4.64/1.03    inference(forward_demodulation,[],[f3605,f1107])).
% 4.64/1.03  fof(f1107,plain,(
% 4.64/1.03    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 4.64/1.03    inference(superposition,[],[f52,f877])).
% 4.64/1.03  fof(f877,plain,(
% 4.64/1.03    sK1 = k2_xboole_0(sK1,sK2)),
% 4.64/1.03    inference(forward_demodulation,[],[f876,f45])).
% 4.64/1.03  fof(f876,plain,(
% 4.64/1.03    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK1,sK2)),
% 4.64/1.03    inference(forward_demodulation,[],[f875,f36])).
% 4.64/1.03  fof(f875,plain,(
% 4.64/1.03    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 4.64/1.03    inference(forward_demodulation,[],[f796,f837])).
% 4.64/1.03  fof(f837,plain,(
% 4.64/1.03    sK2 = k4_xboole_0(sK2,sK0)),
% 4.64/1.03    inference(backward_demodulation,[],[f623,f827])).
% 4.64/1.03  fof(f827,plain,(
% 4.64/1.03    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 4.64/1.03    inference(forward_demodulation,[],[f793,f38])).
% 4.64/1.03  fof(f793,plain,(
% 4.64/1.03    ( ! [X2,X3] : (k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 4.64/1.03    inference(superposition,[],[f150,f52])).
% 4.64/1.03  fof(f150,plain,(
% 4.64/1.03    ( ! [X4,X5,X3] : (k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) )),
% 4.64/1.03    inference(superposition,[],[f35,f34])).
% 4.64/1.03  fof(f34,plain,(
% 4.64/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.64/1.03    inference(cnf_transformation,[],[f7])).
% 4.64/1.03  fof(f7,axiom,(
% 4.64/1.03    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.64/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.64/1.03  fof(f35,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.64/1.03    inference(cnf_transformation,[],[f6])).
% 4.64/1.03  fof(f6,axiom,(
% 4.64/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.64/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.64/1.03  fof(f623,plain,(
% 4.64/1.03    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 4.64/1.03    inference(unit_resulting_resolution,[],[f23,f84])).
% 4.64/1.03  fof(f84,plain,(
% 4.64/1.03    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.64/1.03    inference(forward_demodulation,[],[f83,f36])).
% 4.64/1.03  fof(f83,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),X0) | ~r1_xboole_0(X0,X1)) )),
% 4.64/1.03    inference(forward_demodulation,[],[f82,f45])).
% 4.64/1.03  fof(f82,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 4.64/1.03    inference(forward_demodulation,[],[f78,f36])).
% 4.64/1.03  fof(f78,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 4.64/1.03    inference(superposition,[],[f35,f40])).
% 4.64/1.03  fof(f40,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 4.64/1.03    inference(definition_unfolding,[],[f31,f39])).
% 4.64/1.03  fof(f31,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.64/1.03    inference(cnf_transformation,[],[f2])).
% 4.64/1.03  fof(f23,plain,(
% 4.64/1.03    r1_xboole_0(sK2,sK0)),
% 4.64/1.03    inference(cnf_transformation,[],[f17])).
% 4.64/1.03  fof(f17,plain,(
% 4.64/1.03    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 4.64/1.03    inference(flattening,[],[f16])).
% 4.64/1.03  fof(f16,plain,(
% 4.64/1.03    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 4.64/1.03    inference(ennf_transformation,[],[f15])).
% 4.64/1.03  fof(f15,negated_conjecture,(
% 4.64/1.03    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 4.64/1.03    inference(negated_conjecture,[],[f14])).
% 4.64/1.03  fof(f14,conjecture,(
% 4.64/1.03    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 4.64/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 4.64/1.03  fof(f796,plain,(
% 4.64/1.03    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(sK2,sK0))),
% 4.64/1.03    inference(superposition,[],[f150,f50])).
% 4.64/1.03  fof(f50,plain,(
% 4.64/1.03    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 4.64/1.03    inference(superposition,[],[f37,f22])).
% 4.64/1.03  fof(f22,plain,(
% 4.64/1.03    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 4.64/1.03    inference(cnf_transformation,[],[f17])).
% 4.64/1.03  fof(f52,plain,(
% 4.64/1.03    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 4.64/1.03    inference(superposition,[],[f37,f36])).
% 4.64/1.03  fof(f3605,plain,(
% 4.64/1.03    ~r1_xboole_0(sK3,k4_xboole_0(sK2,sK1))),
% 4.64/1.03    inference(unit_resulting_resolution,[],[f24,f3427,f105])).
% 4.64/1.03  fof(f105,plain,(
% 4.64/1.03    ( ! [X10,X11,X9] : (~r1_xboole_0(X11,X9) | r1_xboole_0(X11,k2_xboole_0(X9,X10)) | ~r1_xboole_0(X11,k4_xboole_0(X10,X9))) )),
% 4.64/1.03    inference(superposition,[],[f29,f35])).
% 4.64/1.03  fof(f29,plain,(
% 4.64/1.03    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 4.64/1.03    inference(cnf_transformation,[],[f20])).
% 4.64/1.03  fof(f20,plain,(
% 4.64/1.03    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 4.64/1.03    inference(ennf_transformation,[],[f11])).
% 4.64/1.03  fof(f11,axiom,(
% 4.64/1.03    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 4.64/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 4.64/1.03  fof(f3427,plain,(
% 4.64/1.03    ( ! [X0] : (~r1_xboole_0(sK3,k2_xboole_0(X0,sK2))) )),
% 4.64/1.03    inference(unit_resulting_resolution,[],[f3404,f28])).
% 4.64/1.03  fof(f28,plain,(
% 4.64/1.03    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.64/1.03    inference(cnf_transformation,[],[f20])).
% 4.64/1.03  fof(f3404,plain,(
% 4.64/1.03    ~r1_xboole_0(sK3,sK2)),
% 4.64/1.03    inference(unit_resulting_resolution,[],[f3393,f32])).
% 4.64/1.03  fof(f3393,plain,(
% 4.64/1.03    ~r1_xboole_0(sK2,sK3)),
% 4.64/1.03    inference(unit_resulting_resolution,[],[f25,f22,f2439])).
% 4.64/1.03  fof(f2439,plain,(
% 4.64/1.03    ( ! [X19] : (~r1_xboole_0(X19,sK3) | k2_xboole_0(sK0,sK1) != k2_xboole_0(X19,sK3) | sK1 = X19) )),
% 4.64/1.03    inference(backward_demodulation,[],[f185,f2417])).
% 4.64/1.03  fof(f2417,plain,(
% 4.64/1.03    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)),
% 4.64/1.03    inference(superposition,[],[f2247,f36])).
% 4.64/1.03  fof(f2247,plain,(
% 4.64/1.03    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK1)),
% 4.64/1.03    inference(forward_demodulation,[],[f2246,f36])).
% 4.64/1.03  fof(f2246,plain,(
% 4.64/1.03    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK3,sK1)),
% 4.64/1.03    inference(forward_demodulation,[],[f2184,f335])).
% 4.64/1.03  fof(f335,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 4.64/1.03    inference(superposition,[],[f65,f33])).
% 4.64/1.03  fof(f33,plain,(
% 4.64/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.64/1.03    inference(cnf_transformation,[],[f10])).
% 4.64/1.03  fof(f10,axiom,(
% 4.64/1.03    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.64/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 4.64/1.03  fof(f65,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 4.64/1.03    inference(forward_demodulation,[],[f64,f38])).
% 4.64/1.03  fof(f64,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))) )),
% 4.64/1.03    inference(forward_demodulation,[],[f59,f33])).
% 4.64/1.03  fof(f59,plain,(
% 4.64/1.03    ( ! [X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) )),
% 4.64/1.03    inference(superposition,[],[f35,f37])).
% 4.64/1.03  fof(f2184,plain,(
% 4.64/1.03    k2_xboole_0(sK3,sK1) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 4.64/1.03    inference(superposition,[],[f463,f877])).
% 4.64/1.03  fof(f463,plain,(
% 4.64/1.03    ( ! [X32] : (k2_xboole_0(sK3,k2_xboole_0(X32,sK2)) = k2_xboole_0(X32,k2_xboole_0(sK0,sK1))) )),
% 4.64/1.03    inference(superposition,[],[f115,f22])).
% 4.64/1.03  fof(f115,plain,(
% 4.64/1.03    ( ! [X6,X7,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 4.64/1.03    inference(superposition,[],[f33,f36])).
% 4.64/1.03  fof(f185,plain,(
% 4.64/1.03    ( ! [X19] : (k2_xboole_0(sK1,sK3) != k2_xboole_0(X19,sK3) | ~r1_xboole_0(X19,sK3) | sK1 = X19) )),
% 4.64/1.03    inference(resolution,[],[f26,f43])).
% 4.64/1.03  fof(f43,plain,(
% 4.64/1.03    r1_xboole_0(sK1,sK3)),
% 4.64/1.03    inference(unit_resulting_resolution,[],[f24,f32])).
% 4.64/1.03  fof(f26,plain,(
% 4.64/1.03    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) | ~r1_xboole_0(X2,X1) | X0 = X2) )),
% 4.64/1.03    inference(cnf_transformation,[],[f19])).
% 4.64/1.03  fof(f19,plain,(
% 4.64/1.03    ! [X0,X1,X2] : (X0 = X2 | ~r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1))),
% 4.64/1.03    inference(flattening,[],[f18])).
% 4.64/1.03  fof(f18,plain,(
% 4.64/1.03    ! [X0,X1,X2] : (X0 = X2 | (~r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1)))),
% 4.64/1.03    inference(ennf_transformation,[],[f12])).
% 4.64/1.03  fof(f12,axiom,(
% 4.64/1.03    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 4.64/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).
% 4.64/1.03  fof(f25,plain,(
% 4.64/1.03    sK1 != sK2),
% 4.64/1.03    inference(cnf_transformation,[],[f17])).
% 4.64/1.03  fof(f24,plain,(
% 4.64/1.03    r1_xboole_0(sK3,sK1)),
% 4.64/1.03    inference(cnf_transformation,[],[f17])).
% 4.64/1.03  % SZS output end Proof for theBenchmark
% 4.64/1.03  % (26789)------------------------------
% 4.64/1.03  % (26789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.03  % (26789)Termination reason: Refutation
% 4.64/1.03  
% 4.64/1.03  % (26789)Memory used [KB]: 4989
% 4.64/1.03  % (26789)Time elapsed: 0.622 s
% 4.64/1.03  % (26789)------------------------------
% 4.64/1.03  % (26789)------------------------------
% 4.64/1.04  % (26769)Success in time 0.664 s
%------------------------------------------------------------------------------
