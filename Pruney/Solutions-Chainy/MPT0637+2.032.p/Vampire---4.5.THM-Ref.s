%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 132 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  105 ( 214 expanded)
%              Number of equality atoms :   41 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f782,plain,(
    $false ),
    inference(resolution,[],[f522,f488])).

fof(f488,plain,(
    ~ r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f195,f222,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f222,plain,(
    ! [X4,X5] : r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(k3_xboole_0(X4,X5))) ),
    inference(superposition,[],[f79,f95])).

fof(f95,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f92,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f92,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(unit_resulting_resolution,[],[f40,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f53,f70])).

fof(f70,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(unit_resulting_resolution,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f40,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f195,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f29,f70])).

fof(f29,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f522,plain,(
    ! [X6,X5] : r1_tarski(k6_relat_1(k3_xboole_0(X5,X6)),k7_relat_1(k6_relat_1(X5),X6)) ),
    inference(superposition,[],[f168,f194])).

fof(f194,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f70,f113])).

fof(f113,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f109,f41])).

fof(f109,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f40,f46,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f168,plain,(
    ! [X2,X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f81,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f161,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X0,X2)) ),
    inference(backward_demodulation,[],[f85,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2)) ),
    inference(unit_resulting_resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f85,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f71,f70])).

fof(f71,plain,(
    ! [X2,X0,X1] : k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f50,f39])).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f40,f40,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f161,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(forward_demodulation,[],[f160,f70])).

fof(f160,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f127,f70])).

fof(f127,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) ),
    inference(unit_resulting_resolution,[],[f40,f40,f40,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f81,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f56,f70])).

fof(f56,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f50,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:44:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (29988)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (29972)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (29980)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (29969)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (29967)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (29965)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (29970)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (29971)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (29990)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (29966)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (29966)Refutation not found, incomplete strategy% (29966)------------------------------
% 0.21/0.53  % (29966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29966)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29966)Memory used [KB]: 1663
% 0.21/0.53  % (29966)Time elapsed: 0.115 s
% 0.21/0.53  % (29966)------------------------------
% 0.21/0.53  % (29966)------------------------------
% 0.21/0.53  % (29968)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (29977)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (29977)Refutation not found, incomplete strategy% (29977)------------------------------
% 0.21/0.54  % (29977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29977)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29977)Memory used [KB]: 10618
% 0.21/0.54  % (29977)Time elapsed: 0.134 s
% 0.21/0.54  % (29977)------------------------------
% 0.21/0.54  % (29977)------------------------------
% 0.21/0.54  % (29993)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (29983)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (29983)Refutation not found, incomplete strategy% (29983)------------------------------
% 0.21/0.54  % (29983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29983)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29983)Memory used [KB]: 1663
% 0.21/0.54  % (29983)Time elapsed: 0.128 s
% 0.21/0.54  % (29983)------------------------------
% 0.21/0.54  % (29983)------------------------------
% 0.21/0.54  % (29981)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (29994)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (29993)Refutation not found, incomplete strategy% (29993)------------------------------
% 0.21/0.54  % (29993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29993)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29993)Memory used [KB]: 10618
% 0.21/0.54  % (29993)Time elapsed: 0.130 s
% 0.21/0.54  % (29993)------------------------------
% 0.21/0.54  % (29993)------------------------------
% 0.21/0.54  % (29994)Refutation not found, incomplete strategy% (29994)------------------------------
% 0.21/0.54  % (29994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29994)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29994)Memory used [KB]: 1663
% 0.21/0.54  % (29994)Time elapsed: 0.001 s
% 0.21/0.54  % (29994)------------------------------
% 0.21/0.54  % (29994)------------------------------
% 0.21/0.54  % (29981)Refutation not found, incomplete strategy% (29981)------------------------------
% 0.21/0.54  % (29981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29981)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29981)Memory used [KB]: 10618
% 0.21/0.54  % (29981)Time elapsed: 0.129 s
% 0.21/0.54  % (29981)------------------------------
% 0.21/0.54  % (29981)------------------------------
% 0.21/0.54  % (29985)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (29982)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (29992)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (29986)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (29982)Refutation not found, incomplete strategy% (29982)------------------------------
% 0.21/0.54  % (29982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29982)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29982)Memory used [KB]: 1663
% 0.21/0.54  % (29982)Time elapsed: 0.128 s
% 0.21/0.54  % (29982)------------------------------
% 0.21/0.54  % (29982)------------------------------
% 0.21/0.54  % (29992)Refutation not found, incomplete strategy% (29992)------------------------------
% 0.21/0.54  % (29992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29992)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29992)Memory used [KB]: 6140
% 0.21/0.54  % (29992)Time elapsed: 0.127 s
% 0.21/0.54  % (29992)------------------------------
% 0.21/0.54  % (29992)------------------------------
% 0.21/0.54  % (29990)Refutation not found, incomplete strategy% (29990)------------------------------
% 0.21/0.54  % (29990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29989)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (29989)Refutation not found, incomplete strategy% (29989)------------------------------
% 0.21/0.55  % (29989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29989)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29989)Memory used [KB]: 10618
% 0.21/0.55  % (29989)Time elapsed: 0.138 s
% 0.21/0.55  % (29989)------------------------------
% 0.21/0.55  % (29989)------------------------------
% 0.21/0.55  % (29990)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29990)Memory used [KB]: 6140
% 0.21/0.55  % (29990)Time elapsed: 0.129 s
% 0.21/0.55  % (29990)------------------------------
% 0.21/0.55  % (29990)------------------------------
% 0.21/0.55  % (29984)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (29991)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (29974)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (29991)Refutation not found, incomplete strategy% (29991)------------------------------
% 0.21/0.55  % (29991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29991)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29991)Memory used [KB]: 6140
% 0.21/0.55  % (29991)Time elapsed: 0.138 s
% 0.21/0.55  % (29991)------------------------------
% 0.21/0.55  % (29991)------------------------------
% 0.21/0.55  % (29975)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (29976)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (29975)Refutation not found, incomplete strategy% (29975)------------------------------
% 0.21/0.55  % (29975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29975)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29975)Memory used [KB]: 10618
% 0.21/0.55  % (29975)Time elapsed: 0.142 s
% 0.21/0.55  % (29975)------------------------------
% 0.21/0.55  % (29975)------------------------------
% 0.21/0.55  % (29976)Refutation not found, incomplete strategy% (29976)------------------------------
% 0.21/0.55  % (29976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29976)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29976)Memory used [KB]: 6140
% 0.21/0.55  % (29976)Time elapsed: 0.141 s
% 0.21/0.55  % (29976)------------------------------
% 0.21/0.55  % (29976)------------------------------
% 0.21/0.55  % (29978)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (29973)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (29987)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (29979)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.59  % (29979)Refutation not found, incomplete strategy% (29979)------------------------------
% 0.21/0.59  % (29979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (29979)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (29979)Memory used [KB]: 1663
% 0.21/0.59  % (29979)Time elapsed: 0.165 s
% 0.21/0.59  % (29979)------------------------------
% 0.21/0.59  % (29979)------------------------------
% 0.21/0.60  % (29984)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f782,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(resolution,[],[f522,f488])).
% 0.21/0.60  fof(f488,plain,(
% 0.21/0.60    ~r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f195,f222,f45])).
% 0.21/0.60  fof(f45,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.60  fof(f222,plain,(
% 0.21/0.60    ( ! [X4,X5] : (r1_tarski(k7_relat_1(k6_relat_1(X4),X5),k6_relat_1(k3_xboole_0(X4,X5)))) )),
% 0.21/0.60    inference(superposition,[],[f79,f95])).
% 0.21/0.60  fof(f95,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f92,f41])).
% 0.21/0.60  fof(f41,plain,(
% 0.21/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f12])).
% 0.21/0.60  fof(f12,axiom,(
% 0.21/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.60  fof(f92,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f40,f33])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f10])).
% 0.21/0.60  fof(f10,axiom,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,axiom,(
% 0.21/0.60    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.60  fof(f79,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0))) )),
% 0.21/0.60    inference(backward_demodulation,[],[f53,f70])).
% 0.21/0.60  fof(f70,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f40,f39])).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f28])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f16])).
% 0.21/0.60  fof(f16,axiom,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.60  fof(f53,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0))) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f40,f37])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f27])).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f13])).
% 0.21/0.60  fof(f13,axiom,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 0.21/0.60  fof(f195,plain,(
% 0.21/0.60    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.60    inference(superposition,[],[f29,f70])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(cnf_transformation,[],[f19])).
% 0.21/0.60  fof(f19,plain,(
% 0.21/0.60    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f18])).
% 0.21/0.60  fof(f18,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.60    inference(negated_conjecture,[],[f17])).
% 0.21/0.60  fof(f17,conjecture,(
% 0.21/0.60    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.60  fof(f522,plain,(
% 0.21/0.60    ( ! [X6,X5] : (r1_tarski(k6_relat_1(k3_xboole_0(X5,X6)),k7_relat_1(k6_relat_1(X5),X6))) )),
% 0.21/0.60    inference(superposition,[],[f168,f194])).
% 0.21/0.60  fof(f194,plain,(
% 0.21/0.60    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.60    inference(superposition,[],[f70,f113])).
% 0.21/0.60  fof(f113,plain,(
% 0.21/0.60    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f109,f41])).
% 0.21/0.60  fof(f109,plain,(
% 0.21/0.60    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0))) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f40,f46,f36])).
% 0.21/0.60  fof(f36,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f26])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.60    inference(flattening,[],[f25])).
% 0.21/0.60  fof(f25,plain,(
% 0.21/0.60    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f14])).
% 0.21/0.60  fof(f14,axiom,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.60  fof(f46,plain,(
% 0.21/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.60    inference(equality_resolution,[],[f44])).
% 0.21/0.60  fof(f44,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f2])).
% 0.21/0.60  fof(f168,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)),k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.21/0.60    inference(backward_demodulation,[],[f81,f162])).
% 0.21/0.60  fof(f162,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f161,f124])).
% 0.21/0.60  fof(f124,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.60    inference(backward_demodulation,[],[f85,f117])).
% 0.21/0.60  fof(f117,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2))) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f40,f32])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f21])).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.60    inference(ennf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.60  fof(f85,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.21/0.60    inference(backward_demodulation,[],[f71,f70])).
% 0.21/0.60  fof(f71,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f50,f39])).
% 0.21/0.60  fof(f50,plain,(
% 0.21/0.60    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f40,f40,f35])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f24])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(flattening,[],[f23])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f7])).
% 0.21/0.60  fof(f7,axiom,(
% 0.21/0.60    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.60  fof(f161,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f160,f70])).
% 0.21/0.60  fof(f160,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f127,f70])).
% 0.21/0.60  fof(f127,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2))) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f40,f40,f40,f31])).
% 0.21/0.60  fof(f31,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f11])).
% 0.21/0.60  fof(f11,axiom,(
% 0.21/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.60  fof(f81,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)),k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.21/0.60    inference(backward_demodulation,[],[f56,f70])).
% 0.21/0.60  fof(f56,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f50,f37])).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (29984)------------------------------
% 0.21/0.60  % (29984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (29984)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (29984)Memory used [KB]: 2174
% 0.21/0.60  % (29984)Time elapsed: 0.192 s
% 0.21/0.60  % (29984)------------------------------
% 0.21/0.60  % (29984)------------------------------
% 0.21/0.60  % (29964)Success in time 0.229 s
%------------------------------------------------------------------------------
