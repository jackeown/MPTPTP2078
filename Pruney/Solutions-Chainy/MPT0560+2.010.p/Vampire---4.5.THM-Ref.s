%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 180 expanded)
%              Number of leaves         :   13 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  132 ( 343 expanded)
%              Number of equality atoms :   60 ( 153 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1209,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1208])).

fof(f1208,plain,(
    k9_relat_1(sK0,sK1) != k9_relat_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f184,f1203])).

fof(f1203,plain,(
    sK1 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f859,f141])).

fof(f141,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(X4,X3))
      | k3_xboole_0(X4,X3) = X3 ) ),
    inference(resolution,[],[f84,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f84,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(backward_demodulation,[],[f66,f83])).

fof(f83,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(forward_demodulation,[],[f79,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f79,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(k1_relat_1(k6_relat_1(X1)),X2) ),
    inference(resolution,[],[f48,f38])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f66,plain,(
    ! [X2,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(resolution,[],[f45,f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f859,plain,(
    r1_tarski(sK1,k3_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f601,f145])).

fof(f145,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f144,f39])).

fof(f144,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f83,f62])).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f61,f39])).

fof(f61,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f41,f38])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f601,plain,(
    ! [X3] : r1_tarski(k3_xboole_0(sK1,X3),k3_xboole_0(sK2,X3)) ),
    inference(superposition,[],[f84,f288])).

fof(f288,plain,(
    ! [X10] : k3_xboole_0(sK1,k3_xboole_0(sK2,X10)) = k3_xboole_0(sK1,X10) ),
    inference(superposition,[],[f135,f166])).

fof(f166,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f163,f39])).

fof(f163,plain,(
    k3_xboole_0(sK1,sK2) = k1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f83,f148])).

fof(f148,plain,(
    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2) ),
    inference(resolution,[],[f91,f36])).

fof(f36,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f91,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f89,f39])).

fof(f89,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f49,f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f135,plain,(
    ! [X14,X15,X16] : k3_xboole_0(k3_xboole_0(X14,X15),X16) = k3_xboole_0(X14,k3_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f134,f83])).

fof(f134,plain,(
    ! [X14,X15,X16] : k3_xboole_0(k3_xboole_0(X14,X15),X16) = k1_relat_1(k7_relat_1(k6_relat_1(X14),k3_xboole_0(X15,X16))) ),
    inference(forward_demodulation,[],[f133,f94])).

fof(f94,plain,(
    ! [X4,X2,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k7_relat_1(k6_relat_1(X2),k3_xboole_0(X3,X4)) ),
    inference(resolution,[],[f54,f38])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f133,plain,(
    ! [X14,X15,X16] : k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X14),X15),X16)) = k3_xboole_0(k3_xboole_0(X14,X15),X16) ),
    inference(forward_demodulation,[],[f123,f83])).

fof(f123,plain,(
    ! [X14,X15,X16] : k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X14),X15),X16)) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(X14),X15)),X16) ),
    inference(resolution,[],[f59,f48])).

fof(f59,plain,(
    ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(resolution,[],[f44,f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f184,plain,(
    k9_relat_1(sK0,sK1) != k9_relat_1(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f37,f102])).

fof(f102,plain,(
    ! [X4,X3] : k9_relat_1(k7_relat_1(sK0,X3),X4) = k9_relat_1(sK0,k3_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f99,f72])).

fof(f72,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    inference(resolution,[],[f46,f35])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f99,plain,(
    ! [X4,X3] : k9_relat_1(k7_relat_1(sK0,X3),X4) = k2_relat_1(k7_relat_1(sK0,k3_xboole_0(X3,X4))) ),
    inference(backward_demodulation,[],[f74,f93])).

fof(f93,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f54,f35])).

fof(f74,plain,(
    ! [X4,X3] : k2_relat_1(k7_relat_1(k7_relat_1(sK0,X3),X4)) = k9_relat_1(k7_relat_1(sK0,X3),X4) ),
    inference(resolution,[],[f46,f58])).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK0,X0)) ),
    inference(resolution,[],[f44,f35])).

fof(f37,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (22490)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (22483)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (22500)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (22487)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (22485)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (22493)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (22484)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (22502)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (22503)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (22505)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (22495)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (22499)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (22488)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (22510)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (22497)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (22509)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (22486)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (22492)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (22489)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (22512)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (22491)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (22507)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (22511)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (22504)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (22508)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (22501)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (22498)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (22496)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (22494)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (22506)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.57  % (22490)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f1209,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f1208])).
% 0.21/0.58  fof(f1208,plain,(
% 0.21/0.58    k9_relat_1(sK0,sK1) != k9_relat_1(sK0,sK1)),
% 0.21/0.58    inference(backward_demodulation,[],[f184,f1203])).
% 0.21/0.58  fof(f1203,plain,(
% 0.21/0.58    sK1 = k3_xboole_0(sK2,sK1)),
% 0.21/0.58    inference(resolution,[],[f859,f141])).
% 0.21/0.58  fof(f141,plain,(
% 0.21/0.58    ( ! [X4,X3] : (~r1_tarski(X3,k3_xboole_0(X4,X3)) | k3_xboole_0(X4,X3) = X3) )),
% 0.21/0.58    inference(resolution,[],[f84,f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.58    inference(flattening,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.58    inference(nnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X1,X2),X2)) )),
% 0.21/0.58    inference(backward_demodulation,[],[f66,f83])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f79,f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(k1_relat_1(k6_relat_1(X1)),X2)) )),
% 0.21/0.58    inference(resolution,[],[f48,f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    ( ! [X2,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)) )),
% 0.21/0.58    inference(resolution,[],[f45,f38])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.58  fof(f859,plain,(
% 0.21/0.58    r1_tarski(sK1,k3_xboole_0(sK2,sK1))),
% 0.21/0.58    inference(superposition,[],[f601,f145])).
% 0.21/0.58  fof(f145,plain,(
% 0.21/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.58    inference(forward_demodulation,[],[f144,f39])).
% 0.21/0.58  fof(f144,plain,(
% 0.21/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k3_xboole_0(X0,X0)) )),
% 0.21/0.58    inference(superposition,[],[f83,f62])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f61,f39])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 0.21/0.58    inference(resolution,[],[f41,f38])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.58  fof(f601,plain,(
% 0.21/0.58    ( ! [X3] : (r1_tarski(k3_xboole_0(sK1,X3),k3_xboole_0(sK2,X3))) )),
% 0.21/0.58    inference(superposition,[],[f84,f288])).
% 0.21/0.58  fof(f288,plain,(
% 0.21/0.58    ( ! [X10] : (k3_xboole_0(sK1,k3_xboole_0(sK2,X10)) = k3_xboole_0(sK1,X10)) )),
% 0.21/0.58    inference(superposition,[],[f135,f166])).
% 0.21/0.58  fof(f166,plain,(
% 0.21/0.58    sK1 = k3_xboole_0(sK1,sK2)),
% 0.21/0.58    inference(forward_demodulation,[],[f163,f39])).
% 0.21/0.58  fof(f163,plain,(
% 0.21/0.58    k3_xboole_0(sK1,sK2) = k1_relat_1(k6_relat_1(sK1))),
% 0.21/0.58    inference(superposition,[],[f83,f148])).
% 0.21/0.58  fof(f148,plain,(
% 0.21/0.58    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2)),
% 0.21/0.58    inference(resolution,[],[f91,f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    r1_tarski(sK1,sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f31,f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) => (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,negated_conjecture,(
% 0.21/0.58    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.21/0.58    inference(negated_conjecture,[],[f16])).
% 0.21/0.58  fof(f16,conjecture,(
% 0.21/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 0.21/0.58  fof(f91,plain,(
% 0.21/0.58    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f89,f39])).
% 0.21/0.58  fof(f89,plain,(
% 0.21/0.58    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 0.21/0.58    inference(resolution,[],[f49,f38])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.58    inference(flattening,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.58  fof(f135,plain,(
% 0.21/0.58    ( ! [X14,X15,X16] : (k3_xboole_0(k3_xboole_0(X14,X15),X16) = k3_xboole_0(X14,k3_xboole_0(X15,X16))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f134,f83])).
% 0.21/0.58  fof(f134,plain,(
% 0.21/0.58    ( ! [X14,X15,X16] : (k3_xboole_0(k3_xboole_0(X14,X15),X16) = k1_relat_1(k7_relat_1(k6_relat_1(X14),k3_xboole_0(X15,X16)))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f133,f94])).
% 0.21/0.58  fof(f94,plain,(
% 0.21/0.58    ( ! [X4,X2,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k7_relat_1(k6_relat_1(X2),k3_xboole_0(X3,X4))) )),
% 0.21/0.58    inference(resolution,[],[f54,f38])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.58  fof(f133,plain,(
% 0.21/0.58    ( ! [X14,X15,X16] : (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X14),X15),X16)) = k3_xboole_0(k3_xboole_0(X14,X15),X16)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f123,f83])).
% 0.21/0.58  fof(f123,plain,(
% 0.21/0.58    ( ! [X14,X15,X16] : (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X14),X15),X16)) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(X14),X15)),X16)) )),
% 0.21/0.58    inference(resolution,[],[f59,f48])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) )),
% 0.21/0.58    inference(resolution,[],[f44,f38])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.58  fof(f184,plain,(
% 0.21/0.58    k9_relat_1(sK0,sK1) != k9_relat_1(sK0,k3_xboole_0(sK2,sK1))),
% 0.21/0.58    inference(superposition,[],[f37,f102])).
% 0.21/0.58  fof(f102,plain,(
% 0.21/0.58    ( ! [X4,X3] : (k9_relat_1(k7_relat_1(sK0,X3),X4) = k9_relat_1(sK0,k3_xboole_0(X3,X4))) )),
% 0.21/0.58    inference(forward_demodulation,[],[f99,f72])).
% 0.21/0.58  fof(f72,plain,(
% 0.21/0.58    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) )),
% 0.21/0.58    inference(resolution,[],[f46,f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    v1_relat_1(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.58  fof(f99,plain,(
% 0.21/0.58    ( ! [X4,X3] : (k9_relat_1(k7_relat_1(sK0,X3),X4) = k2_relat_1(k7_relat_1(sK0,k3_xboole_0(X3,X4)))) )),
% 0.21/0.58    inference(backward_demodulation,[],[f74,f93])).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(resolution,[],[f54,f35])).
% 0.21/0.58  fof(f74,plain,(
% 0.21/0.58    ( ! [X4,X3] : (k2_relat_1(k7_relat_1(k7_relat_1(sK0,X3),X4)) = k9_relat_1(k7_relat_1(sK0,X3),X4)) )),
% 0.21/0.58    inference(resolution,[],[f46,f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ( ! [X0] : (v1_relat_1(k7_relat_1(sK0,X0))) )),
% 0.21/0.58    inference(resolution,[],[f44,f35])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (22490)------------------------------
% 0.21/0.58  % (22490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (22490)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (22490)Memory used [KB]: 2686
% 0.21/0.58  % (22490)Time elapsed: 0.164 s
% 0.21/0.58  % (22490)------------------------------
% 0.21/0.58  % (22490)------------------------------
% 0.21/0.58  % (22482)Success in time 0.225 s
%------------------------------------------------------------------------------
