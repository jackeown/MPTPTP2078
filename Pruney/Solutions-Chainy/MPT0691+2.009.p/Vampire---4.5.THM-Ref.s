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
% DateTime   : Thu Dec  3 12:53:45 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 264 expanded)
%              Number of leaves         :   15 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  132 ( 502 expanded)
%              Number of equality atoms :   61 ( 184 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(subsumption_resolution,[],[f220,f123])).

% (7377)Termination reason: Refutation not found, incomplete strategy

% (7377)Memory used [KB]: 10746
% (7377)Time elapsed: 0.173 s
% (7377)------------------------------
% (7377)------------------------------
fof(f123,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f73,f122])).

fof(f122,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f120,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f120,plain,(
    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k5_xboole_0(sK0,k1_setfam_1(k2_tarski(sK0,k1_xboole_0))) ),
    inference(superposition,[],[f54,f73])).

fof(f54,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f42,f40,f51,f51])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f73,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))) ),
    inference(unit_resulting_resolution,[],[f32,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f32,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f220,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f104,f219])).

fof(f219,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f218,f140])).

fof(f140,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f127,f122])).

fof(f127,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f62,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f62,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f31,f55])).

% (7371)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
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

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f218,plain,(
    k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f84,f216])).

fof(f216,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f213,f65])).

fof(f65,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK1,X0),X0) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f59,f31,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f213,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(superposition,[],[f83,f140])).

fof(f83,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f63,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f63,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f84,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f63,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f104,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f103,f61])).

fof(f61,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) ),
    inference(unit_resulting_resolution,[],[f31,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f50,f40])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f103,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) ),
    inference(unit_resulting_resolution,[],[f33,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f33,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (7354)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (7349)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (7374)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (7352)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.56  % (7351)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.56  % (7363)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.56  % (7359)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.56  % (7359)Refutation not found, incomplete strategy% (7359)------------------------------
% 0.20/0.56  % (7359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (7359)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (7359)Memory used [KB]: 10746
% 0.20/0.56  % (7359)Time elapsed: 0.143 s
% 0.20/0.56  % (7359)------------------------------
% 0.20/0.56  % (7359)------------------------------
% 0.20/0.56  % (7364)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.56  % (7367)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.56  % (7370)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (7376)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.57  % (7372)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.57  % (7355)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % (7360)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.57  % (7366)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.58  % (7356)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.58  % (7362)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.58  % (7375)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.58  % (7350)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.57/0.58  % (7358)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.57/0.58  % (7367)Refutation not found, incomplete strategy% (7367)------------------------------
% 1.57/0.58  % (7367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (7367)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  % (7377)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.57/0.58  
% 1.57/0.58  % (7367)Memory used [KB]: 1663
% 1.57/0.58  % (7367)Time elapsed: 0.154 s
% 1.57/0.58  % (7367)------------------------------
% 1.57/0.58  % (7367)------------------------------
% 1.57/0.59  % (7377)Refutation not found, incomplete strategy% (7377)------------------------------
% 1.57/0.59  % (7377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (7353)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.57/0.59  % (7361)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.57/0.59  % (7368)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.57/0.59  % (7360)Refutation found. Thanks to Tanya!
% 1.57/0.59  % SZS status Theorem for theBenchmark
% 1.57/0.59  % SZS output start Proof for theBenchmark
% 1.57/0.59  fof(f221,plain,(
% 1.57/0.59    $false),
% 1.57/0.59    inference(subsumption_resolution,[],[f220,f123])).
% 1.57/0.60  % (7377)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.60  
% 1.57/0.60  % (7377)Memory used [KB]: 10746
% 1.57/0.60  % (7377)Time elapsed: 0.173 s
% 1.57/0.60  % (7377)------------------------------
% 1.57/0.60  % (7377)------------------------------
% 1.57/0.60  fof(f123,plain,(
% 1.57/0.60    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 1.57/0.60    inference(backward_demodulation,[],[f73,f122])).
% 1.57/0.60  fof(f122,plain,(
% 1.57/0.60    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))),
% 1.57/0.60    inference(forward_demodulation,[],[f120,f52])).
% 1.57/0.60  fof(f52,plain,(
% 1.57/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 1.57/0.60    inference(definition_unfolding,[],[f34,f51])).
% 1.57/0.60  fof(f51,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.57/0.60    inference(definition_unfolding,[],[f41,f40])).
% 1.57/0.60  fof(f40,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f8])).
% 1.57/0.60  fof(f8,axiom,(
% 1.57/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.57/0.60  fof(f41,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f4])).
% 1.57/0.60  fof(f4,axiom,(
% 1.57/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.57/0.60  fof(f34,plain,(
% 1.57/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.60    inference(cnf_transformation,[],[f5])).
% 1.57/0.60  fof(f5,axiom,(
% 1.57/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.57/0.60  fof(f120,plain,(
% 1.57/0.60    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k5_xboole_0(sK0,k1_setfam_1(k2_tarski(sK0,k1_xboole_0)))),
% 1.57/0.60    inference(superposition,[],[f54,f73])).
% 1.57/0.60  fof(f54,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 1.57/0.60    inference(definition_unfolding,[],[f42,f40,f51,f51])).
% 1.57/0.60  fof(f42,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f6])).
% 1.57/0.60  fof(f6,axiom,(
% 1.57/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.57/0.60  fof(f73,plain,(
% 1.57/0.60    k1_xboole_0 = k5_xboole_0(sK0,k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))))),
% 1.57/0.60    inference(unit_resulting_resolution,[],[f32,f56])).
% 1.57/0.60  fof(f56,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.57/0.60    inference(definition_unfolding,[],[f49,f51])).
% 1.57/0.60  fof(f49,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f30])).
% 1.88/0.60  fof(f30,plain,(
% 1.88/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.88/0.60    inference(nnf_transformation,[],[f3])).
% 1.88/0.60  fof(f3,axiom,(
% 1.88/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.88/0.60  fof(f32,plain,(
% 1.88/0.60    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.88/0.60    inference(cnf_transformation,[],[f27])).
% 1.88/0.60  fof(f27,plain,(
% 1.88/0.60    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.88/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f26])).
% 1.88/0.60  fof(f26,plain,(
% 1.88/0.60    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.88/0.60    introduced(choice_axiom,[])).
% 1.88/0.60  fof(f19,plain,(
% 1.88/0.60    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.88/0.60    inference(flattening,[],[f18])).
% 1.88/0.60  fof(f18,plain,(
% 1.88/0.60    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.88/0.60    inference(ennf_transformation,[],[f16])).
% 1.88/0.60  fof(f16,negated_conjecture,(
% 1.88/0.60    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.88/0.60    inference(negated_conjecture,[],[f15])).
% 1.88/0.60  fof(f15,conjecture,(
% 1.88/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.88/0.60  fof(f220,plain,(
% 1.88/0.60    k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 1.88/0.60    inference(backward_demodulation,[],[f104,f219])).
% 1.88/0.60  fof(f219,plain,(
% 1.88/0.60    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 1.88/0.60    inference(forward_demodulation,[],[f218,f140])).
% 1.88/0.60  fof(f140,plain,(
% 1.88/0.60    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.88/0.60    inference(superposition,[],[f127,f122])).
% 1.88/0.60  fof(f127,plain,(
% 1.88/0.60    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) )),
% 1.88/0.60    inference(superposition,[],[f62,f39])).
% 1.88/0.60  fof(f39,plain,(
% 1.88/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.88/0.60    inference(cnf_transformation,[],[f7])).
% 1.88/0.60  fof(f7,axiom,(
% 1.88/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.88/0.60  fof(f62,plain,(
% 1.88/0.60    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) )),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f31,f55])).
% 1.88/0.60  % (7371)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.88/0.60  fof(f55,plain,(
% 1.88/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 1.88/0.60    inference(definition_unfolding,[],[f44,f40])).
% 1.88/0.60  fof(f44,plain,(
% 1.88/0.60    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.88/0.60    inference(cnf_transformation,[],[f24])).
% 1.88/0.60  fof(f24,plain,(
% 1.88/0.60    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.88/0.60    inference(ennf_transformation,[],[f13])).
% 1.88/0.60  fof(f13,axiom,(
% 1.88/0.60    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.88/0.60  fof(f31,plain,(
% 1.88/0.60    v1_relat_1(sK1)),
% 1.88/0.60    inference(cnf_transformation,[],[f27])).
% 1.88/0.60  fof(f218,plain,(
% 1.88/0.60    k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.88/0.60    inference(superposition,[],[f84,f216])).
% 1.88/0.60  fof(f216,plain,(
% 1.88/0.60    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 1.88/0.60    inference(forward_demodulation,[],[f213,f65])).
% 1.88/0.60  fof(f65,plain,(
% 1.88/0.60    ( ! [X0] : (k9_relat_1(k7_relat_1(sK1,X0),X0) = k9_relat_1(sK1,X0)) )),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f59,f31,f37])).
% 1.88/0.60  fof(f37,plain,(
% 1.88/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 1.88/0.60    inference(cnf_transformation,[],[f22])).
% 1.88/0.60  fof(f22,plain,(
% 1.88/0.60    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.88/0.60    inference(ennf_transformation,[],[f11])).
% 1.88/0.60  fof(f11,axiom,(
% 1.88/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 1.88/0.60  fof(f59,plain,(
% 1.88/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.88/0.60    inference(equality_resolution,[],[f46])).
% 1.88/0.60  fof(f46,plain,(
% 1.88/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.88/0.60    inference(cnf_transformation,[],[f29])).
% 1.88/0.60  fof(f29,plain,(
% 1.88/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.88/0.60    inference(flattening,[],[f28])).
% 1.88/0.60  fof(f28,plain,(
% 1.88/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.88/0.60    inference(nnf_transformation,[],[f2])).
% 1.88/0.60  fof(f2,axiom,(
% 1.88/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.88/0.60  fof(f213,plain,(
% 1.88/0.60    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 1.88/0.60    inference(superposition,[],[f83,f140])).
% 1.88/0.60  fof(f83,plain,(
% 1.88/0.60    ( ! [X0] : (k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k7_relat_1(sK1,X0))) )),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f63,f36])).
% 1.88/0.60  fof(f36,plain,(
% 1.88/0.60    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.88/0.60    inference(cnf_transformation,[],[f21])).
% 1.88/0.60  fof(f21,plain,(
% 1.88/0.60    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.88/0.60    inference(ennf_transformation,[],[f10])).
% 1.88/0.60  fof(f10,axiom,(
% 1.88/0.60    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.88/0.60  fof(f63,plain,(
% 1.88/0.60    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f31,f43])).
% 1.88/0.60  fof(f43,plain,(
% 1.88/0.60    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.88/0.60    inference(cnf_transformation,[],[f23])).
% 1.88/0.60  fof(f23,plain,(
% 1.88/0.60    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.88/0.60    inference(ennf_transformation,[],[f9])).
% 1.88/0.60  fof(f9,axiom,(
% 1.88/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.88/0.60  fof(f84,plain,(
% 1.88/0.60    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f63,f35])).
% 1.88/0.60  fof(f35,plain,(
% 1.88/0.60    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 1.88/0.60    inference(cnf_transformation,[],[f20])).
% 1.88/0.60  fof(f20,plain,(
% 1.88/0.60    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.88/0.60    inference(ennf_transformation,[],[f12])).
% 1.88/0.60  fof(f12,axiom,(
% 1.88/0.60    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.88/0.60  fof(f104,plain,(
% 1.88/0.60    k1_xboole_0 != k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)))),
% 1.88/0.60    inference(forward_demodulation,[],[f103,f61])).
% 1.88/0.60  fof(f61,plain,(
% 1.88/0.60    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1)))) )),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f31,f58])).
% 1.88/0.60  fof(f58,plain,(
% 1.88/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 1.88/0.60    inference(definition_unfolding,[],[f50,f40])).
% 1.88/0.60  fof(f50,plain,(
% 1.88/0.60    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.88/0.60    inference(cnf_transformation,[],[f25])).
% 1.88/0.60  fof(f25,plain,(
% 1.88/0.60    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.88/0.60    inference(ennf_transformation,[],[f14])).
% 1.88/0.60  fof(f14,axiom,(
% 1.88/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.88/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.88/0.60  fof(f103,plain,(
% 1.88/0.60    k1_xboole_0 != k5_xboole_0(sK0,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))))),
% 1.88/0.60    inference(unit_resulting_resolution,[],[f33,f57])).
% 1.88/0.60  fof(f57,plain,(
% 1.88/0.60    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | r1_tarski(X0,X1)) )),
% 1.88/0.60    inference(definition_unfolding,[],[f48,f51])).
% 1.88/0.60  fof(f48,plain,(
% 1.88/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.88/0.60    inference(cnf_transformation,[],[f30])).
% 1.88/0.60  fof(f33,plain,(
% 1.88/0.60    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.88/0.60    inference(cnf_transformation,[],[f27])).
% 1.88/0.60  % SZS output end Proof for theBenchmark
% 1.88/0.60  % (7360)------------------------------
% 1.88/0.60  % (7360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.60  % (7360)Termination reason: Refutation
% 1.88/0.60  
% 1.88/0.60  % (7360)Memory used [KB]: 6396
% 1.88/0.60  % (7360)Time elapsed: 0.155 s
% 1.88/0.60  % (7360)------------------------------
% 1.88/0.60  % (7360)------------------------------
% 1.88/0.61  % (7348)Success in time 0.244 s
%------------------------------------------------------------------------------
