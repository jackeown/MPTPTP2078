%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 182 expanded)
%              Number of leaves         :   11 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  153 ( 710 expanded)
%              Number of equality atoms :   17 (  38 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f425,plain,(
    $false ),
    inference(subsumption_resolution,[],[f424,f26])).

fof(f26,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

fof(f424,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f418,f29])).

fof(f29,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f418,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f214,f203])).

fof(f203,plain,(
    r1_tarski(k7_relat_1(sK2,sK0),sK3) ),
    inference(superposition,[],[f95,f199])).

fof(f199,plain,(
    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(resolution,[],[f138,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f138,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,sK0) = k7_relat_1(k7_relat_1(X1,sK0),sK1) ) ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(f95,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k7_relat_1(sK2,X0),X1),sK3) ),
    inference(subsumption_resolution,[],[f94,f25])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(k7_relat_1(sK2,X0),X1),sK3)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f92,f74])).

fof(f74,plain,(
    ! [X1] : v1_relat_1(k7_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f73,f25])).

fof(f73,plain,(
    ! [X1] :
      ( v1_relat_1(k7_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f38,f68])).

fof(f68,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k1_setfam_1(k2_tarski(sK2,k7_relat_1(sK2,X0))) ),
    inference(resolution,[],[f50,f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k7_relat_1(X0,X1))) ) ),
    inference(forward_demodulation,[],[f49,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(k7_relat_1(X0,X1),X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f39,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f35,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

% (3817)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X0))
      | r1_tarski(k7_relat_1(k7_relat_1(sK2,X0),X1),sK3)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f88,f33])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK2)
      | ~ v1_relat_1(X0)
      | r1_tarski(k7_relat_1(X0,X1),sK3) ) ),
    inference(resolution,[],[f66,f27])).

fof(f27,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_tarski(X4,X5)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(X3,X4)
      | r1_tarski(k7_relat_1(X3,X6),X5) ) ),
    inference(resolution,[],[f46,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f46,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k7_relat_1(X2,X4),X3)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f37,f33])).

fof(f214,plain,(
    ! [X9] :
      ( ~ r1_tarski(k7_relat_1(sK2,sK0),X9)
      | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X9,sK1))
      | ~ v1_relat_1(X9) ) ),
    inference(subsumption_resolution,[],[f211,f74])).

fof(f211,plain,(
    ! [X9] :
      ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X9,sK1))
      | ~ r1_tarski(k7_relat_1(sK2,sK0),X9)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ) ),
    inference(superposition,[],[f34,f199])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:43:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (3820)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (3821)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (3814)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (3813)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (3825)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (3816)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (3822)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (3811)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (3819)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (3818)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (3828)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (3815)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (3825)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f425,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f424,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    v1_relat_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).
% 0.22/0.50  fof(f424,plain,(
% 0.22/0.50    ~v1_relat_1(sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f418,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f418,plain,(
% 0.22/0.50    r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 0.22/0.50    inference(resolution,[],[f214,f203])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    r1_tarski(k7_relat_1(sK2,sK0),sK3)),
% 0.22/0.50    inference(superposition,[],[f95,f199])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.50    inference(resolution,[],[f138,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    v1_relat_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ( ! [X1] : (~v1_relat_1(X1) | k7_relat_1(X1,sK0) = k7_relat_1(k7_relat_1(X1,sK0),sK1)) )),
% 0.22/0.50    inference(resolution,[],[f36,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    r1_tarski(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(sK2,X0),X1),sK3)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f94,f25])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(sK2,X0),X1),sK3) | ~v1_relat_1(sK2)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f92,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X1] : (v1_relat_1(k7_relat_1(sK2,X1))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f73,f25])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X1] : (v1_relat_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 0.22/0.50    inference(superposition,[],[f38,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0] : (k7_relat_1(sK2,X0) = k1_setfam_1(k2_tarski(sK2,k7_relat_1(sK2,X0)))) )),
% 0.22/0.50    inference(resolution,[],[f50,f25])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k7_relat_1(X0,X1)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f49,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(k7_relat_1(X0,X1),X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f39,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.22/0.50    inference(definition_unfolding,[],[f35,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  % (3817)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f32,f31])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(sK2,X0)) | r1_tarski(k7_relat_1(k7_relat_1(sK2,X0),X1),sK3) | ~v1_relat_1(sK2)) )),
% 0.22/0.50    inference(resolution,[],[f88,f33])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,sK2) | ~v1_relat_1(X0) | r1_tarski(k7_relat_1(X0,X1),sK3)) )),
% 0.22/0.50    inference(resolution,[],[f66,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    r1_tarski(sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X6,X4,X5,X3] : (~r1_tarski(X4,X5) | ~v1_relat_1(X3) | ~r1_tarski(X3,X4) | r1_tarski(k7_relat_1(X3,X6),X5)) )),
% 0.22/0.50    inference(resolution,[],[f46,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(X2,X4),X3) | ~r1_tarski(X2,X3) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(resolution,[],[f37,f33])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    ( ! [X9] : (~r1_tarski(k7_relat_1(sK2,sK0),X9) | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X9,sK1)) | ~v1_relat_1(X9)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f211,f74])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    ( ! [X9] : (r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X9,sK1)) | ~r1_tarski(k7_relat_1(sK2,sK0),X9) | ~v1_relat_1(X9) | ~v1_relat_1(k7_relat_1(sK2,sK0))) )),
% 0.22/0.50    inference(superposition,[],[f34,f199])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (3825)------------------------------
% 0.22/0.50  % (3825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3825)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (3825)Memory used [KB]: 6524
% 0.22/0.50  % (3825)Time elapsed: 0.062 s
% 0.22/0.50  % (3825)------------------------------
% 0.22/0.50  % (3825)------------------------------
% 0.22/0.50  % (3812)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (3810)Success in time 0.141 s
%------------------------------------------------------------------------------
