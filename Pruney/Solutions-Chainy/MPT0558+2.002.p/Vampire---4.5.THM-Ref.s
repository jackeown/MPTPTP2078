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
% DateTime   : Thu Dec  3 12:49:56 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 109 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :  132 ( 248 expanded)
%              Number of equality atoms :   40 (  78 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1203,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1201,f25])).

fof(f25,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f1201,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f412,f1197])).

fof(f1197,plain,(
    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(superposition,[],[f1056,f140])).

fof(f140,plain,(
    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f131,f40])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,(
    ! [X18] :
      ( ~ r1_tarski(k2_relat_1(sK0),X18)
      | sK0 = k5_relat_1(sK0,k6_relat_1(X18)) ) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f1056,plain,(
    ! [X4] : k5_relat_1(sK0,k7_relat_1(sK1,X4)) = k5_relat_1(k5_relat_1(sK0,k6_relat_1(X4)),sK1) ),
    inference(forward_demodulation,[],[f1044,f46])).

fof(f46,plain,(
    ! [X6] : k7_relat_1(sK1,X6) = k5_relat_1(k6_relat_1(X6),sK1) ),
    inference(resolution,[],[f33,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f1044,plain,(
    ! [X4] : k5_relat_1(k5_relat_1(sK0,k6_relat_1(X4)),sK1) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(X4),sK1)) ),
    inference(resolution,[],[f799,f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f799,plain,(
    ! [X24] :
      ( ~ v1_relat_1(X24)
      | k5_relat_1(k5_relat_1(sK0,X24),sK1) = k5_relat_1(sK0,k5_relat_1(X24,sK1)) ) ),
    inference(resolution,[],[f349,f26])).

fof(f349,plain,(
    ! [X28,X27] :
      ( ~ v1_relat_1(X28)
      | ~ v1_relat_1(X27)
      | k5_relat_1(k5_relat_1(X28,X27),sK1) = k5_relat_1(X28,k5_relat_1(X27,sK1)) ) ),
    inference(resolution,[],[f32,f24])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f412,plain,(
    k9_relat_1(sK1,k2_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0)))) ),
    inference(resolution,[],[f201,f26])).

fof(f201,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X1,k7_relat_1(sK1,k2_relat_1(X1)))) = k9_relat_1(sK1,k2_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f200,f60])).

fof(f60,plain,(
    ! [X10] : k2_relat_1(k7_relat_1(sK1,X10)) = k9_relat_1(sK1,X10) ),
    inference(resolution,[],[f34,f24])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f200,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X1,k7_relat_1(sK1,k2_relat_1(X1)))) = k2_relat_1(k7_relat_1(sK1,k2_relat_1(X1))) ) ),
    inference(subsumption_resolution,[],[f184,f53])).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(subsumption_resolution,[],[f52,f27])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(k7_relat_1(sK1,X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f51,f24])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(k7_relat_1(sK1,X0))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f36,f46])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f184,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(X1)))
      | k2_relat_1(k5_relat_1(X1,k7_relat_1(sK1,k2_relat_1(X1)))) = k2_relat_1(k7_relat_1(sK1,k2_relat_1(X1))) ) ),
    inference(resolution,[],[f31,f97])).

fof(f97,plain,(
    ! [X7] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X7)),X7) ),
    inference(forward_demodulation,[],[f96,f28])).

fof(f28,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f96,plain,(
    ! [X7] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X7)),k1_relat_1(k6_relat_1(X7))) ),
    inference(subsumption_resolution,[],[f95,f27])).

fof(f95,plain,(
    ! [X7] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X7)),k1_relat_1(k6_relat_1(X7)))
      | ~ v1_relat_1(k6_relat_1(X7)) ) ),
    inference(subsumption_resolution,[],[f81,f24])).

fof(f81,plain,(
    ! [X7] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X7)),k1_relat_1(k6_relat_1(X7)))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(k6_relat_1(X7)) ) ),
    inference(superposition,[],[f30,f46])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:02:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (15195)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (15185)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (15184)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.53  % (15183)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (15193)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.54  % (15182)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.54  % (15201)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.55  % (15192)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.55  % (15203)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.55  % (15191)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.55  % (15198)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.55  % (15202)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.55  % (15208)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.55  % (15186)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.55  % (15189)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.55  % (15187)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.56  % (15199)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.56  % (15200)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.58  % (15190)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.58  % (15196)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.58  % (15205)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.59  % (15197)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.59  % (15204)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.60  % (15206)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.60  % (15188)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.61  % (15207)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 2.72/0.72  % (15191)Refutation not found, incomplete strategy% (15191)------------------------------
% 2.72/0.72  % (15191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.72/0.74  % (15202)Refutation found. Thanks to Tanya!
% 2.72/0.74  % SZS status Theorem for theBenchmark
% 2.72/0.74  % (15191)Termination reason: Refutation not found, incomplete strategy
% 2.72/0.74  
% 2.72/0.74  % (15191)Memory used [KB]: 6012
% 2.72/0.74  % (15191)Time elapsed: 0.307 s
% 2.72/0.74  % (15191)------------------------------
% 2.72/0.74  % (15191)------------------------------
% 2.72/0.76  % SZS output start Proof for theBenchmark
% 2.72/0.76  fof(f1203,plain,(
% 2.72/0.76    $false),
% 2.72/0.76    inference(subsumption_resolution,[],[f1201,f25])).
% 2.72/0.76  fof(f25,plain,(
% 2.72/0.76    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))),
% 2.72/0.76    inference(cnf_transformation,[],[f13])).
% 2.72/0.76  fof(f13,plain,(
% 2.72/0.76    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.72/0.76    inference(ennf_transformation,[],[f12])).
% 2.72/0.76  fof(f12,negated_conjecture,(
% 2.72/0.76    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 2.72/0.76    inference(negated_conjecture,[],[f11])).
% 2.72/0.76  fof(f11,conjecture,(
% 2.72/0.76    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 2.72/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 2.72/0.76  fof(f1201,plain,(
% 2.72/0.76    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))),
% 2.72/0.76    inference(backward_demodulation,[],[f412,f1197])).
% 2.72/0.76  fof(f1197,plain,(
% 2.72/0.76    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0)))),
% 2.72/0.76    inference(superposition,[],[f1056,f140])).
% 2.72/0.76  fof(f140,plain,(
% 2.72/0.76    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 2.72/0.76    inference(resolution,[],[f131,f40])).
% 2.72/0.76  fof(f40,plain,(
% 2.72/0.76    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.72/0.76    inference(equality_resolution,[],[f38])).
% 2.72/0.76  fof(f38,plain,(
% 2.72/0.76    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.72/0.76    inference(cnf_transformation,[],[f1])).
% 2.72/0.76  fof(f1,axiom,(
% 2.72/0.76    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.72/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.72/0.76  fof(f131,plain,(
% 2.72/0.76    ( ! [X18] : (~r1_tarski(k2_relat_1(sK0),X18) | sK0 = k5_relat_1(sK0,k6_relat_1(X18))) )),
% 2.72/0.76    inference(resolution,[],[f35,f26])).
% 2.72/0.76  fof(f26,plain,(
% 2.72/0.76    v1_relat_1(sK0)),
% 2.72/0.76    inference(cnf_transformation,[],[f13])).
% 2.72/0.76  fof(f35,plain,(
% 2.72/0.76    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 2.72/0.76    inference(cnf_transformation,[],[f21])).
% 2.72/0.76  fof(f21,plain,(
% 2.72/0.76    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.72/0.76    inference(flattening,[],[f20])).
% 2.72/0.76  fof(f20,plain,(
% 2.72/0.76    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.72/0.76    inference(ennf_transformation,[],[f9])).
% 2.72/0.76  fof(f9,axiom,(
% 2.72/0.76    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.72/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 2.72/0.76  fof(f1056,plain,(
% 2.72/0.76    ( ! [X4] : (k5_relat_1(sK0,k7_relat_1(sK1,X4)) = k5_relat_1(k5_relat_1(sK0,k6_relat_1(X4)),sK1)) )),
% 2.72/0.76    inference(forward_demodulation,[],[f1044,f46])).
% 2.72/0.76  fof(f46,plain,(
% 2.72/0.76    ( ! [X6] : (k7_relat_1(sK1,X6) = k5_relat_1(k6_relat_1(X6),sK1)) )),
% 2.72/0.76    inference(resolution,[],[f33,f24])).
% 2.72/0.76  fof(f24,plain,(
% 2.72/0.76    v1_relat_1(sK1)),
% 2.72/0.76    inference(cnf_transformation,[],[f13])).
% 2.72/0.76  fof(f33,plain,(
% 2.72/0.76    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.72/0.76    inference(cnf_transformation,[],[f18])).
% 2.72/0.76  fof(f18,plain,(
% 2.72/0.76    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.72/0.76    inference(ennf_transformation,[],[f10])).
% 2.72/0.76  fof(f10,axiom,(
% 2.72/0.76    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.72/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.72/0.76  fof(f1044,plain,(
% 2.72/0.76    ( ! [X4] : (k5_relat_1(k5_relat_1(sK0,k6_relat_1(X4)),sK1) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(X4),sK1))) )),
% 2.72/0.76    inference(resolution,[],[f799,f27])).
% 2.72/0.76  fof(f27,plain,(
% 2.72/0.76    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.72/0.76    inference(cnf_transformation,[],[f3])).
% 2.72/0.76  fof(f3,axiom,(
% 2.72/0.76    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.72/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 2.72/0.76  fof(f799,plain,(
% 2.72/0.76    ( ! [X24] : (~v1_relat_1(X24) | k5_relat_1(k5_relat_1(sK0,X24),sK1) = k5_relat_1(sK0,k5_relat_1(X24,sK1))) )),
% 2.72/0.76    inference(resolution,[],[f349,f26])).
% 2.72/0.76  fof(f349,plain,(
% 2.72/0.76    ( ! [X28,X27] : (~v1_relat_1(X28) | ~v1_relat_1(X27) | k5_relat_1(k5_relat_1(X28,X27),sK1) = k5_relat_1(X28,k5_relat_1(X27,sK1))) )),
% 2.72/0.76    inference(resolution,[],[f32,f24])).
% 2.72/0.76  fof(f32,plain,(
% 2.72/0.76    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 2.72/0.76    inference(cnf_transformation,[],[f17])).
% 2.72/0.76  fof(f17,plain,(
% 2.72/0.76    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.72/0.76    inference(ennf_transformation,[],[f7])).
% 2.72/0.76  fof(f7,axiom,(
% 2.72/0.76    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.72/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.72/0.76  fof(f412,plain,(
% 2.72/0.76    k9_relat_1(sK1,k2_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0))))),
% 2.72/0.76    inference(resolution,[],[f201,f26])).
% 2.72/0.76  fof(f201,plain,(
% 2.72/0.76    ( ! [X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X1,k7_relat_1(sK1,k2_relat_1(X1)))) = k9_relat_1(sK1,k2_relat_1(X1))) )),
% 2.72/0.76    inference(forward_demodulation,[],[f200,f60])).
% 2.72/0.76  fof(f60,plain,(
% 2.72/0.76    ( ! [X10] : (k2_relat_1(k7_relat_1(sK1,X10)) = k9_relat_1(sK1,X10)) )),
% 2.72/0.76    inference(resolution,[],[f34,f24])).
% 2.72/0.76  fof(f34,plain,(
% 2.72/0.76    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.72/0.76    inference(cnf_transformation,[],[f19])).
% 2.72/0.76  fof(f19,plain,(
% 2.72/0.76    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.72/0.76    inference(ennf_transformation,[],[f4])).
% 2.72/0.76  fof(f4,axiom,(
% 2.72/0.76    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.72/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.72/0.76  fof(f200,plain,(
% 2.72/0.76    ( ! [X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X1,k7_relat_1(sK1,k2_relat_1(X1)))) = k2_relat_1(k7_relat_1(sK1,k2_relat_1(X1)))) )),
% 2.72/0.76    inference(subsumption_resolution,[],[f184,f53])).
% 2.72/0.76  fof(f53,plain,(
% 2.72/0.76    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 2.72/0.76    inference(subsumption_resolution,[],[f52,f27])).
% 2.72/0.76  fof(f52,plain,(
% 2.72/0.76    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.72/0.76    inference(subsumption_resolution,[],[f51,f24])).
% 2.72/0.76  fof(f51,plain,(
% 2.72/0.76    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.72/0.76    inference(superposition,[],[f36,f46])).
% 2.72/0.76  fof(f36,plain,(
% 2.72/0.76    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.72/0.76    inference(cnf_transformation,[],[f23])).
% 2.72/0.76  fof(f23,plain,(
% 2.72/0.76    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.72/0.76    inference(flattening,[],[f22])).
% 2.72/0.76  fof(f22,plain,(
% 2.72/0.76    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.72/0.76    inference(ennf_transformation,[],[f2])).
% 2.72/0.76  fof(f2,axiom,(
% 2.72/0.76    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.72/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.72/0.76  fof(f184,plain,(
% 2.72/0.76    ( ! [X1] : (~v1_relat_1(X1) | ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(X1))) | k2_relat_1(k5_relat_1(X1,k7_relat_1(sK1,k2_relat_1(X1)))) = k2_relat_1(k7_relat_1(sK1,k2_relat_1(X1)))) )),
% 2.72/0.76    inference(resolution,[],[f31,f97])).
% 2.72/0.76  fof(f97,plain,(
% 2.72/0.76    ( ! [X7] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X7)),X7)) )),
% 2.72/0.76    inference(forward_demodulation,[],[f96,f28])).
% 2.72/0.76  fof(f28,plain,(
% 2.72/0.76    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.72/0.76    inference(cnf_transformation,[],[f8])).
% 2.72/0.76  fof(f8,axiom,(
% 2.72/0.76    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.72/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.72/0.76  fof(f96,plain,(
% 2.72/0.76    ( ! [X7] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X7)),k1_relat_1(k6_relat_1(X7)))) )),
% 2.72/0.76    inference(subsumption_resolution,[],[f95,f27])).
% 2.72/0.76  fof(f95,plain,(
% 2.72/0.76    ( ! [X7] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X7)),k1_relat_1(k6_relat_1(X7))) | ~v1_relat_1(k6_relat_1(X7))) )),
% 2.72/0.76    inference(subsumption_resolution,[],[f81,f24])).
% 2.72/0.76  fof(f81,plain,(
% 2.72/0.76    ( ! [X7] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X7)),k1_relat_1(k6_relat_1(X7))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(X7))) )),
% 2.72/0.76    inference(superposition,[],[f30,f46])).
% 2.72/0.76  fof(f30,plain,(
% 2.72/0.76    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.72/0.76    inference(cnf_transformation,[],[f14])).
% 2.72/0.76  fof(f14,plain,(
% 2.72/0.76    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.72/0.76    inference(ennf_transformation,[],[f5])).
% 2.72/0.76  fof(f5,axiom,(
% 2.72/0.76    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 2.72/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 2.72/0.76  fof(f31,plain,(
% 2.72/0.76    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)) )),
% 2.72/0.76    inference(cnf_transformation,[],[f16])).
% 2.72/0.76  fof(f16,plain,(
% 2.72/0.76    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.72/0.76    inference(flattening,[],[f15])).
% 2.72/0.76  fof(f15,plain,(
% 2.72/0.76    ! [X0] : (! [X1] : ((k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.72/0.76    inference(ennf_transformation,[],[f6])).
% 2.72/0.76  fof(f6,axiom,(
% 2.72/0.76    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0))))),
% 2.72/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 2.72/0.76  % SZS output end Proof for theBenchmark
% 2.72/0.76  % (15202)------------------------------
% 2.72/0.76  % (15202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.72/0.76  % (15202)Termination reason: Refutation
% 2.72/0.76  
% 2.72/0.76  % (15202)Memory used [KB]: 3582
% 2.72/0.76  % (15202)Time elapsed: 0.322 s
% 2.72/0.76  % (15202)------------------------------
% 2.72/0.76  % (15202)------------------------------
% 2.72/0.76  % (15176)Success in time 0.403 s
%------------------------------------------------------------------------------
