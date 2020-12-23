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
% DateTime   : Thu Dec  3 12:49:57 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   56 (  96 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   15
%              Number of atoms          :  124 ( 221 expanded)
%              Number of equality atoms :   41 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1087,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1086,f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f1086,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f491,f1083])).

fof(f1083,plain,(
    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(superposition,[],[f1078,f88])).

fof(f88,plain,(
    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f84,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f84,plain,(
    ! [X5] :
      ( ~ r1_tarski(k2_relat_1(sK0),X5)
      | sK0 = k5_relat_1(sK0,k6_relat_1(X5)) ) ),
    inference(resolution,[],[f35,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f1078,plain,(
    ! [X0] : k5_relat_1(k5_relat_1(sK0,k6_relat_1(X0)),sK1) = k5_relat_1(sK0,k7_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f1072,f45])).

fof(f45,plain,(
    ! [X6] : k7_relat_1(sK1,X6) = k5_relat_1(k6_relat_1(X6),sK1) ),
    inference(resolution,[],[f33,f23])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f1072,plain,(
    ! [X0] : k5_relat_1(k5_relat_1(sK0,k6_relat_1(X0)),sK1) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(X0),sK1)) ),
    inference(resolution,[],[f1070,f26])).

fof(f26,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f1070,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k5_relat_1(k5_relat_1(sK0,X7),sK1) = k5_relat_1(sK0,k5_relat_1(X7,sK1)) ) ),
    inference(resolution,[],[f783,f25])).

fof(f783,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X9)
      | k5_relat_1(k5_relat_1(X10,X9),sK1) = k5_relat_1(X10,k5_relat_1(X9,sK1)) ) ),
    inference(resolution,[],[f31,f23])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f491,plain,(
    k9_relat_1(sK1,k2_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0)))) ),
    inference(resolution,[],[f483,f25])).

fof(f483,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,k7_relat_1(sK1,k2_relat_1(X0)))) = k9_relat_1(sK1,k2_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f466,f23])).

fof(f466,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,k7_relat_1(sK1,k2_relat_1(X0)))) = k9_relat_1(sK1,k2_relat_1(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f263,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f263,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X1,k7_relat_1(sK1,k2_relat_1(X1)))) = k9_relat_1(sK1,k2_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f245,f49])).

fof(f49,plain,(
    ! [X6] : k2_relat_1(k7_relat_1(sK1,X6)) = k9_relat_1(sK1,X6) ),
    inference(resolution,[],[f34,f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f245,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(X1)))
      | k2_relat_1(k5_relat_1(X1,k7_relat_1(sK1,k2_relat_1(X1)))) = k2_relat_1(k7_relat_1(sK1,k2_relat_1(X1))) ) ),
    inference(resolution,[],[f30,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),X1) ),
    inference(forward_demodulation,[],[f59,f27])).

fof(f27,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f59,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k6_relat_1(X1))) ),
    inference(subsumption_resolution,[],[f58,f26])).

fof(f58,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f52,f23])).

fof(f52,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f29,f45])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:17:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.50  % (8287)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.51  % (8280)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.52  % (8274)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.52  % (8282)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.52  % (8283)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.53  % (8267)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.53  % (8290)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.53  % (8268)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.53  % (8288)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.53  % (8273)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.53  % (8269)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.53  % (8265)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.54  % (8286)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.54  % (8271)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.54  % (8270)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.54  % (8284)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.54  % (8276)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.54  % (8275)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.55  % (8266)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.55  % (8279)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.55  % (8278)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.55  % (8272)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.55  % (8287)Refutation found. Thanks to Tanya!
% 0.23/0.55  % SZS status Theorem for theBenchmark
% 0.23/0.55  % SZS output start Proof for theBenchmark
% 0.23/0.55  fof(f1087,plain,(
% 0.23/0.55    $false),
% 0.23/0.55    inference(subsumption_resolution,[],[f1086,f24])).
% 0.23/0.55  fof(f24,plain,(
% 0.23/0.55    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.23/0.55    inference(cnf_transformation,[],[f13])).
% 0.23/0.55  fof(f13,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f12])).
% 0.23/0.55  fof(f12,negated_conjecture,(
% 0.23/0.55    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.23/0.55    inference(negated_conjecture,[],[f11])).
% 0.23/0.55  fof(f11,conjecture,(
% 0.23/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.23/0.55  fof(f1086,plain,(
% 0.23/0.55    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.23/0.55    inference(backward_demodulation,[],[f491,f1083])).
% 0.23/0.55  fof(f1083,plain,(
% 0.23/0.55    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0)))),
% 0.23/0.55    inference(superposition,[],[f1078,f88])).
% 0.23/0.55  fof(f88,plain,(
% 0.23/0.55    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.23/0.55    inference(resolution,[],[f84,f39])).
% 0.23/0.55  fof(f39,plain,(
% 0.23/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.55    inference(equality_resolution,[],[f37])).
% 0.23/0.55  fof(f37,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.55    inference(cnf_transformation,[],[f1])).
% 0.23/0.55  fof(f1,axiom,(
% 0.23/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.55  fof(f84,plain,(
% 0.23/0.55    ( ! [X5] : (~r1_tarski(k2_relat_1(sK0),X5) | sK0 = k5_relat_1(sK0,k6_relat_1(X5))) )),
% 0.23/0.55    inference(resolution,[],[f35,f25])).
% 0.23/0.55  fof(f25,plain,(
% 0.23/0.55    v1_relat_1(sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f13])).
% 0.23/0.55  fof(f35,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.23/0.55    inference(cnf_transformation,[],[f22])).
% 0.23/0.55  fof(f22,plain,(
% 0.23/0.55    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.55    inference(flattening,[],[f21])).
% 0.23/0.55  fof(f21,plain,(
% 0.23/0.55    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.55    inference(ennf_transformation,[],[f9])).
% 0.23/0.55  fof(f9,axiom,(
% 0.23/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.23/0.55  fof(f1078,plain,(
% 0.23/0.55    ( ! [X0] : (k5_relat_1(k5_relat_1(sK0,k6_relat_1(X0)),sK1) = k5_relat_1(sK0,k7_relat_1(sK1,X0))) )),
% 0.23/0.55    inference(forward_demodulation,[],[f1072,f45])).
% 0.23/0.55  fof(f45,plain,(
% 0.23/0.55    ( ! [X6] : (k7_relat_1(sK1,X6) = k5_relat_1(k6_relat_1(X6),sK1)) )),
% 0.23/0.55    inference(resolution,[],[f33,f23])).
% 0.23/0.55  fof(f23,plain,(
% 0.23/0.55    v1_relat_1(sK1)),
% 0.23/0.55    inference(cnf_transformation,[],[f13])).
% 0.23/0.55  fof(f33,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f19])).
% 0.23/0.55  fof(f19,plain,(
% 0.23/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.23/0.55    inference(ennf_transformation,[],[f10])).
% 0.23/0.55  fof(f10,axiom,(
% 0.23/0.55    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.23/0.55  fof(f1072,plain,(
% 0.23/0.55    ( ! [X0] : (k5_relat_1(k5_relat_1(sK0,k6_relat_1(X0)),sK1) = k5_relat_1(sK0,k5_relat_1(k6_relat_1(X0),sK1))) )),
% 0.23/0.55    inference(resolution,[],[f1070,f26])).
% 0.23/0.55  fof(f26,plain,(
% 0.23/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f2])).
% 0.23/0.55  fof(f2,axiom,(
% 0.23/0.55    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.23/0.55  fof(f1070,plain,(
% 0.23/0.55    ( ! [X7] : (~v1_relat_1(X7) | k5_relat_1(k5_relat_1(sK0,X7),sK1) = k5_relat_1(sK0,k5_relat_1(X7,sK1))) )),
% 0.23/0.55    inference(resolution,[],[f783,f25])).
% 0.23/0.55  fof(f783,plain,(
% 0.23/0.55    ( ! [X10,X9] : (~v1_relat_1(X10) | ~v1_relat_1(X9) | k5_relat_1(k5_relat_1(X10,X9),sK1) = k5_relat_1(X10,k5_relat_1(X9,sK1))) )),
% 0.23/0.55    inference(resolution,[],[f31,f23])).
% 0.23/0.55  fof(f31,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f17])).
% 0.23/0.55  fof(f17,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f7])).
% 0.23/0.55  fof(f7,axiom,(
% 0.23/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.23/0.55  fof(f491,plain,(
% 0.23/0.55    k9_relat_1(sK1,k2_relat_1(sK0)) = k2_relat_1(k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0))))),
% 0.23/0.55    inference(resolution,[],[f483,f25])).
% 0.23/0.55  fof(f483,plain,(
% 0.23/0.55    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,k7_relat_1(sK1,k2_relat_1(X0)))) = k9_relat_1(sK1,k2_relat_1(X0))) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f466,f23])).
% 0.23/0.55  fof(f466,plain,(
% 0.23/0.55    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,k7_relat_1(sK1,k2_relat_1(X0)))) = k9_relat_1(sK1,k2_relat_1(X0)) | ~v1_relat_1(sK1)) )),
% 0.23/0.55    inference(resolution,[],[f263,f32])).
% 0.23/0.55  fof(f32,plain,(
% 0.23/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f18])).
% 0.23/0.55  fof(f18,plain,(
% 0.23/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f3])).
% 0.23/0.55  fof(f3,axiom,(
% 0.23/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.23/0.55  fof(f263,plain,(
% 0.23/0.55    ( ! [X1] : (~v1_relat_1(k7_relat_1(sK1,k2_relat_1(X1))) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X1,k7_relat_1(sK1,k2_relat_1(X1)))) = k9_relat_1(sK1,k2_relat_1(X1))) )),
% 0.23/0.55    inference(forward_demodulation,[],[f245,f49])).
% 0.23/0.55  fof(f49,plain,(
% 0.23/0.55    ( ! [X6] : (k2_relat_1(k7_relat_1(sK1,X6)) = k9_relat_1(sK1,X6)) )),
% 0.23/0.55    inference(resolution,[],[f34,f23])).
% 0.23/0.55  fof(f34,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f20])).
% 0.23/0.55  fof(f20,plain,(
% 0.23/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.55    inference(ennf_transformation,[],[f4])).
% 0.23/0.55  fof(f4,axiom,(
% 0.23/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.23/0.55  fof(f245,plain,(
% 0.23/0.55    ( ! [X1] : (~v1_relat_1(X1) | ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(X1))) | k2_relat_1(k5_relat_1(X1,k7_relat_1(sK1,k2_relat_1(X1)))) = k2_relat_1(k7_relat_1(sK1,k2_relat_1(X1)))) )),
% 0.23/0.55    inference(resolution,[],[f30,f60])).
% 0.23/0.55  fof(f60,plain,(
% 0.23/0.55    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),X1)) )),
% 0.23/0.55    inference(forward_demodulation,[],[f59,f27])).
% 0.23/0.55  fof(f27,plain,(
% 0.23/0.55    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f8])).
% 0.23/0.55  fof(f8,axiom,(
% 0.23/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.23/0.55  fof(f59,plain,(
% 0.23/0.55    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k6_relat_1(X1)))) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f58,f26])).
% 0.23/0.55  fof(f58,plain,(
% 0.23/0.55    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f52,f23])).
% 0.23/0.55  fof(f52,plain,(
% 0.23/0.55    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X1)),k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.23/0.55    inference(superposition,[],[f29,f45])).
% 0.23/0.55  fof(f29,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f14])).
% 0.23/0.55  fof(f14,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f5])).
% 0.23/0.55  fof(f5,axiom,(
% 0.23/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 0.23/0.55  fof(f30,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f16])).
% 0.23/0.55  fof(f16,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(flattening,[],[f15])).
% 0.23/0.55  fof(f15,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : ((k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f6])).
% 0.23/0.55  fof(f6,axiom,(
% 0.23/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 0.23/0.55  % SZS output end Proof for theBenchmark
% 0.23/0.55  % (8287)------------------------------
% 0.23/0.55  % (8287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (8287)Termination reason: Refutation
% 0.23/0.55  
% 0.23/0.55  % (8287)Memory used [KB]: 12281
% 0.23/0.55  % (8287)Time elapsed: 0.078 s
% 0.23/0.55  % (8287)------------------------------
% 0.23/0.55  % (8287)------------------------------
% 0.23/0.55  % (8262)Success in time 0.183 s
%------------------------------------------------------------------------------
