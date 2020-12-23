%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:55 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   44 (  75 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 137 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(subsumption_resolution,[],[f170,f80])).

fof(f80,plain,(
    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0))) ),
    inference(resolution,[],[f76,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f76,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0))) ),
    inference(resolution,[],[f64,f35])).

fof(f35,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK0))
      | r1_tarski(X0,k1_relat_1(k2_xboole_0(sK1,sK0))) ) ),
    inference(superposition,[],[f28,f63])).

fof(f63,plain,(
    k1_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(resolution,[],[f38,f17])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(f38,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(k2_xboole_0(sK1,X2)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X2)) ) ),
    inference(resolution,[],[f15,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f170,plain,(
    k1_xboole_0 != k6_subset_1(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f169,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f169,plain,(
    k1_xboole_0 != k6_subset_1(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f107,f167])).

fof(f167,plain,(
    ! [X4] : k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X4))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X4))) ),
    inference(resolution,[],[f61,f17])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k2_xboole_0(sK1,k6_subset_1(X0,X1))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(X0,X1))) ) ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k6_subset_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f107,plain,(
    k1_xboole_0 != k6_subset_1(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) ),
    inference(superposition,[],[f42,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k2_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f27,f19,f19,f19])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f42,plain,(
    k1_xboole_0 != k6_subset_1(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f16,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:53:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (12678)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.47  % (12661)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (12668)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.32/0.54  % (12685)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.55  % (12659)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.32/0.55  % (12685)Refutation not found, incomplete strategy% (12685)------------------------------
% 1.32/0.55  % (12685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (12685)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (12685)Memory used [KB]: 10618
% 1.32/0.55  % (12685)Time elapsed: 0.099 s
% 1.32/0.55  % (12685)------------------------------
% 1.32/0.55  % (12685)------------------------------
% 1.32/0.55  % (12677)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.55  % (12683)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.50/0.55  % (12673)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.55  % (12655)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.50/0.56  % (12660)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.50/0.56  % (12670)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.50/0.56  % (12658)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.50/0.56  % (12656)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.50/0.56  % (12686)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.50/0.56  % (12666)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.56  % (12666)Refutation not found, incomplete strategy% (12666)------------------------------
% 1.50/0.56  % (12666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (12666)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (12666)Memory used [KB]: 10618
% 1.50/0.56  % (12666)Time elapsed: 0.148 s
% 1.50/0.56  % (12666)------------------------------
% 1.50/0.56  % (12666)------------------------------
% 1.50/0.56  % (12686)Refutation not found, incomplete strategy% (12686)------------------------------
% 1.50/0.56  % (12686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (12663)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.50/0.56  % (12686)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (12686)Memory used [KB]: 1663
% 1.50/0.56  % (12686)Time elapsed: 0.003 s
% 1.50/0.56  % (12686)------------------------------
% 1.50/0.56  % (12686)------------------------------
% 1.50/0.56  % (12674)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.50/0.57  % (12672)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.50/0.57  % (12667)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.50/0.57  % (12683)Refutation not found, incomplete strategy% (12683)------------------------------
% 1.50/0.57  % (12683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (12684)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.50/0.57  % (12680)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.50/0.57  % (12665)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.50/0.57  % (12671)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.50/0.57  % (12682)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.50/0.57  % (12672)Refutation not found, incomplete strategy% (12672)------------------------------
% 1.50/0.57  % (12672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (12672)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (12672)Memory used [KB]: 10618
% 1.50/0.57  % (12672)Time elapsed: 0.155 s
% 1.50/0.57  % (12672)------------------------------
% 1.50/0.57  % (12672)------------------------------
% 1.50/0.57  % (12673)Refutation found. Thanks to Tanya!
% 1.50/0.57  % SZS status Theorem for theBenchmark
% 1.50/0.57  % (12662)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.57  % (12681)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.50/0.57  % (12676)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.50/0.57  % SZS output start Proof for theBenchmark
% 1.50/0.57  fof(f171,plain,(
% 1.50/0.57    $false),
% 1.50/0.57    inference(subsumption_resolution,[],[f170,f80])).
% 1.50/0.57  fof(f80,plain,(
% 1.50/0.57    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0)))),
% 1.50/0.57    inference(resolution,[],[f76,f32])).
% 1.50/0.57  fof(f32,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f25,f19])).
% 1.50/0.57  fof(f19,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f6])).
% 1.50/0.57  fof(f6,axiom,(
% 1.50/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.50/0.57  fof(f25,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f2])).
% 1.50/0.57  fof(f2,axiom,(
% 1.50/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.50/0.57  fof(f76,plain,(
% 1.50/0.57    r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0)))),
% 1.50/0.57    inference(resolution,[],[f64,f35])).
% 1.50/0.57  fof(f35,plain,(
% 1.50/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.57    inference(equality_resolution,[],[f22])).
% 1.50/0.57  fof(f22,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.50/0.57    inference(cnf_transformation,[],[f1])).
% 1.50/0.57  fof(f1,axiom,(
% 1.50/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.57  fof(f64,plain,(
% 1.50/0.57    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK0)) | r1_tarski(X0,k1_relat_1(k2_xboole_0(sK1,sK0)))) )),
% 1.50/0.57    inference(superposition,[],[f28,f63])).
% 1.50/0.57  fof(f63,plain,(
% 1.50/0.57    k1_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))),
% 1.50/0.57    inference(resolution,[],[f38,f17])).
% 1.50/0.57  fof(f17,plain,(
% 1.50/0.57    v1_relat_1(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f11])).
% 1.50/0.57  fof(f11,plain,(
% 1.50/0.57    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f10])).
% 1.50/0.57  fof(f10,negated_conjecture,(
% 1.50/0.57    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 1.50/0.57    inference(negated_conjecture,[],[f9])).
% 1.50/0.57  fof(f9,conjecture,(
% 1.50/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 1.50/0.57  fof(f38,plain,(
% 1.50/0.57    ( ! [X2] : (~v1_relat_1(X2) | k1_relat_1(k2_xboole_0(sK1,X2)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X2))) )),
% 1.50/0.57    inference(resolution,[],[f15,f18])).
% 1.50/0.57  fof(f18,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f12])).
% 1.50/0.57  fof(f12,plain,(
% 1.50/0.57    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f8])).
% 1.50/0.57  fof(f8,axiom,(
% 1.50/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 1.50/0.57  fof(f15,plain,(
% 1.50/0.57    v1_relat_1(sK1)),
% 1.50/0.57    inference(cnf_transformation,[],[f11])).
% 1.50/0.57  fof(f28,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f14])).
% 1.50/0.57  fof(f14,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.50/0.57    inference(ennf_transformation,[],[f3])).
% 1.50/0.57  fof(f3,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.50/0.57  fof(f170,plain,(
% 1.50/0.57    k1_xboole_0 != k6_subset_1(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0)))),
% 1.50/0.57    inference(forward_demodulation,[],[f169,f29])).
% 1.50/0.57  fof(f29,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 1.50/0.57    inference(definition_unfolding,[],[f20,f19])).
% 1.50/0.57  fof(f20,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f4])).
% 1.50/0.57  fof(f4,axiom,(
% 1.50/0.57    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.50/0.57  fof(f169,plain,(
% 1.50/0.57    k1_xboole_0 != k6_subset_1(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))),
% 1.50/0.57    inference(backward_demodulation,[],[f107,f167])).
% 1.50/0.57  fof(f167,plain,(
% 1.50/0.57    ( ! [X4] : (k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X4))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X4)))) )),
% 1.50/0.57    inference(resolution,[],[f61,f17])).
% 1.50/0.57  fof(f61,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k2_xboole_0(sK1,k6_subset_1(X0,X1))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(X0,X1)))) )),
% 1.50/0.57    inference(resolution,[],[f38,f30])).
% 1.50/0.57  fof(f30,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k6_subset_1(X0,X1))) )),
% 1.50/0.57    inference(definition_unfolding,[],[f21,f19])).
% 1.50/0.57  fof(f21,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k4_xboole_0(X0,X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f13])).
% 1.50/0.57  fof(f13,plain,(
% 1.50/0.57    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f7])).
% 1.50/0.57  fof(f7,axiom,(
% 1.50/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).
% 1.50/0.57  fof(f107,plain,(
% 1.50/0.57    k1_xboole_0 != k6_subset_1(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))))),
% 1.50/0.57    inference(superposition,[],[f42,f33])).
% 1.50/0.57  fof(f33,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k2_xboole_0(X1,X2))) )),
% 1.50/0.57    inference(definition_unfolding,[],[f27,f19,f19,f19])).
% 1.50/0.57  fof(f27,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f5])).
% 1.50/0.57  fof(f5,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.50/0.57  fof(f42,plain,(
% 1.50/0.57    k1_xboole_0 != k6_subset_1(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 1.50/0.57    inference(resolution,[],[f16,f31])).
% 1.50/0.57  fof(f31,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f26,f19])).
% 1.50/0.57  fof(f26,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f2])).
% 1.50/0.57  fof(f16,plain,(
% 1.50/0.57    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 1.50/0.57    inference(cnf_transformation,[],[f11])).
% 1.50/0.57  % SZS output end Proof for theBenchmark
% 1.50/0.57  % (12673)------------------------------
% 1.50/0.57  % (12673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (12673)Termination reason: Refutation
% 1.50/0.57  
% 1.50/0.57  % (12673)Memory used [KB]: 1791
% 1.50/0.57  % (12673)Time elapsed: 0.142 s
% 1.50/0.57  % (12673)------------------------------
% 1.50/0.57  % (12673)------------------------------
% 1.50/0.58  % (12654)Success in time 0.206 s
%------------------------------------------------------------------------------
