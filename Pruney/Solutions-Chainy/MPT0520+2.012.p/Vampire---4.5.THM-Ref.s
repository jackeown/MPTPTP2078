%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:54 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 209 expanded)
%              Number of leaves         :    6 (  56 expanded)
%              Depth                    :   21
%              Number of atoms          :  138 ( 468 expanded)
%              Number of equality atoms :   47 ( 192 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f694,plain,(
    $false ),
    inference(subsumption_resolution,[],[f693,f17])).

fof(f17,plain,(
    sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

fof(f693,plain,(
    sK0 = k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f692,f207])).

fof(f207,plain,(
    sK0 = k1_setfam_1(k1_enumset1(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(k8_relat_1(sK0,sK1)),sK0)) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( sK0 = k1_setfam_1(k1_enumset1(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(k8_relat_1(sK0,sK1)),sK0))
    | sK0 = k1_setfam_1(k1_enumset1(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(k8_relat_1(sK0,sK1)),sK0)) ),
    inference(resolution,[],[f185,f75])).

fof(f75,plain,(
    ! [X3] :
      ( r2_hidden(sK2(X3,sK0,sK0),k2_relat_1(k8_relat_1(sK0,sK1)))
      | sK0 = k1_setfam_1(k1_enumset1(X3,X3,sK0)) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X3] :
      ( sK0 = k1_setfam_1(k1_enumset1(X3,X3,sK0))
      | r2_hidden(sK2(X3,sK0,sK0),k2_relat_1(k8_relat_1(sK0,sK1)))
      | sK0 = k1_setfam_1(k1_enumset1(X3,X3,sK0)) ) ),
    inference(resolution,[],[f70,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X1),X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X1 ) ),
    inference(factoring,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,sK0,sK0),X1)
      | sK0 = k1_setfam_1(k1_enumset1(X0,X0,sK0))
      | r2_hidden(sK2(X0,sK0,sK0),k2_relat_1(k8_relat_1(X1,sK1))) ) ),
    inference(subsumption_resolution,[],[f67,f15])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0,X1] :
      ( sK0 = k1_setfam_1(k1_enumset1(X0,X0,sK0))
      | ~ r2_hidden(sK2(X0,sK0,sK0),X1)
      | ~ v1_relat_1(sK1)
      | r2_hidden(sK2(X0,sK0,sK0),k2_relat_1(k8_relat_1(X1,sK1))) ) ),
    inference(resolution,[],[f66,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,sK0,sK0),k2_relat_1(sK1))
      | sK0 = k1_setfam_1(k1_enumset1(X0,X0,sK0)) ) ),
    inference(resolution,[],[f60,f16])).

fof(f16,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X4,X5)
      | k1_setfam_1(k1_enumset1(X3,X3,X4)) = X4
      | r2_hidden(sK2(X3,X4,X4),X5) ) ),
    inference(resolution,[],[f58,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f185,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK2(X10,X11,X11),X10)
      | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11 ) ),
    inference(subsumption_resolution,[],[f182,f36])).

fof(f182,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK2(X10,X11,X11),X11)
      | ~ r2_hidden(sK2(X10,X11,X11),X10)
      | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11 ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK2(X10,X11,X11),X11)
      | ~ r2_hidden(sK2(X10,X11,X11),X10)
      | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11
      | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11 ) ),
    inference(resolution,[],[f38,f58])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f692,plain,(
    k2_relat_1(k8_relat_1(sK0,sK1)) = k1_setfam_1(k1_enumset1(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(k8_relat_1(sK0,sK1)),sK0)) ),
    inference(duplicate_literal_removal,[],[f681])).

fof(f681,plain,
    ( k2_relat_1(k8_relat_1(sK0,sK1)) = k1_setfam_1(k1_enumset1(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(k8_relat_1(sK0,sK1)),sK0))
    | k2_relat_1(k8_relat_1(sK0,sK1)) = k1_setfam_1(k1_enumset1(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(k8_relat_1(sK0,sK1)),sK0)) ),
    inference(resolution,[],[f680,f186])).

fof(f186,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(sK2(X12,X13,X12),X13)
      | k1_setfam_1(k1_enumset1(X12,X12,X13)) = X12 ) ),
    inference(subsumption_resolution,[],[f181,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f181,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(sK2(X12,X13,X12),X13)
      | ~ r2_hidden(sK2(X12,X13,X12),X12)
      | k1_setfam_1(k1_enumset1(X12,X12,X13)) = X12 ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(sK2(X12,X13,X12),X13)
      | ~ r2_hidden(sK2(X12,X13,X12),X12)
      | k1_setfam_1(k1_enumset1(X12,X12,X13)) = X12
      | k1_setfam_1(k1_enumset1(X12,X12,X13)) = X12 ) ),
    inference(resolution,[],[f38,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(factoring,[],[f37])).

fof(f680,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2,sK0,k2_relat_1(k8_relat_1(sK0,sK1))),sK0)
      | k2_relat_1(k8_relat_1(sK0,sK1)) = k1_setfam_1(k1_enumset1(X2,X2,sK0)) ) ),
    inference(subsumption_resolution,[],[f674,f15])).

fof(f674,plain,(
    ! [X2] :
      ( k2_relat_1(k8_relat_1(sK0,sK1)) = k1_setfam_1(k1_enumset1(X2,X2,sK0))
      | r2_hidden(sK2(X2,sK0,k2_relat_1(k8_relat_1(sK0,sK1))),sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f480,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f480,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,sK0,k2_relat_1(k8_relat_1(sK0,sK1))),k2_relat_1(k8_relat_1(sK0,sK1)))
      | k2_relat_1(k8_relat_1(sK0,sK1)) = k1_setfam_1(k1_enumset1(X0,X0,sK0)) ) ),
    inference(factoring,[],[f229])).

fof(f229,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,sK0,X1),k2_relat_1(k8_relat_1(sK0,sK1)))
      | r2_hidden(sK2(X0,sK0,X1),X1)
      | k1_setfam_1(k1_enumset1(X0,X0,sK0)) = X1 ) ),
    inference(resolution,[],[f227,f36])).

fof(f227,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k2_relat_1(k8_relat_1(sK0,sK1))) ) ),
    inference(superposition,[],[f41,f207])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.50  % (2532)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (2542)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (2534)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (2539)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.51  % (2542)Refutation not found, incomplete strategy% (2542)------------------------------
% 0.19/0.51  % (2542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (2526)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (2542)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (2542)Memory used [KB]: 10618
% 0.19/0.51  % (2542)Time elapsed: 0.059 s
% 0.19/0.51  % (2542)------------------------------
% 0.19/0.51  % (2542)------------------------------
% 0.19/0.51  % (2530)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.52  % (2547)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.53  % (2520)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (2544)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.53  % (2523)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (2522)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.53  % (2524)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.53  % (2525)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (2522)Refutation not found, incomplete strategy% (2522)------------------------------
% 0.19/0.53  % (2522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (2522)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (2522)Memory used [KB]: 10618
% 0.19/0.53  % (2522)Time elapsed: 0.134 s
% 0.19/0.53  % (2522)------------------------------
% 0.19/0.53  % (2522)------------------------------
% 0.19/0.53  % (2524)Refutation not found, incomplete strategy% (2524)------------------------------
% 0.19/0.53  % (2524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (2524)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (2524)Memory used [KB]: 6140
% 0.19/0.53  % (2524)Time elapsed: 0.136 s
% 0.19/0.53  % (2524)------------------------------
% 0.19/0.53  % (2524)------------------------------
% 0.19/0.54  % (2521)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.54  % (2531)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.54  % (2549)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.54  % (2536)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.54  % (2548)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.54  % (2545)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.54  % (2545)Refutation not found, incomplete strategy% (2545)------------------------------
% 0.19/0.54  % (2545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (2545)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (2545)Memory used [KB]: 6140
% 0.19/0.54  % (2545)Time elapsed: 0.150 s
% 0.19/0.54  % (2545)------------------------------
% 0.19/0.54  % (2545)------------------------------
% 0.19/0.54  % (2541)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.54  % (2528)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.54  % (2527)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.54  % (2537)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.55  % (2540)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.55  % (2528)Refutation not found, incomplete strategy% (2528)------------------------------
% 0.19/0.55  % (2528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (2528)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (2528)Memory used [KB]: 10618
% 0.19/0.55  % (2528)Time elapsed: 0.147 s
% 0.19/0.55  % (2528)------------------------------
% 0.19/0.55  % (2528)------------------------------
% 0.19/0.55  % (2546)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.55  % (2540)Refutation not found, incomplete strategy% (2540)------------------------------
% 0.19/0.55  % (2540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (2540)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (2540)Memory used [KB]: 10746
% 0.19/0.55  % (2540)Time elapsed: 0.147 s
% 0.19/0.55  % (2540)------------------------------
% 0.19/0.55  % (2540)------------------------------
% 0.19/0.55  % (2546)Refutation not found, incomplete strategy% (2546)------------------------------
% 0.19/0.55  % (2546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (2546)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (2546)Memory used [KB]: 10618
% 0.19/0.55  % (2546)Time elapsed: 0.147 s
% 0.19/0.55  % (2546)------------------------------
% 0.19/0.55  % (2546)------------------------------
% 0.19/0.55  % (2535)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.55  % (2533)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.55  % (2529)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.55  % (2538)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.55  % (2543)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.57  % (2526)Refutation found. Thanks to Tanya!
% 0.19/0.57  % SZS status Theorem for theBenchmark
% 0.19/0.57  % SZS output start Proof for theBenchmark
% 0.19/0.57  fof(f694,plain,(
% 0.19/0.57    $false),
% 0.19/0.57    inference(subsumption_resolution,[],[f693,f17])).
% 0.19/0.57  fof(f17,plain,(
% 0.19/0.57    sK0 != k2_relat_1(k8_relat_1(sK0,sK1))),
% 0.19/0.57    inference(cnf_transformation,[],[f12])).
% 0.19/0.57  fof(f12,plain,(
% 0.19/0.57    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1))),
% 0.19/0.57    inference(flattening,[],[f11])).
% 0.19/0.57  fof(f11,plain,(
% 0.19/0.57    ? [X0,X1] : ((k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.19/0.57    inference(ennf_transformation,[],[f8])).
% 0.19/0.57  fof(f8,negated_conjecture,(
% 0.19/0.57    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.19/0.57    inference(negated_conjecture,[],[f7])).
% 0.19/0.57  fof(f7,conjecture,(
% 0.19/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).
% 0.19/0.57  fof(f693,plain,(
% 0.19/0.57    sK0 = k2_relat_1(k8_relat_1(sK0,sK1))),
% 0.19/0.57    inference(forward_demodulation,[],[f692,f207])).
% 0.19/0.57  fof(f207,plain,(
% 0.19/0.57    sK0 = k1_setfam_1(k1_enumset1(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(k8_relat_1(sK0,sK1)),sK0))),
% 0.19/0.57    inference(duplicate_literal_removal,[],[f194])).
% 0.19/0.57  fof(f194,plain,(
% 0.19/0.57    sK0 = k1_setfam_1(k1_enumset1(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(k8_relat_1(sK0,sK1)),sK0)) | sK0 = k1_setfam_1(k1_enumset1(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(k8_relat_1(sK0,sK1)),sK0))),
% 0.19/0.57    inference(resolution,[],[f185,f75])).
% 0.19/0.57  fof(f75,plain,(
% 0.19/0.57    ( ! [X3] : (r2_hidden(sK2(X3,sK0,sK0),k2_relat_1(k8_relat_1(sK0,sK1))) | sK0 = k1_setfam_1(k1_enumset1(X3,X3,sK0))) )),
% 0.19/0.57    inference(duplicate_literal_removal,[],[f74])).
% 0.19/0.57  fof(f74,plain,(
% 0.19/0.57    ( ! [X3] : (sK0 = k1_setfam_1(k1_enumset1(X3,X3,sK0)) | r2_hidden(sK2(X3,sK0,sK0),k2_relat_1(k8_relat_1(sK0,sK1))) | sK0 = k1_setfam_1(k1_enumset1(X3,X3,sK0))) )),
% 0.19/0.57    inference(resolution,[],[f70,f58])).
% 0.19/0.57  fof(f58,plain,(
% 0.19/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X1),X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X1) )),
% 0.19/0.57    inference(factoring,[],[f36])).
% 0.19/0.57  fof(f36,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2) )),
% 0.19/0.57    inference(definition_unfolding,[],[f27,f31])).
% 0.19/0.57  fof(f31,plain,(
% 0.19/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.19/0.57    inference(definition_unfolding,[],[f19,f20])).
% 0.19/0.57  fof(f20,plain,(
% 0.19/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f4])).
% 0.19/0.57  fof(f4,axiom,(
% 0.19/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.57  fof(f19,plain,(
% 0.19/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f5])).
% 0.19/0.57  fof(f5,axiom,(
% 0.19/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.57  fof(f27,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.19/0.57    inference(cnf_transformation,[],[f2])).
% 0.19/0.57  fof(f2,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.19/0.57  fof(f70,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~r2_hidden(sK2(X0,sK0,sK0),X1) | sK0 = k1_setfam_1(k1_enumset1(X0,X0,sK0)) | r2_hidden(sK2(X0,sK0,sK0),k2_relat_1(k8_relat_1(X1,sK1)))) )),
% 0.19/0.57    inference(subsumption_resolution,[],[f67,f15])).
% 0.19/0.57  fof(f15,plain,(
% 0.19/0.57    v1_relat_1(sK1)),
% 0.19/0.57    inference(cnf_transformation,[],[f12])).
% 0.19/0.57  fof(f67,plain,(
% 0.19/0.57    ( ! [X0,X1] : (sK0 = k1_setfam_1(k1_enumset1(X0,X0,sK0)) | ~r2_hidden(sK2(X0,sK0,sK0),X1) | ~v1_relat_1(sK1) | r2_hidden(sK2(X0,sK0,sK0),k2_relat_1(k8_relat_1(X1,sK1)))) )),
% 0.19/0.57    inference(resolution,[],[f66,f24])).
% 0.19/0.57  fof(f24,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2) | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f14])).
% 0.19/0.57  fof(f14,plain,(
% 0.19/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.19/0.57    inference(ennf_transformation,[],[f6])).
% 0.19/0.57  fof(f6,axiom,(
% 0.19/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).
% 0.19/0.57  fof(f66,plain,(
% 0.19/0.57    ( ! [X0] : (r2_hidden(sK2(X0,sK0,sK0),k2_relat_1(sK1)) | sK0 = k1_setfam_1(k1_enumset1(X0,X0,sK0))) )),
% 0.19/0.57    inference(resolution,[],[f60,f16])).
% 0.19/0.57  fof(f16,plain,(
% 0.19/0.57    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.19/0.57    inference(cnf_transformation,[],[f12])).
% 0.19/0.57  fof(f60,plain,(
% 0.19/0.57    ( ! [X4,X5,X3] : (~r1_tarski(X4,X5) | k1_setfam_1(k1_enumset1(X3,X3,X4)) = X4 | r2_hidden(sK2(X3,X4,X4),X5)) )),
% 0.19/0.57    inference(resolution,[],[f58,f21])).
% 0.19/0.57  fof(f21,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r1_tarski(X0,X1) | r2_hidden(X2,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f13])).
% 0.19/0.57  fof(f13,plain,(
% 0.19/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.19/0.57    inference(ennf_transformation,[],[f10])).
% 0.19/0.57  fof(f10,plain,(
% 0.19/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 0.19/0.57  fof(f1,axiom,(
% 0.19/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.57  fof(f185,plain,(
% 0.19/0.57    ( ! [X10,X11] : (~r2_hidden(sK2(X10,X11,X11),X10) | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11) )),
% 0.19/0.57    inference(subsumption_resolution,[],[f182,f36])).
% 0.19/0.57  fof(f182,plain,(
% 0.19/0.57    ( ! [X10,X11] : (~r2_hidden(sK2(X10,X11,X11),X11) | ~r2_hidden(sK2(X10,X11,X11),X10) | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11) )),
% 0.19/0.57    inference(duplicate_literal_removal,[],[f179])).
% 0.19/0.57  fof(f179,plain,(
% 0.19/0.57    ( ! [X10,X11] : (~r2_hidden(sK2(X10,X11,X11),X11) | ~r2_hidden(sK2(X10,X11,X11),X10) | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11 | k1_setfam_1(k1_enumset1(X10,X10,X11)) = X11) )),
% 0.19/0.57    inference(resolution,[],[f38,f58])).
% 0.19/0.57  fof(f38,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2) )),
% 0.19/0.57    inference(definition_unfolding,[],[f25,f31])).
% 0.19/0.57  fof(f25,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.19/0.57    inference(cnf_transformation,[],[f2])).
% 0.19/0.57  fof(f692,plain,(
% 0.19/0.57    k2_relat_1(k8_relat_1(sK0,sK1)) = k1_setfam_1(k1_enumset1(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(k8_relat_1(sK0,sK1)),sK0))),
% 0.19/0.57    inference(duplicate_literal_removal,[],[f681])).
% 0.19/0.57  fof(f681,plain,(
% 0.19/0.57    k2_relat_1(k8_relat_1(sK0,sK1)) = k1_setfam_1(k1_enumset1(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(k8_relat_1(sK0,sK1)),sK0)) | k2_relat_1(k8_relat_1(sK0,sK1)) = k1_setfam_1(k1_enumset1(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(k8_relat_1(sK0,sK1)),sK0))),
% 0.19/0.57    inference(resolution,[],[f680,f186])).
% 0.19/0.57  fof(f186,plain,(
% 0.19/0.57    ( ! [X12,X13] : (~r2_hidden(sK2(X12,X13,X12),X13) | k1_setfam_1(k1_enumset1(X12,X12,X13)) = X12) )),
% 0.19/0.57    inference(subsumption_resolution,[],[f181,f37])).
% 0.19/0.57  fof(f37,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2) )),
% 0.19/0.57    inference(definition_unfolding,[],[f26,f31])).
% 0.19/0.57  fof(f26,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.19/0.57    inference(cnf_transformation,[],[f2])).
% 0.19/0.57  fof(f181,plain,(
% 0.19/0.57    ( ! [X12,X13] : (~r2_hidden(sK2(X12,X13,X12),X13) | ~r2_hidden(sK2(X12,X13,X12),X12) | k1_setfam_1(k1_enumset1(X12,X12,X13)) = X12) )),
% 0.19/0.57    inference(duplicate_literal_removal,[],[f180])).
% 0.19/0.57  fof(f180,plain,(
% 0.19/0.57    ( ! [X12,X13] : (~r2_hidden(sK2(X12,X13,X12),X13) | ~r2_hidden(sK2(X12,X13,X12),X12) | k1_setfam_1(k1_enumset1(X12,X12,X13)) = X12 | k1_setfam_1(k1_enumset1(X12,X12,X13)) = X12) )),
% 0.19/0.57    inference(resolution,[],[f38,f100])).
% 0.19/0.57  fof(f100,plain,(
% 0.19/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 0.19/0.57    inference(factoring,[],[f37])).
% 0.19/0.57  fof(f680,plain,(
% 0.19/0.57    ( ! [X2] : (r2_hidden(sK2(X2,sK0,k2_relat_1(k8_relat_1(sK0,sK1))),sK0) | k2_relat_1(k8_relat_1(sK0,sK1)) = k1_setfam_1(k1_enumset1(X2,X2,sK0))) )),
% 0.19/0.57    inference(subsumption_resolution,[],[f674,f15])).
% 0.19/0.57  fof(f674,plain,(
% 0.19/0.57    ( ! [X2] : (k2_relat_1(k8_relat_1(sK0,sK1)) = k1_setfam_1(k1_enumset1(X2,X2,sK0)) | r2_hidden(sK2(X2,sK0,k2_relat_1(k8_relat_1(sK0,sK1))),sK0) | ~v1_relat_1(sK1)) )),
% 0.19/0.57    inference(resolution,[],[f480,f22])).
% 0.19/0.57  fof(f22,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f14])).
% 0.19/0.57  fof(f480,plain,(
% 0.19/0.57    ( ! [X0] : (r2_hidden(sK2(X0,sK0,k2_relat_1(k8_relat_1(sK0,sK1))),k2_relat_1(k8_relat_1(sK0,sK1))) | k2_relat_1(k8_relat_1(sK0,sK1)) = k1_setfam_1(k1_enumset1(X0,X0,sK0))) )),
% 0.19/0.57    inference(factoring,[],[f229])).
% 0.19/0.57  fof(f229,plain,(
% 0.19/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,sK0,X1),k2_relat_1(k8_relat_1(sK0,sK1))) | r2_hidden(sK2(X0,sK0,X1),X1) | k1_setfam_1(k1_enumset1(X0,X0,sK0)) = X1) )),
% 0.19/0.57    inference(resolution,[],[f227,f36])).
% 0.19/0.57  fof(f227,plain,(
% 0.19/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,k2_relat_1(k8_relat_1(sK0,sK1)))) )),
% 0.19/0.57    inference(superposition,[],[f41,f207])).
% 0.19/0.57  fof(f41,plain,(
% 0.19/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_setfam_1(k1_enumset1(X0,X0,X1))) | r2_hidden(X3,X0)) )),
% 0.19/0.57    inference(equality_resolution,[],[f35])).
% 0.19/0.57  fof(f35,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2) )),
% 0.19/0.57    inference(definition_unfolding,[],[f28,f31])).
% 0.19/0.57  fof(f28,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.19/0.57    inference(cnf_transformation,[],[f2])).
% 0.19/0.57  % SZS output end Proof for theBenchmark
% 0.19/0.57  % (2526)------------------------------
% 0.19/0.57  % (2526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (2526)Termination reason: Refutation
% 0.19/0.57  
% 0.19/0.57  % (2526)Memory used [KB]: 6908
% 0.19/0.57  % (2526)Time elapsed: 0.116 s
% 0.19/0.57  % (2526)------------------------------
% 0.19/0.57  % (2526)------------------------------
% 0.19/0.57  % (2519)Success in time 0.214 s
%------------------------------------------------------------------------------
