%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:27 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 (  62 expanded)
%              Number of equality atoms :   32 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(subsumption_resolution,[],[f27,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f55,f29])).

fof(f29,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f55,plain,(
    ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f54,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

fof(f54,plain,(
    ! [X0] : k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k7_relat_1(k1_xboole_0,X0)) ),
    inference(resolution,[],[f38,f48])).

fof(f48,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f47,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

% (2259)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f47,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f46,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f46,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f25])).

% (2260)Refutation not found, incomplete strategy% (2260)------------------------------
% (2260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2257)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f27,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f21])).

fof(f21,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:29:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (810778625)
% 0.14/0.37  ipcrm: permission denied for id (810811395)
% 0.14/0.37  ipcrm: permission denied for id (810876932)
% 0.14/0.37  ipcrm: permission denied for id (810942469)
% 0.14/0.38  ipcrm: permission denied for id (810975238)
% 0.14/0.38  ipcrm: permission denied for id (811106312)
% 0.14/0.38  ipcrm: permission denied for id (811139082)
% 0.14/0.38  ipcrm: permission denied for id (811270158)
% 0.14/0.39  ipcrm: permission denied for id (811335697)
% 0.14/0.39  ipcrm: permission denied for id (811499542)
% 0.14/0.39  ipcrm: permission denied for id (811532311)
% 0.14/0.40  ipcrm: permission denied for id (811663388)
% 0.14/0.40  ipcrm: permission denied for id (811892771)
% 0.14/0.41  ipcrm: permission denied for id (811925541)
% 0.14/0.41  ipcrm: permission denied for id (811958310)
% 0.14/0.41  ipcrm: permission denied for id (811991079)
% 0.14/0.41  ipcrm: permission denied for id (812023848)
% 0.14/0.41  ipcrm: permission denied for id (812089387)
% 0.14/0.41  ipcrm: permission denied for id (812122157)
% 0.14/0.42  ipcrm: permission denied for id (812154928)
% 0.14/0.42  ipcrm: permission denied for id (812187697)
% 0.22/0.42  ipcrm: permission denied for id (812220467)
% 0.22/0.42  ipcrm: permission denied for id (812318774)
% 0.22/0.42  ipcrm: permission denied for id (812351543)
% 0.22/0.42  ipcrm: permission denied for id (812384312)
% 0.22/0.43  ipcrm: permission denied for id (812417082)
% 0.22/0.43  ipcrm: permission denied for id (812449852)
% 0.22/0.43  ipcrm: permission denied for id (812548159)
% 0.22/0.43  ipcrm: permission denied for id (812646466)
% 0.22/0.44  ipcrm: permission denied for id (812712004)
% 0.22/0.44  ipcrm: permission denied for id (812744773)
% 0.22/0.44  ipcrm: permission denied for id (812777542)
% 0.22/0.44  ipcrm: permission denied for id (812941388)
% 0.22/0.45  ipcrm: permission denied for id (813006927)
% 0.22/0.45  ipcrm: permission denied for id (813039696)
% 0.22/0.45  ipcrm: permission denied for id (813072465)
% 0.22/0.45  ipcrm: permission denied for id (813203541)
% 0.22/0.45  ipcrm: permission denied for id (813236310)
% 0.22/0.45  ipcrm: permission denied for id (813269079)
% 0.22/0.45  ipcrm: permission denied for id (813301848)
% 0.22/0.45  ipcrm: permission denied for id (813334617)
% 0.22/0.46  ipcrm: permission denied for id (813432924)
% 0.22/0.46  ipcrm: permission denied for id (813465694)
% 0.22/0.46  ipcrm: permission denied for id (813498463)
% 0.22/0.46  ipcrm: permission denied for id (813596771)
% 0.22/0.47  ipcrm: permission denied for id (813629540)
% 0.22/0.47  ipcrm: permission denied for id (813826156)
% 0.22/0.47  ipcrm: permission denied for id (813858925)
% 0.22/0.47  ipcrm: permission denied for id (813891694)
% 0.22/0.48  ipcrm: permission denied for id (813924463)
% 0.22/0.48  ipcrm: permission denied for id (813957232)
% 0.22/0.48  ipcrm: permission denied for id (814022771)
% 0.22/0.48  ipcrm: permission denied for id (814088309)
% 0.22/0.48  ipcrm: permission denied for id (814121078)
% 0.22/0.49  ipcrm: permission denied for id (814317694)
% 1.22/0.65  % (2249)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.22/0.66  % (2260)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.22/0.66  % (2251)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.22/0.66  % (2250)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.22/0.66  % (2251)Refutation not found, incomplete strategy% (2251)------------------------------
% 1.22/0.66  % (2251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.66  % (2251)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.66  
% 1.22/0.66  % (2251)Memory used [KB]: 10618
% 1.22/0.66  % (2251)Time elapsed: 0.117 s
% 1.22/0.66  % (2251)------------------------------
% 1.22/0.66  % (2251)------------------------------
% 1.22/0.66  % (2250)Refutation found. Thanks to Tanya!
% 1.22/0.66  % SZS status Theorem for theBenchmark
% 1.22/0.66  % (2258)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.22/0.67  % (2268)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.22/0.67  % (2252)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.22/0.67  % (2265)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.22/0.67  % (2252)Refutation not found, incomplete strategy% (2252)------------------------------
% 1.22/0.67  % (2252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.67  % (2252)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.67  
% 1.22/0.67  % (2252)Memory used [KB]: 10618
% 1.22/0.67  % (2252)Time elapsed: 0.115 s
% 1.22/0.67  % (2252)------------------------------
% 1.22/0.67  % (2252)------------------------------
% 1.22/0.67  % (2266)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.22/0.67  % SZS output start Proof for theBenchmark
% 1.22/0.67  fof(f57,plain,(
% 1.22/0.67    $false),
% 1.22/0.67    inference(subsumption_resolution,[],[f27,f56])).
% 1.22/0.67  fof(f56,plain,(
% 1.22/0.67    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.22/0.67    inference(forward_demodulation,[],[f55,f29])).
% 1.22/0.67  fof(f29,plain,(
% 1.22/0.67    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.22/0.67    inference(cnf_transformation,[],[f14])).
% 1.22/0.67  fof(f14,axiom,(
% 1.22/0.67    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.22/0.67  fof(f55,plain,(
% 1.22/0.67    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) )),
% 1.22/0.67    inference(forward_demodulation,[],[f54,f30])).
% 1.22/0.67  fof(f30,plain,(
% 1.22/0.67    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.22/0.67    inference(cnf_transformation,[],[f12])).
% 1.22/0.67  fof(f12,axiom,(
% 1.22/0.67    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
% 1.22/0.67  fof(f54,plain,(
% 1.22/0.67    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k7_relat_1(k1_xboole_0,X0))) )),
% 1.22/0.67    inference(resolution,[],[f38,f48])).
% 1.22/0.67  fof(f48,plain,(
% 1.22/0.67    v1_relat_1(k1_xboole_0)),
% 1.22/0.67    inference(resolution,[],[f47,f33])).
% 1.22/0.67  fof(f33,plain,(
% 1.22/0.67    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 1.22/0.67    inference(cnf_transformation,[],[f24])).
% 1.22/0.67  % (2259)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.22/0.67  fof(f24,plain,(
% 1.22/0.67    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.22/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f23])).
% 1.22/0.67  fof(f23,plain,(
% 1.22/0.67    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.22/0.67    introduced(choice_axiom,[])).
% 1.22/0.67  fof(f19,plain,(
% 1.22/0.67    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.22/0.67    inference(ennf_transformation,[],[f17])).
% 1.22/0.67  fof(f17,plain,(
% 1.22/0.67    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.22/0.67    inference(unused_predicate_definition_removal,[],[f11])).
% 1.22/0.67  fof(f11,axiom,(
% 1.22/0.67    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 1.22/0.67  fof(f47,plain,(
% 1.22/0.67    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.22/0.67    inference(superposition,[],[f46,f31])).
% 1.22/0.67  fof(f31,plain,(
% 1.22/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.22/0.67    inference(cnf_transformation,[],[f2])).
% 1.22/0.67  fof(f2,axiom,(
% 1.22/0.67    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.22/0.67  fof(f46,plain,(
% 1.22/0.67    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.22/0.67    inference(equality_resolution,[],[f41])).
% 1.22/0.67  fof(f41,plain,(
% 1.22/0.67    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.22/0.67    inference(cnf_transformation,[],[f26])).
% 1.22/0.67  fof(f26,plain,(
% 1.22/0.67    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.22/0.67    inference(flattening,[],[f25])).
% 1.22/0.67  % (2260)Refutation not found, incomplete strategy% (2260)------------------------------
% 1.22/0.67  % (2260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.67  % (2257)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.67  fof(f25,plain,(
% 1.22/0.67    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.22/0.67    inference(nnf_transformation,[],[f9])).
% 1.22/0.67  fof(f9,axiom,(
% 1.22/0.67    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.22/0.67  fof(f38,plain,(
% 1.22/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.22/0.67    inference(cnf_transformation,[],[f20])).
% 1.22/0.67  fof(f20,plain,(
% 1.22/0.67    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.22/0.67    inference(ennf_transformation,[],[f13])).
% 1.22/0.67  fof(f13,axiom,(
% 1.22/0.67    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.22/0.67  fof(f27,plain,(
% 1.22/0.67    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 1.22/0.67    inference(cnf_transformation,[],[f22])).
% 1.22/0.67  fof(f22,plain,(
% 1.22/0.67    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 1.22/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f21])).
% 1.22/0.67  fof(f21,plain,(
% 1.22/0.67    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 1.22/0.67    introduced(choice_axiom,[])).
% 1.22/0.67  fof(f18,plain,(
% 1.22/0.67    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 1.22/0.67    inference(ennf_transformation,[],[f16])).
% 1.22/0.67  fof(f16,negated_conjecture,(
% 1.22/0.67    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.22/0.67    inference(negated_conjecture,[],[f15])).
% 1.22/0.67  fof(f15,conjecture,(
% 1.22/0.67    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.22/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 1.22/0.67  % SZS output end Proof for theBenchmark
% 1.22/0.67  % (2250)------------------------------
% 1.22/0.67  % (2250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.67  % (2250)Termination reason: Refutation
% 1.22/0.67  
% 1.22/0.67  % (2250)Memory used [KB]: 6268
% 1.22/0.67  % (2250)Time elapsed: 0.117 s
% 1.22/0.67  % (2250)------------------------------
% 1.22/0.67  % (2250)------------------------------
% 1.22/0.67  % (2103)Success in time 0.305 s
%------------------------------------------------------------------------------
