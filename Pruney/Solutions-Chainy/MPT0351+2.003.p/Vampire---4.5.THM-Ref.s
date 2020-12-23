%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:03 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   52 (  73 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 119 expanded)
%              Number of equality atoms :   35 (  52 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(subsumption_resolution,[],[f147,f50])).

fof(f50,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f26,f28])).

fof(f28,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f26,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f147,plain,(
    sK0 = k4_subset_1(sK0,sK1,sK0) ),
    inference(forward_demodulation,[],[f146,f77])).

fof(f77,plain,(
    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(superposition,[],[f61,f74])).

fof(f74,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f73,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f73,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f71,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f67,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f42,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

% (14084)Refutation not found, incomplete strategy% (14084)------------------------------
% (14084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14084)Termination reason: Refutation not found, incomplete strategy
fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

% (14084)Memory used [KB]: 10746
% (14084)Time elapsed: 0.156 s
fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

% (14084)------------------------------
% (14084)------------------------------
fof(f61,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[],[f48,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f34,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f146,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f143,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f32,f35,f35])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f143,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK0)) ),
    inference(resolution,[],[f94,f25])).

fof(f94,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X2,X1,X2) ) ),
    inference(resolution,[],[f49,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f29,f28])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.35/0.56  % (14062)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.57  % (14063)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.57  % (14064)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.57  % (14068)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.57  % (14070)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.57  % (14084)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.57  % (14078)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.57  % (14064)Refutation found. Thanks to Tanya!
% 1.35/0.57  % SZS status Theorem for theBenchmark
% 1.35/0.57  % SZS output start Proof for theBenchmark
% 1.35/0.57  fof(f148,plain,(
% 1.35/0.57    $false),
% 1.35/0.57    inference(subsumption_resolution,[],[f147,f50])).
% 1.35/0.57  fof(f50,plain,(
% 1.35/0.57    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 1.35/0.57    inference(backward_demodulation,[],[f26,f28])).
% 1.35/0.57  fof(f28,plain,(
% 1.35/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.35/0.57    inference(cnf_transformation,[],[f10])).
% 1.35/0.57  fof(f10,axiom,(
% 1.35/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.35/0.57  fof(f26,plain,(
% 1.35/0.57    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.35/0.57    inference(cnf_transformation,[],[f18])).
% 1.35/0.57  fof(f18,plain,(
% 1.35/0.57    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.57    inference(ennf_transformation,[],[f16])).
% 1.35/0.57  fof(f16,negated_conjecture,(
% 1.35/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.35/0.57    inference(negated_conjecture,[],[f15])).
% 1.35/0.57  fof(f15,conjecture,(
% 1.35/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 1.35/0.57  fof(f147,plain,(
% 1.35/0.57    sK0 = k4_subset_1(sK0,sK1,sK0)),
% 1.35/0.57    inference(forward_demodulation,[],[f146,f77])).
% 1.35/0.57  fof(f77,plain,(
% 1.35/0.57    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.35/0.57    inference(superposition,[],[f61,f74])).
% 1.35/0.57  fof(f74,plain,(
% 1.35/0.57    sK1 = k3_xboole_0(sK1,sK0)),
% 1.35/0.57    inference(resolution,[],[f73,f41])).
% 1.35/0.57  fof(f41,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.35/0.57    inference(cnf_transformation,[],[f20])).
% 1.35/0.57  fof(f20,plain,(
% 1.35/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.35/0.57    inference(ennf_transformation,[],[f5])).
% 1.35/0.57  fof(f5,axiom,(
% 1.35/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.35/0.57  fof(f73,plain,(
% 1.35/0.57    r1_tarski(sK1,sK0)),
% 1.35/0.57    inference(duplicate_literal_removal,[],[f72])).
% 1.35/0.57  fof(f72,plain,(
% 1.35/0.57    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 1.35/0.57    inference(resolution,[],[f71,f44])).
% 1.35/0.57  fof(f44,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f22])).
% 1.35/0.57  fof(f22,plain,(
% 1.35/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.35/0.57    inference(ennf_transformation,[],[f17])).
% 1.35/0.57  fof(f17,plain,(
% 1.35/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.35/0.57    inference(unused_predicate_definition_removal,[],[f3])).
% 1.35/0.57  fof(f3,axiom,(
% 1.35/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.35/0.57  fof(f71,plain,(
% 1.35/0.57    ( ! [X0] : (r2_hidden(sK3(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 1.35/0.57    inference(resolution,[],[f67,f43])).
% 1.35/0.57  fof(f43,plain,(
% 1.35/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f22])).
% 1.35/0.57  fof(f67,plain,(
% 1.35/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 1.35/0.57    inference(resolution,[],[f42,f25])).
% 1.35/0.57  fof(f25,plain,(
% 1.35/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.35/0.57    inference(cnf_transformation,[],[f18])).
% 1.35/0.57  fof(f42,plain,(
% 1.35/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f21])).
% 1.35/0.57  % (14084)Refutation not found, incomplete strategy% (14084)------------------------------
% 1.35/0.57  % (14084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (14084)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  fof(f21,plain,(
% 1.35/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.57    inference(ennf_transformation,[],[f13])).
% 1.35/0.57  
% 1.35/0.57  % (14084)Memory used [KB]: 10746
% 1.35/0.57  % (14084)Time elapsed: 0.156 s
% 1.35/0.57  fof(f13,axiom,(
% 1.35/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.35/0.57  % (14084)------------------------------
% 1.35/0.57  % (14084)------------------------------
% 1.35/0.57  fof(f61,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X1,X0))) = X0) )),
% 1.35/0.57    inference(superposition,[],[f48,f33])).
% 1.35/0.57  fof(f33,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f1])).
% 1.35/0.57  fof(f1,axiom,(
% 1.35/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.35/0.57  fof(f48,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 1.35/0.57    inference(definition_unfolding,[],[f34,f46])).
% 1.35/0.57  fof(f46,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.35/0.57    inference(definition_unfolding,[],[f36,f35])).
% 1.35/0.57  fof(f35,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f7])).
% 1.35/0.57  fof(f7,axiom,(
% 1.35/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.35/0.57  fof(f36,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f8])).
% 1.35/0.57  fof(f8,axiom,(
% 1.35/0.57    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.35/0.57  fof(f34,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.35/0.57    inference(cnf_transformation,[],[f4])).
% 1.35/0.57  fof(f4,axiom,(
% 1.35/0.57    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.35/0.57  fof(f146,plain,(
% 1.35/0.57    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.35/0.57    inference(forward_demodulation,[],[f143,f47])).
% 1.35/0.57  fof(f47,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.35/0.57    inference(definition_unfolding,[],[f32,f35,f35])).
% 1.35/0.57  fof(f32,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f6])).
% 1.35/0.57  fof(f6,axiom,(
% 1.35/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.35/0.57  fof(f143,plain,(
% 1.35/0.57    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK0))),
% 1.35/0.57    inference(resolution,[],[f94,f25])).
% 1.35/0.57  fof(f94,plain,(
% 1.35/0.57    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X2,X1,X2)) )),
% 1.35/0.57    inference(resolution,[],[f49,f51])).
% 1.35/0.57  fof(f51,plain,(
% 1.35/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.35/0.57    inference(forward_demodulation,[],[f29,f28])).
% 1.35/0.57  fof(f29,plain,(
% 1.35/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.35/0.57    inference(cnf_transformation,[],[f11])).
% 1.35/0.57  fof(f11,axiom,(
% 1.35/0.57    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.35/0.57  fof(f49,plain,(
% 1.35/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))) )),
% 1.35/0.57    inference(definition_unfolding,[],[f45,f46])).
% 1.35/0.57  fof(f45,plain,(
% 1.35/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f24])).
% 1.35/0.57  fof(f24,plain,(
% 1.35/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.57    inference(flattening,[],[f23])).
% 1.35/0.57  fof(f23,plain,(
% 1.35/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.35/0.57    inference(ennf_transformation,[],[f14])).
% 1.35/0.57  fof(f14,axiom,(
% 1.35/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.35/0.57  % SZS output end Proof for theBenchmark
% 1.35/0.57  % (14064)------------------------------
% 1.35/0.57  % (14064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (14064)Termination reason: Refutation
% 1.35/0.57  
% 1.35/0.57  % (14064)Memory used [KB]: 6268
% 1.35/0.57  % (14064)Time elapsed: 0.148 s
% 1.35/0.57  % (14064)------------------------------
% 1.35/0.57  % (14064)------------------------------
% 1.35/0.57  % (14086)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.57  % (14081)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.58  % (14061)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.58  % (14076)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.58  % (14080)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.58  % (14058)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.71/0.58  % (14058)Refutation not found, incomplete strategy% (14058)------------------------------
% 1.71/0.58  % (14058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.58  % (14058)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.58  
% 1.71/0.58  % (14058)Memory used [KB]: 1663
% 1.71/0.58  % (14058)Time elapsed: 0.155 s
% 1.71/0.58  % (14058)------------------------------
% 1.71/0.58  % (14058)------------------------------
% 1.71/0.58  % (14073)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.71/0.58  % (14068)Refutation not found, incomplete strategy% (14068)------------------------------
% 1.71/0.58  % (14068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.58  % (14068)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.58  
% 1.71/0.58  % (14068)Memory used [KB]: 10618
% 1.71/0.58  % (14068)Time elapsed: 0.162 s
% 1.71/0.58  % (14068)------------------------------
% 1.71/0.58  % (14068)------------------------------
% 1.71/0.58  % (14060)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.71/0.58  % (14062)Refutation not found, incomplete strategy% (14062)------------------------------
% 1.71/0.58  % (14062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.58  % (14062)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.58  
% 1.71/0.58  % (14062)Memory used [KB]: 6140
% 1.71/0.58  % (14062)Time elapsed: 0.162 s
% 1.71/0.58  % (14062)------------------------------
% 1.71/0.58  % (14062)------------------------------
% 1.71/0.58  % (14072)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.71/0.59  % (14057)Success in time 0.223 s
%------------------------------------------------------------------------------
