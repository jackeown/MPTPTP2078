%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:10 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 138 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 199 expanded)
%              Number of equality atoms :   53 ( 114 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(subsumption_resolution,[],[f122,f87])).

fof(f87,plain,(
    sK0 != k4_subset_1(sK0,sK0,sK1) ),
    inference(superposition,[],[f57,f86])).

fof(f86,plain,(
    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f70,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f31,f29])).

fof(f29,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k4_subset_1(sK0,sK1,X0) ) ),
    inference(resolution,[],[f48,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f57,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f28,f29])).

fof(f28,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f122,plain,(
    sK0 = k4_subset_1(sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f120,f100])).

fof(f100,plain,(
    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f99,f51])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f30,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f99,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f93,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f66,f59])).

fof(f59,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f38,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f52,f51])).

fof(f52,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f32,f36,f50])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f93,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k5_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f53,f78])).

fof(f78,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f75,f38])).

fof(f75,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f68,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f64,f27])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(sK2(X0,X2),X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f39,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f53,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f37,f50,f36,f50])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f120,plain,(
    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(resolution,[],[f117,f58])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k3_tarski(k2_enumset1(X0,X0,X0,sK1)) ) ),
    inference(resolution,[],[f54,f27])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:42:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.27/0.54  % (6839)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.55  % (6843)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.55/0.59  % (6819)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.55/0.59  % (6826)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.55/0.59  % (6833)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.55/0.59  % (6820)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.55/0.59  % (6820)Refutation not found, incomplete strategy% (6820)------------------------------
% 1.55/0.59  % (6820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (6833)Refutation not found, incomplete strategy% (6833)------------------------------
% 1.55/0.59  % (6833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (6820)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (6820)Memory used [KB]: 6268
% 1.55/0.59  % (6820)Time elapsed: 0.158 s
% 1.55/0.59  % (6820)------------------------------
% 1.55/0.59  % (6820)------------------------------
% 1.55/0.59  % (6818)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.55/0.59  % (6833)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (6833)Memory used [KB]: 10618
% 1.55/0.59  % (6833)Time elapsed: 0.164 s
% 1.55/0.59  % (6833)------------------------------
% 1.55/0.59  % (6833)------------------------------
% 1.55/0.59  % (6825)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.55/0.60  % (6822)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.55/0.60  % (6825)Refutation not found, incomplete strategy% (6825)------------------------------
% 1.55/0.60  % (6825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (6825)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.60  
% 1.55/0.60  % (6825)Memory used [KB]: 10618
% 1.55/0.60  % (6825)Time elapsed: 0.160 s
% 1.55/0.60  % (6825)------------------------------
% 1.55/0.60  % (6825)------------------------------
% 1.55/0.60  % (6816)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.55/0.60  % (6822)Refutation found. Thanks to Tanya!
% 1.55/0.60  % SZS status Theorem for theBenchmark
% 1.55/0.60  % SZS output start Proof for theBenchmark
% 1.55/0.60  fof(f123,plain,(
% 1.55/0.60    $false),
% 1.55/0.60    inference(subsumption_resolution,[],[f122,f87])).
% 1.55/0.60  fof(f87,plain,(
% 1.55/0.60    sK0 != k4_subset_1(sK0,sK0,sK1)),
% 1.55/0.60    inference(superposition,[],[f57,f86])).
% 1.55/0.60  fof(f86,plain,(
% 1.55/0.60    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)),
% 1.55/0.60    inference(resolution,[],[f70,f58])).
% 1.55/0.60  fof(f58,plain,(
% 1.55/0.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.55/0.60    inference(forward_demodulation,[],[f31,f29])).
% 1.55/0.60  fof(f29,plain,(
% 1.55/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.55/0.60    inference(cnf_transformation,[],[f13])).
% 1.55/0.60  fof(f13,axiom,(
% 1.55/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.55/0.60  fof(f31,plain,(
% 1.55/0.60    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f14])).
% 1.55/0.60  fof(f14,axiom,(
% 1.55/0.60    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.55/0.60  fof(f70,plain,(
% 1.55/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k4_subset_1(sK0,sK1,X0)) )),
% 1.55/0.60    inference(resolution,[],[f48,f27])).
% 1.55/0.60  fof(f27,plain,(
% 1.55/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.55/0.60    inference(cnf_transformation,[],[f19])).
% 1.55/0.60  fof(f19,plain,(
% 1.55/0.60    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.60    inference(ennf_transformation,[],[f18])).
% 1.55/0.60  fof(f18,negated_conjecture,(
% 1.55/0.60    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.55/0.60    inference(negated_conjecture,[],[f17])).
% 1.55/0.60  fof(f17,conjecture,(
% 1.55/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 1.55/0.60  fof(f48,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f26])).
% 1.55/0.60  fof(f26,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.60    inference(flattening,[],[f25])).
% 1.55/0.60  fof(f25,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.55/0.60    inference(ennf_transformation,[],[f12])).
% 1.55/0.60  fof(f12,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 1.55/0.60  fof(f57,plain,(
% 1.55/0.60    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 1.55/0.60    inference(backward_demodulation,[],[f28,f29])).
% 1.55/0.60  fof(f28,plain,(
% 1.55/0.60    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.55/0.60    inference(cnf_transformation,[],[f19])).
% 1.55/0.60  fof(f122,plain,(
% 1.55/0.60    sK0 = k4_subset_1(sK0,sK0,sK1)),
% 1.55/0.60    inference(forward_demodulation,[],[f120,f100])).
% 1.55/0.60  fof(f100,plain,(
% 1.55/0.60    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.55/0.60    inference(forward_demodulation,[],[f99,f51])).
% 1.55/0.60  fof(f51,plain,(
% 1.55/0.60    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.55/0.60    inference(definition_unfolding,[],[f30,f50])).
% 1.55/0.60  fof(f50,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f34,f49])).
% 1.55/0.60  fof(f49,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.55/0.60    inference(definition_unfolding,[],[f35,f46])).
% 1.55/0.60  fof(f46,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f10])).
% 1.55/0.60  fof(f10,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.55/0.60  fof(f35,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f9])).
% 1.55/0.60  fof(f9,axiom,(
% 1.55/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.55/0.60  fof(f34,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f11])).
% 1.55/0.60  fof(f11,axiom,(
% 1.55/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.55/0.60  fof(f30,plain,(
% 1.55/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/0.60    inference(cnf_transformation,[],[f5])).
% 1.55/0.60  fof(f5,axiom,(
% 1.55/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.55/0.60  fof(f99,plain,(
% 1.55/0.60    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k1_xboole_0))),
% 1.55/0.60    inference(forward_demodulation,[],[f93,f67])).
% 1.55/0.60  fof(f67,plain,(
% 1.55/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.55/0.60    inference(forward_demodulation,[],[f66,f59])).
% 1.55/0.60  fof(f59,plain,(
% 1.55/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.55/0.60    inference(resolution,[],[f38,f55])).
% 1.55/0.60  fof(f55,plain,(
% 1.55/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.55/0.60    inference(equality_resolution,[],[f41])).
% 1.55/0.60  fof(f41,plain,(
% 1.55/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.55/0.60    inference(cnf_transformation,[],[f3])).
% 1.55/0.60  fof(f3,axiom,(
% 1.55/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.55/0.60  fof(f38,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.55/0.60    inference(cnf_transformation,[],[f20])).
% 1.55/0.60  fof(f20,plain,(
% 1.55/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.55/0.60    inference(ennf_transformation,[],[f6])).
% 1.55/0.60  fof(f6,axiom,(
% 1.55/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.55/0.60  fof(f66,plain,(
% 1.55/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.55/0.60    inference(superposition,[],[f52,f51])).
% 1.55/0.60  fof(f52,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f32,f36,f50])).
% 1.55/0.60  fof(f36,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f4])).
% 1.55/0.60  fof(f4,axiom,(
% 1.55/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.55/0.60  fof(f32,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f8])).
% 1.55/0.60  fof(f8,axiom,(
% 1.55/0.60    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.55/0.60  fof(f93,plain,(
% 1.55/0.60    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k5_xboole_0(sK1,sK1)))),
% 1.55/0.60    inference(superposition,[],[f53,f78])).
% 1.55/0.60  fof(f78,plain,(
% 1.55/0.60    sK1 = k3_xboole_0(sK1,sK0)),
% 1.55/0.60    inference(resolution,[],[f75,f38])).
% 1.55/0.60  fof(f75,plain,(
% 1.55/0.60    r1_tarski(sK1,sK0)),
% 1.55/0.60    inference(duplicate_literal_removal,[],[f72])).
% 1.55/0.60  fof(f72,plain,(
% 1.55/0.60    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 1.55/0.60    inference(resolution,[],[f68,f45])).
% 1.55/0.60  fof(f45,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f22])).
% 1.55/0.60  fof(f22,plain,(
% 1.55/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.55/0.60    inference(ennf_transformation,[],[f2])).
% 1.55/0.60  fof(f2,axiom,(
% 1.55/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.55/0.60  fof(f68,plain,(
% 1.55/0.60    ( ! [X0] : (r2_hidden(sK2(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 1.55/0.60    inference(resolution,[],[f64,f27])).
% 1.55/0.60  fof(f64,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(sK2(X0,X2),X1) | r1_tarski(X0,X2)) )),
% 1.55/0.60    inference(resolution,[],[f39,f44])).
% 1.55/0.60  fof(f44,plain,(
% 1.55/0.60    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f22])).
% 1.55/0.60  fof(f39,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f21])).
% 1.55/0.60  fof(f21,plain,(
% 1.55/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.60    inference(ennf_transformation,[],[f15])).
% 1.55/0.60  fof(f15,axiom,(
% 1.55/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.55/0.60  fof(f53,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f37,f50,f36,f50])).
% 1.55/0.60  fof(f37,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f7])).
% 1.55/0.60  fof(f7,axiom,(
% 1.55/0.60    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.55/0.60  fof(f120,plain,(
% 1.55/0.60    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.55/0.60    inference(resolution,[],[f117,f58])).
% 1.55/0.60  fof(f117,plain,(
% 1.55/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k3_tarski(k2_enumset1(X0,X0,X0,sK1))) )),
% 1.55/0.60    inference(resolution,[],[f54,f27])).
% 1.55/0.60  fof(f54,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f47,f50])).
% 1.55/0.60  fof(f47,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f24])).
% 1.55/0.60  fof(f24,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.60    inference(flattening,[],[f23])).
% 1.55/0.60  fof(f23,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.55/0.60    inference(ennf_transformation,[],[f16])).
% 1.55/0.60  fof(f16,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.55/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.55/0.60  % SZS output end Proof for theBenchmark
% 1.55/0.60  % (6822)------------------------------
% 1.55/0.60  % (6822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (6822)Termination reason: Refutation
% 1.55/0.60  
% 1.55/0.60  % (6822)Memory used [KB]: 6268
% 1.55/0.60  % (6822)Time elapsed: 0.170 s
% 1.55/0.60  % (6822)------------------------------
% 1.55/0.60  % (6822)------------------------------
% 1.55/0.60  % (6816)Refutation not found, incomplete strategy% (6816)------------------------------
% 1.55/0.60  % (6816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (6816)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.60  
% 1.55/0.60  % (6816)Memory used [KB]: 1663
% 1.55/0.60  % (6816)Time elapsed: 0.167 s
% 1.55/0.60  % (6816)------------------------------
% 1.55/0.60  % (6816)------------------------------
% 1.55/0.60  % (6815)Success in time 0.229 s
%------------------------------------------------------------------------------
