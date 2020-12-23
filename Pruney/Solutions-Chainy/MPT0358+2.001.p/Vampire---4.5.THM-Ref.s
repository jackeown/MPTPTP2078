%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 114 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 210 expanded)
%              Number of equality atoms :   55 ( 116 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f326,plain,(
    $false ),
    inference(subsumption_resolution,[],[f325,f63])).

fof(f63,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f62,f57])).

fof(f57,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) ),
    inference(superposition,[],[f32,f46])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f19,f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f62,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)))
    | k1_xboole_0 != sK1 ),
    inference(resolution,[],[f34,f45])).

fof(f45,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | k1_xboole_0 != sK1 ),
    inference(inner_rewriting,[],[f30])).

fof(f30,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f14,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f325,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f318,f66])).

fof(f66,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f64,f63])).

fof(f64,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1)))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f13,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f318,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1))) ),
    inference(superposition,[],[f310,f72])).

fof(f72,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f33,f15])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f310,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(duplicate_literal_removal,[],[f300])).

fof(f300,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0
      | k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ) ),
    inference(resolution,[],[f102,f185])).

fof(f185,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK2(X5,X6,X5),X6)
      | k5_xboole_0(X5,k3_xboole_0(X5,X6)) = X5 ) ),
    inference(subsumption_resolution,[],[f183,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f25,f20])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f183,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK2(X5,X6,X5),X6)
      | ~ r2_hidden(sK2(X5,X6,X5),X5)
      | k5_xboole_0(X5,k3_xboole_0(X5,X6)) = X5 ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK2(X5,X6,X5),X6)
      | ~ r2_hidden(sK2(X5,X6,X5),X5)
      | k5_xboole_0(X5,k3_xboole_0(X5,X6)) = X5
      | k5_xboole_0(X5,k3_xboole_0(X5,X6)) = X5 ) ),
    inference(resolution,[],[f41,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(factoring,[],[f40])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f24,f20])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f102,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK2(X4,X5,X4),k5_xboole_0(X6,k3_xboole_0(X6,X4)))
      | k5_xboole_0(X4,k3_xboole_0(X4,X5)) = X4 ) ),
    inference(resolution,[],[f86,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f28,f20])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:07:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (10017)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (10009)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (9998)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (10017)Refutation not found, incomplete strategy% (10017)------------------------------
% 0.21/0.52  % (10017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10001)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (10017)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10017)Memory used [KB]: 10618
% 0.21/0.52  % (10017)Time elapsed: 0.062 s
% 0.21/0.52  % (10017)------------------------------
% 0.21/0.52  % (10017)------------------------------
% 0.21/0.52  % (10013)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (10000)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (10000)Refutation not found, incomplete strategy% (10000)------------------------------
% 0.21/0.53  % (10000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10000)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10000)Memory used [KB]: 6268
% 0.21/0.53  % (10000)Time elapsed: 0.115 s
% 0.21/0.53  % (10000)------------------------------
% 0.21/0.53  % (10000)------------------------------
% 0.21/0.53  % (10005)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (10001)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f326,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f325,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(subsumption_resolution,[],[f62,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5))) )),
% 0.21/0.53    inference(superposition,[],[f32,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.53    inference(superposition,[],[f19,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f18,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))) | k1_xboole_0 != sK1),
% 0.21/0.53    inference(resolution,[],[f34,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | k1_xboole_0 != sK1),
% 0.21/0.53    inference(inner_rewriting,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.53    inference(definition_unfolding,[],[f14,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f23,f20])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.53  fof(f325,plain,(
% 0.21/0.53    k1_xboole_0 = sK1),
% 0.21/0.53    inference(forward_demodulation,[],[f318,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f64,f63])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1))) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(resolution,[],[f35,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(definition_unfolding,[],[f13,f16])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f20])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1)))),
% 0.21/0.53    inference(superposition,[],[f310,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f33,f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f21,f20])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.53  fof(f310,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f300])).
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 | k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 0.21/0.53    inference(resolution,[],[f102,f185])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ( ! [X6,X5] : (r2_hidden(sK2(X5,X6,X5),X6) | k5_xboole_0(X5,k3_xboole_0(X5,X6)) = X5) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f183,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f25,f20])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ( ! [X6,X5] : (r2_hidden(sK2(X5,X6,X5),X6) | ~r2_hidden(sK2(X5,X6,X5),X5) | k5_xboole_0(X5,k3_xboole_0(X5,X6)) = X5) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f178])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X6,X5] : (r2_hidden(sK2(X5,X6,X5),X6) | ~r2_hidden(sK2(X5,X6,X5),X5) | k5_xboole_0(X5,k3_xboole_0(X5,X6)) = X5 | k5_xboole_0(X5,k3_xboole_0(X5,X6)) = X5) )),
% 0.21/0.53    inference(resolution,[],[f41,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.53    inference(factoring,[],[f40])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f24,f20])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X6,X4,X5] : (~r2_hidden(sK2(X4,X5,X4),k5_xboole_0(X6,k3_xboole_0(X6,X4))) | k5_xboole_0(X4,k3_xboole_0(X4,X5)) = X4) )),
% 0.21/0.53    inference(resolution,[],[f86,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.21/0.53    inference(equality_resolution,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f28,f20])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (10001)------------------------------
% 0.21/0.53  % (10001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10001)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (10001)Memory used [KB]: 6396
% 0.21/0.53  % (10001)Time elapsed: 0.080 s
% 0.21/0.53  % (10001)------------------------------
% 0.21/0.53  % (10001)------------------------------
% 0.21/0.54  % (9994)Success in time 0.17 s
%------------------------------------------------------------------------------
