%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 190 expanded)
%              Number of leaves         :   10 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  116 ( 570 expanded)
%              Number of equality atoms :   28 ( 148 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (14199)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f228,plain,(
    $false ),
    inference(subsumption_resolution,[],[f225,f80])).

fof(f80,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f79,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f77,f27])).

fof(f27,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f77,plain,
    ( sK1 = k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f70,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f44,f38])).

fof(f38,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f24,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(X1,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f40,f39])).

fof(f39,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2) ),
    inference(resolution,[],[f23,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X1] : m1_subset_1(k9_subset_1(sK0,X1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f23,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f225,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f204,f38])).

fof(f204,plain,(
    ! [X1] : r1_tarski(k3_xboole_0(X1,sK2),k3_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f165,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f165,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f159,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f159,plain,(
    r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f124,f38])).

fof(f124,plain,(
    ! [X0] : r1_tarski(sK2,k3_subset_1(sK0,k3_xboole_0(sK1,X0))) ),
    inference(subsumption_resolution,[],[f123,f101])).

fof(f101,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(sK1,X1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f78,f28])).

fof(f78,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f74,f73])).

fof(f73,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(sK0,X0,sK1) ),
    inference(resolution,[],[f70,f35])).

fof(f74,plain,(
    ! [X1] : m1_subset_1(k9_subset_1(sK0,X1,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f70,f34])).

fof(f123,plain,(
    ! [X0] :
      ( r1_tarski(sK2,k3_subset_1(sK0,k3_xboole_0(sK1,X0)))
      | ~ m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f116,f23])).

fof(f116,plain,(
    ! [X0] :
      ( r1_tarski(sK2,k3_subset_1(sK0,k3_xboole_0(sK1,X0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f25,f33])).

fof(f25,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:39:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (14180)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (14179)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (14181)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (14195)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (14196)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (14187)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (14188)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (14189)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (14197)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (14196)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (14195)Refutation not found, incomplete strategy% (14195)------------------------------
% 0.22/0.57  % (14195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (14195)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (14195)Memory used [KB]: 10618
% 0.22/0.57  % (14195)Time elapsed: 0.142 s
% 0.22/0.57  % (14195)------------------------------
% 0.22/0.57  % (14195)------------------------------
% 0.22/0.57  % (14178)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (14183)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  % (14199)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.57  fof(f228,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f225,f80])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.57    inference(subsumption_resolution,[],[f79,f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    k1_xboole_0 != sK1),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f12,plain,(
% 1.60/0.57    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.60/0.57    inference(flattening,[],[f11])).
% 1.60/0.57  fof(f11,plain,(
% 1.60/0.57    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f10])).
% 1.60/0.57  fof(f10,negated_conjecture,(
% 1.60/0.57    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.60/0.57    inference(negated_conjecture,[],[f9])).
% 1.60/0.57  fof(f9,conjecture,(
% 1.60/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 1.60/0.57  fof(f79,plain,(
% 1.60/0.57    k1_xboole_0 = sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.60/0.57    inference(forward_demodulation,[],[f77,f27])).
% 1.60/0.57  fof(f27,plain,(
% 1.60/0.57    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 1.60/0.57    inference(cnf_transformation,[],[f4])).
% 1.60/0.57  fof(f4,axiom,(
% 1.60/0.57    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.60/0.57  fof(f77,plain,(
% 1.60/0.57    sK1 = k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.60/0.57    inference(resolution,[],[f70,f30])).
% 1.60/0.57  fof(f30,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f22])).
% 1.60/0.57  fof(f22,plain,(
% 1.60/0.57    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.57    inference(nnf_transformation,[],[f14])).
% 1.60/0.57  fof(f14,plain,(
% 1.60/0.57    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f8])).
% 1.60/0.57  fof(f8,axiom,(
% 1.60/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 1.60/0.57  fof(f70,plain,(
% 1.60/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.60/0.57    inference(superposition,[],[f44,f38])).
% 1.60/0.57  fof(f38,plain,(
% 1.60/0.57    sK1 = k3_xboole_0(sK1,sK2)),
% 1.60/0.57    inference(resolution,[],[f24,f29])).
% 1.60/0.57  fof(f29,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f13])).
% 1.60/0.57  fof(f13,plain,(
% 1.60/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.60/0.57    inference(ennf_transformation,[],[f3])).
% 1.60/0.57  fof(f3,axiom,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.60/0.57  fof(f24,plain,(
% 1.60/0.57    r1_tarski(sK1,sK2)),
% 1.60/0.57    inference(cnf_transformation,[],[f21])).
% 1.60/0.57  fof(f44,plain,(
% 1.60/0.57    ( ! [X1] : (m1_subset_1(k3_xboole_0(X1,sK2),k1_zfmisc_1(sK0))) )),
% 1.60/0.57    inference(forward_demodulation,[],[f40,f39])).
% 1.60/0.57  fof(f39,plain,(
% 1.60/0.57    ( ! [X0] : (k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2)) )),
% 1.60/0.57    inference(resolution,[],[f23,f35])).
% 1.60/0.57  fof(f35,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f19])).
% 1.60/0.57  fof(f19,plain,(
% 1.60/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f6])).
% 1.60/0.57  fof(f6,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.60/0.57  fof(f23,plain,(
% 1.60/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.60/0.57    inference(cnf_transformation,[],[f21])).
% 1.60/0.57  fof(f40,plain,(
% 1.60/0.57    ( ! [X1] : (m1_subset_1(k9_subset_1(sK0,X1,sK2),k1_zfmisc_1(sK0))) )),
% 1.60/0.57    inference(resolution,[],[f23,f34])).
% 1.60/0.57  fof(f34,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f18])).
% 1.60/0.57  fof(f18,plain,(
% 1.60/0.57    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f5])).
% 1.60/0.57  fof(f5,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.60/0.57  fof(f225,plain,(
% 1.60/0.57    r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.60/0.57    inference(superposition,[],[f204,f38])).
% 1.60/0.57  fof(f204,plain,(
% 1.60/0.57    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,sK2),k3_subset_1(sK0,sK1))) )),
% 1.60/0.57    inference(superposition,[],[f165,f28])).
% 1.60/0.57  fof(f28,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f1])).
% 1.60/0.57  fof(f1,axiom,(
% 1.60/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.60/0.57  fof(f165,plain,(
% 1.60/0.57    ( ! [X0] : (r1_tarski(k3_xboole_0(sK2,X0),k3_subset_1(sK0,sK1))) )),
% 1.60/0.57    inference(resolution,[],[f159,f33])).
% 1.60/0.57  fof(f33,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f17])).
% 1.60/0.57  fof(f17,plain,(
% 1.60/0.57    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.60/0.57    inference(ennf_transformation,[],[f2])).
% 1.60/0.57  fof(f2,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 1.60/0.57  fof(f159,plain,(
% 1.60/0.57    r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 1.60/0.57    inference(superposition,[],[f124,f38])).
% 1.60/0.57  fof(f124,plain,(
% 1.60/0.57    ( ! [X0] : (r1_tarski(sK2,k3_subset_1(sK0,k3_xboole_0(sK1,X0)))) )),
% 1.60/0.57    inference(subsumption_resolution,[],[f123,f101])).
% 1.60/0.57  fof(f101,plain,(
% 1.60/0.57    ( ! [X1] : (m1_subset_1(k3_xboole_0(sK1,X1),k1_zfmisc_1(sK0))) )),
% 1.60/0.57    inference(superposition,[],[f78,f28])).
% 1.60/0.57  fof(f78,plain,(
% 1.60/0.57    ( ! [X1] : (m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(sK0))) )),
% 1.60/0.57    inference(forward_demodulation,[],[f74,f73])).
% 1.60/0.57  fof(f73,plain,(
% 1.60/0.57    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(sK0,X0,sK1)) )),
% 1.60/0.57    inference(resolution,[],[f70,f35])).
% 1.60/0.57  fof(f74,plain,(
% 1.60/0.57    ( ! [X1] : (m1_subset_1(k9_subset_1(sK0,X1,sK1),k1_zfmisc_1(sK0))) )),
% 1.60/0.57    inference(resolution,[],[f70,f34])).
% 1.60/0.57  fof(f123,plain,(
% 1.60/0.57    ( ! [X0] : (r1_tarski(sK2,k3_subset_1(sK0,k3_xboole_0(sK1,X0))) | ~m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK0))) )),
% 1.60/0.57    inference(subsumption_resolution,[],[f116,f23])).
% 1.60/0.57  fof(f116,plain,(
% 1.60/0.57    ( ! [X0] : (r1_tarski(sK2,k3_subset_1(sK0,k3_xboole_0(sK1,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK0))) )),
% 1.60/0.57    inference(resolution,[],[f47,f32])).
% 1.60/0.57  fof(f32,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f16])).
% 1.60/0.57  fof(f16,plain,(
% 1.60/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.57    inference(flattening,[],[f15])).
% 1.60/0.57  fof(f15,plain,(
% 1.60/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f7])).
% 1.60/0.57  fof(f7,axiom,(
% 1.60/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 1.60/0.57  fof(f47,plain,(
% 1.60/0.57    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),k3_subset_1(sK0,sK2))) )),
% 1.60/0.57    inference(resolution,[],[f25,f33])).
% 1.60/0.57  fof(f25,plain,(
% 1.60/0.57    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.60/0.57    inference(cnf_transformation,[],[f21])).
% 1.60/0.57  % SZS output end Proof for theBenchmark
% 1.60/0.57  % (14196)------------------------------
% 1.60/0.57  % (14196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (14196)Termination reason: Refutation
% 1.60/0.57  
% 1.60/0.57  % (14196)Memory used [KB]: 1791
% 1.60/0.57  % (14196)Time elapsed: 0.131 s
% 1.60/0.57  % (14196)------------------------------
% 1.60/0.57  % (14196)------------------------------
% 1.60/0.58  % (14172)Success in time 0.209 s
%------------------------------------------------------------------------------
