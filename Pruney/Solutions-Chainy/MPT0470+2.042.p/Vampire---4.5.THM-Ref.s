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
% DateTime   : Thu Dec  3 12:47:49 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 129 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  144 ( 305 expanded)
%              Number of equality atoms :   64 ( 141 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(subsumption_resolution,[],[f167,f109])).

% (11945)Refutation not found, incomplete strategy% (11945)------------------------------
% (11945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11945)Termination reason: Refutation not found, incomplete strategy

% (11945)Memory used [KB]: 10618
% (11945)Time elapsed: 0.126 s
% (11945)------------------------------
% (11945)------------------------------
fof(f109,plain,(
    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f30,f98])).

fof(f98,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f97,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f97,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f95,f52])).

fof(f52,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f95,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) ),
    inference(backward_demodulation,[],[f85,f92])).

fof(f92,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f75,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f45,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

% (11953)Termination reason: Refutation not found, incomplete strategy

% (11953)Memory used [KB]: 10618
% (11953)Time elapsed: 0.126 s
% (11953)------------------------------
% (11953)------------------------------
fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f75,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f74,f32])).

fof(f32,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f74,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f65,f53])).

fof(f53,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f36,f31])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,sK0)),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f39,f29])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f85,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) ),
    inference(resolution,[],[f70,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f70,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f54,f53])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,sK0)) ) ),
    inference(resolution,[],[f42,f29])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f30,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f167,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f166,f35])).

fof(f166,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f164,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f164,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f131,f161])).

fof(f161,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f124,f56])).

fof(f124,plain,(
    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f64,f29])).

fof(f64,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f63,f33])).

fof(f33,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,(
    ! [X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,k1_xboole_0)),k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f38,f53])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f131,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))) ),
    inference(resolution,[],[f121,f37])).

fof(f121,plain,(
    v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f55,f29])).

fof(f55,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f42,f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:34:22 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.23/0.56  % (11937)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.56  % (11936)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.56  % (11936)Refutation found. Thanks to Tanya!
% 0.23/0.56  % SZS status Theorem for theBenchmark
% 0.23/0.56  % (11952)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.56  % (11944)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.56/0.57  % (11953)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.56/0.57  % (11953)Refutation not found, incomplete strategy% (11953)------------------------------
% 1.56/0.57  % (11953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (11945)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f168,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(subsumption_resolution,[],[f167,f109])).
% 1.56/0.58  % (11945)Refutation not found, incomplete strategy% (11945)------------------------------
% 1.56/0.58  % (11945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (11945)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (11945)Memory used [KB]: 10618
% 1.56/0.58  % (11945)Time elapsed: 0.126 s
% 1.56/0.58  % (11945)------------------------------
% 1.56/0.58  % (11945)------------------------------
% 1.56/0.58  fof(f109,plain,(
% 1.56/0.58    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.56/0.58    inference(trivial_inequality_removal,[],[f99])).
% 1.56/0.58  fof(f99,plain,(
% 1.56/0.58    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.56/0.58    inference(backward_demodulation,[],[f30,f98])).
% 1.56/0.58  fof(f98,plain,(
% 1.56/0.58    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.56/0.58    inference(forward_demodulation,[],[f97,f35])).
% 1.56/0.58  fof(f35,plain,(
% 1.56/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f3])).
% 1.56/0.58  fof(f3,axiom,(
% 1.56/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.56/0.58  fof(f97,plain,(
% 1.56/0.58    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)),
% 1.56/0.58    inference(forward_demodulation,[],[f95,f52])).
% 1.56/0.58  fof(f52,plain,(
% 1.56/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.56/0.58    inference(equality_resolution,[],[f47])).
% 1.56/0.58  fof(f47,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.56/0.58    inference(cnf_transformation,[],[f28])).
% 1.56/0.58  fof(f28,plain,(
% 1.56/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.56/0.58    inference(flattening,[],[f27])).
% 1.56/0.58  fof(f27,plain,(
% 1.56/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.56/0.58    inference(nnf_transformation,[],[f6])).
% 1.56/0.58  fof(f6,axiom,(
% 1.56/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.56/0.58  fof(f95,plain,(
% 1.56/0.58    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))),
% 1.56/0.58    inference(backward_demodulation,[],[f85,f92])).
% 1.56/0.58  fof(f92,plain,(
% 1.56/0.58    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.56/0.58    inference(resolution,[],[f75,f56])).
% 1.56/0.58  fof(f56,plain,(
% 1.56/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.56/0.58    inference(resolution,[],[f45,f34])).
% 1.56/0.58  fof(f34,plain,(
% 1.56/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f4])).
% 1.56/0.58  % (11953)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (11953)Memory used [KB]: 10618
% 1.56/0.58  % (11953)Time elapsed: 0.126 s
% 1.56/0.58  % (11953)------------------------------
% 1.56/0.58  % (11953)------------------------------
% 1.56/0.58  fof(f4,axiom,(
% 1.56/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.56/0.58  fof(f45,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f26])).
% 1.56/0.58  fof(f26,plain,(
% 1.56/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.58    inference(flattening,[],[f25])).
% 1.56/0.58  fof(f25,plain,(
% 1.56/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.58    inference(nnf_transformation,[],[f2])).
% 1.56/0.58  fof(f2,axiom,(
% 1.56/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.58  fof(f75,plain,(
% 1.56/0.58    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)),
% 1.56/0.58    inference(forward_demodulation,[],[f74,f32])).
% 1.56/0.58  fof(f32,plain,(
% 1.56/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.56/0.58    inference(cnf_transformation,[],[f13])).
% 1.56/0.58  fof(f13,axiom,(
% 1.56/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.56/0.58  fof(f74,plain,(
% 1.56/0.58    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0))),
% 1.56/0.58    inference(resolution,[],[f65,f53])).
% 1.56/0.58  fof(f53,plain,(
% 1.56/0.58    v1_relat_1(k1_xboole_0)),
% 1.56/0.58    inference(resolution,[],[f36,f31])).
% 1.56/0.58  fof(f31,plain,(
% 1.56/0.58    v1_xboole_0(k1_xboole_0)),
% 1.56/0.58    inference(cnf_transformation,[],[f1])).
% 1.56/0.58  fof(f1,axiom,(
% 1.56/0.58    v1_xboole_0(k1_xboole_0)),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.56/0.58  fof(f36,plain,(
% 1.56/0.58    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f17])).
% 1.56/0.58  fof(f17,plain,(
% 1.56/0.58    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f8])).
% 1.56/0.58  fof(f8,axiom,(
% 1.56/0.58    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.56/0.58  fof(f65,plain,(
% 1.56/0.58    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k1_relat_1(k5_relat_1(X0,sK0)),k1_relat_1(X0))) )),
% 1.56/0.58    inference(resolution,[],[f39,f29])).
% 1.56/0.58  fof(f29,plain,(
% 1.56/0.58    v1_relat_1(sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f24])).
% 1.56/0.58  fof(f24,plain,(
% 1.56/0.58    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.56/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f23])).
% 1.56/0.58  fof(f23,plain,(
% 1.56/0.58    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.56/0.58    introduced(choice_axiom,[])).
% 1.56/0.58  fof(f16,plain,(
% 1.56/0.58    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f15])).
% 1.56/0.58  fof(f15,negated_conjecture,(
% 1.56/0.58    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.56/0.58    inference(negated_conjecture,[],[f14])).
% 1.56/0.58  fof(f14,conjecture,(
% 1.56/0.58    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.56/0.58  fof(f39,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f20])).
% 1.56/0.58  fof(f20,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f11])).
% 1.56/0.58  fof(f11,axiom,(
% 1.56/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 1.56/0.58  fof(f85,plain,(
% 1.56/0.58    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))),
% 1.56/0.58    inference(resolution,[],[f70,f37])).
% 1.56/0.58  fof(f37,plain,(
% 1.56/0.58    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 1.56/0.58    inference(cnf_transformation,[],[f18])).
% 1.56/0.58  fof(f18,plain,(
% 1.56/0.58    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f10])).
% 1.56/0.58  fof(f10,axiom,(
% 1.56/0.58    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.56/0.58  fof(f70,plain,(
% 1.56/0.58    v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.56/0.58    inference(resolution,[],[f54,f53])).
% 1.56/0.58  fof(f54,plain,(
% 1.56/0.58    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,sK0))) )),
% 1.56/0.58    inference(resolution,[],[f42,f29])).
% 1.56/0.58  fof(f42,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f22])).
% 1.56/0.58  fof(f22,plain,(
% 1.56/0.58    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.56/0.58    inference(flattening,[],[f21])).
% 1.56/0.58  fof(f21,plain,(
% 1.56/0.58    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f9])).
% 1.56/0.58  fof(f9,axiom,(
% 1.56/0.58    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.56/0.58  fof(f30,plain,(
% 1.56/0.58    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f24])).
% 1.56/0.58  fof(f167,plain,(
% 1.56/0.58    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.56/0.58    inference(forward_demodulation,[],[f166,f35])).
% 1.56/0.58  fof(f166,plain,(
% 1.56/0.58    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)),
% 1.56/0.58    inference(forward_demodulation,[],[f164,f51])).
% 1.56/0.58  fof(f51,plain,(
% 1.56/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.56/0.58    inference(equality_resolution,[],[f48])).
% 1.56/0.58  fof(f48,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.56/0.58    inference(cnf_transformation,[],[f28])).
% 1.56/0.58  fof(f164,plain,(
% 1.56/0.58    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))),
% 1.56/0.58    inference(backward_demodulation,[],[f131,f161])).
% 1.56/0.58  fof(f161,plain,(
% 1.56/0.58    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.56/0.58    inference(resolution,[],[f124,f56])).
% 1.56/0.58  fof(f124,plain,(
% 1.56/0.58    r1_tarski(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)),
% 1.56/0.58    inference(resolution,[],[f64,f29])).
% 1.56/0.58  fof(f64,plain,(
% 1.56/0.58    ( ! [X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0)) )),
% 1.56/0.58    inference(forward_demodulation,[],[f63,f33])).
% 1.56/0.58  fof(f33,plain,(
% 1.56/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.56/0.58    inference(cnf_transformation,[],[f13])).
% 1.56/0.58  fof(f63,plain,(
% 1.56/0.58    ( ! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,k1_xboole_0)),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(X1)) )),
% 1.56/0.58    inference(resolution,[],[f38,f53])).
% 1.56/0.58  fof(f38,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f19])).
% 1.56/0.58  fof(f19,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f12])).
% 1.56/0.58  fof(f12,axiom,(
% 1.56/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.56/0.58  fof(f131,plain,(
% 1.56/0.58    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))),
% 1.56/0.58    inference(resolution,[],[f121,f37])).
% 1.56/0.58  fof(f121,plain,(
% 1.56/0.58    v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.56/0.58    inference(resolution,[],[f55,f29])).
% 1.56/0.58  fof(f55,plain,(
% 1.56/0.58    ( ! [X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X1,k1_xboole_0))) )),
% 1.56/0.58    inference(resolution,[],[f42,f53])).
% 1.56/0.58  % SZS output end Proof for theBenchmark
% 1.56/0.58  % (11936)------------------------------
% 1.56/0.58  % (11936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (11936)Termination reason: Refutation
% 1.56/0.58  
% 1.56/0.58  % (11936)Memory used [KB]: 1791
% 1.56/0.58  % (11936)Time elapsed: 0.122 s
% 1.56/0.58  % (11936)------------------------------
% 1.56/0.58  % (11936)------------------------------
% 1.56/0.58  % (11928)Success in time 0.211 s
%------------------------------------------------------------------------------
