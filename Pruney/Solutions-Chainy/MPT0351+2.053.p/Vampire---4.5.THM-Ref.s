%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:10 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   60 (  93 expanded)
%              Number of leaves         :   14 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  112 ( 177 expanded)
%              Number of equality atoms :   43 (  70 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(subsumption_resolution,[],[f66,f44])).

fof(f44,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(forward_demodulation,[],[f28,f29])).

fof(f29,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f28,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f66,plain,(
    sK0 = k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f53,f65])).

fof(f65,plain,(
    sK0 = k4_subset_1(sK0,sK0,sK1) ),
    inference(backward_demodulation,[],[f62,f64])).

fof(f64,plain,(
    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(superposition,[],[f42,f55])).

fof(f55,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f54,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f54,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f50,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f50,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f48,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f32,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f62,plain,(
    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f60,f29])).

fof(f60,plain,(
    k4_subset_1(sK0,k2_subset_1(sK0),sK1) = k3_tarski(k1_enumset1(k2_subset_1(sK0),k2_subset_1(sK0),sK1)) ),
    inference(resolution,[],[f46,f30])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f46,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X1,sK1) = k3_tarski(k1_enumset1(X1,X1,sK1)) ) ),
    inference(resolution,[],[f27,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f53,plain,(
    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f51,f29])).

fof(f51,plain,(
    k4_subset_1(sK0,sK1,k2_subset_1(sK0)) = k4_subset_1(sK0,k2_subset_1(sK0),sK1) ),
    inference(resolution,[],[f45,f30])).

fof(f45,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k4_subset_1(sK0,sK1,X0) ) ),
    inference(resolution,[],[f27,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (13098)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.46  % (13081)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (13081)Refutation not found, incomplete strategy% (13081)------------------------------
% 0.20/0.46  % (13081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (13081)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (13081)Memory used [KB]: 10618
% 0.20/0.46  % (13081)Time elapsed: 0.056 s
% 0.20/0.46  % (13081)------------------------------
% 0.20/0.46  % (13081)------------------------------
% 0.20/0.46  % (13098)Refutation not found, incomplete strategy% (13098)------------------------------
% 0.20/0.46  % (13098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (13098)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (13098)Memory used [KB]: 10746
% 0.20/0.46  % (13098)Time elapsed: 0.058 s
% 0.20/0.46  % (13098)------------------------------
% 0.20/0.46  % (13098)------------------------------
% 1.22/0.51  % (13079)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.22/0.51  % (13079)Refutation found. Thanks to Tanya!
% 1.22/0.51  % SZS status Theorem for theBenchmark
% 1.22/0.51  % SZS output start Proof for theBenchmark
% 1.22/0.51  fof(f67,plain,(
% 1.22/0.51    $false),
% 1.22/0.51    inference(subsumption_resolution,[],[f66,f44])).
% 1.22/0.51  fof(f44,plain,(
% 1.22/0.51    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 1.22/0.51    inference(forward_demodulation,[],[f28,f29])).
% 1.22/0.51  fof(f29,plain,(
% 1.22/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.22/0.51    inference(cnf_transformation,[],[f8])).
% 1.22/0.51  fof(f8,axiom,(
% 1.22/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.22/0.51  fof(f28,plain,(
% 1.22/0.51    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.22/0.51    inference(cnf_transformation,[],[f24])).
% 1.22/0.51  fof(f24,plain,(
% 1.22/0.51    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23])).
% 1.22/0.51  fof(f23,plain,(
% 1.22/0.51    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.22/0.51    introduced(choice_axiom,[])).
% 1.22/0.51  fof(f15,plain,(
% 1.22/0.51    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.51    inference(ennf_transformation,[],[f13])).
% 1.22/0.51  fof(f13,negated_conjecture,(
% 1.22/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.22/0.51    inference(negated_conjecture,[],[f12])).
% 1.22/0.51  fof(f12,conjecture,(
% 1.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 1.22/0.51  fof(f66,plain,(
% 1.22/0.51    sK0 = k4_subset_1(sK0,sK1,sK0)),
% 1.22/0.51    inference(backward_demodulation,[],[f53,f65])).
% 1.22/0.51  fof(f65,plain,(
% 1.22/0.51    sK0 = k4_subset_1(sK0,sK0,sK1)),
% 1.22/0.51    inference(backward_demodulation,[],[f62,f64])).
% 1.22/0.51  fof(f64,plain,(
% 1.22/0.51    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.22/0.51    inference(superposition,[],[f42,f55])).
% 1.22/0.51  fof(f55,plain,(
% 1.22/0.51    sK1 = k3_xboole_0(sK0,sK1)),
% 1.22/0.51    inference(superposition,[],[f54,f31])).
% 1.22/0.51  fof(f31,plain,(
% 1.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f1])).
% 1.22/0.51  fof(f1,axiom,(
% 1.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.22/0.51  fof(f54,plain,(
% 1.22/0.51    sK1 = k3_xboole_0(sK1,sK0)),
% 1.22/0.51    inference(resolution,[],[f50,f35])).
% 1.22/0.51  fof(f35,plain,(
% 1.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.22/0.51    inference(cnf_transformation,[],[f16])).
% 1.22/0.51  fof(f16,plain,(
% 1.22/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.22/0.51    inference(ennf_transformation,[],[f4])).
% 1.22/0.51  fof(f4,axiom,(
% 1.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.22/0.51  fof(f50,plain,(
% 1.22/0.51    r1_tarski(sK1,sK0)),
% 1.22/0.51    inference(duplicate_literal_removal,[],[f49])).
% 1.22/0.51  fof(f49,plain,(
% 1.22/0.51    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 1.22/0.51    inference(resolution,[],[f48,f38])).
% 1.22/0.51  fof(f38,plain,(
% 1.22/0.51    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f26])).
% 1.22/0.51  fof(f26,plain,(
% 1.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f25])).
% 1.22/0.51  fof(f25,plain,(
% 1.22/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.22/0.51    introduced(choice_axiom,[])).
% 1.22/0.51  fof(f18,plain,(
% 1.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.22/0.51    inference(ennf_transformation,[],[f14])).
% 1.22/0.51  fof(f14,plain,(
% 1.22/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.22/0.51    inference(unused_predicate_definition_removal,[],[f2])).
% 1.22/0.51  fof(f2,axiom,(
% 1.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.22/0.51  fof(f48,plain,(
% 1.22/0.51    ( ! [X0] : (r2_hidden(sK2(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 1.22/0.51    inference(resolution,[],[f47,f37])).
% 1.22/0.51  fof(f37,plain,(
% 1.22/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f26])).
% 1.22/0.51  fof(f47,plain,(
% 1.22/0.51    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,sK0)) )),
% 1.22/0.51    inference(resolution,[],[f27,f36])).
% 1.22/0.51  fof(f36,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f17])).
% 1.22/0.51  fof(f17,plain,(
% 1.22/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.51    inference(ennf_transformation,[],[f10])).
% 1.22/0.51  fof(f10,axiom,(
% 1.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.22/0.51  fof(f27,plain,(
% 1.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.22/0.51    inference(cnf_transformation,[],[f24])).
% 1.22/0.51  fof(f42,plain,(
% 1.22/0.51    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 1.22/0.51    inference(definition_unfolding,[],[f32,f41])).
% 1.22/0.51  fof(f41,plain,(
% 1.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.22/0.51    inference(definition_unfolding,[],[f33,f34])).
% 1.22/0.51  fof(f34,plain,(
% 1.22/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f5])).
% 1.22/0.52  fof(f5,axiom,(
% 1.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.22/0.52  fof(f33,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f6])).
% 1.22/0.52  fof(f6,axiom,(
% 1.22/0.52    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.22/0.52  fof(f32,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.22/0.52    inference(cnf_transformation,[],[f3])).
% 1.22/0.52  fof(f3,axiom,(
% 1.22/0.52    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.22/0.52  fof(f62,plain,(
% 1.22/0.52    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.22/0.52    inference(forward_demodulation,[],[f60,f29])).
% 1.22/0.52  fof(f60,plain,(
% 1.22/0.52    k4_subset_1(sK0,k2_subset_1(sK0),sK1) = k3_tarski(k1_enumset1(k2_subset_1(sK0),k2_subset_1(sK0),sK1))),
% 1.22/0.52    inference(resolution,[],[f46,f30])).
% 1.22/0.52  fof(f30,plain,(
% 1.22/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f9])).
% 1.22/0.52  fof(f9,axiom,(
% 1.22/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.22/0.52  fof(f46,plain,(
% 1.22/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X1,sK1) = k3_tarski(k1_enumset1(X1,X1,sK1))) )),
% 1.22/0.52    inference(resolution,[],[f27,f43])).
% 1.22/0.52  fof(f43,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.22/0.52    inference(definition_unfolding,[],[f39,f41])).
% 1.22/0.52  fof(f39,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f20])).
% 1.22/0.52  fof(f20,plain,(
% 1.22/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.52    inference(flattening,[],[f19])).
% 1.22/0.52  fof(f19,plain,(
% 1.22/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.22/0.52    inference(ennf_transformation,[],[f11])).
% 1.22/0.52  fof(f11,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.22/0.52  fof(f53,plain,(
% 1.22/0.52    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)),
% 1.22/0.52    inference(forward_demodulation,[],[f51,f29])).
% 1.22/0.52  fof(f51,plain,(
% 1.22/0.52    k4_subset_1(sK0,sK1,k2_subset_1(sK0)) = k4_subset_1(sK0,k2_subset_1(sK0),sK1)),
% 1.22/0.52    inference(resolution,[],[f45,f30])).
% 1.22/0.52  fof(f45,plain,(
% 1.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k4_subset_1(sK0,sK1,X0)) )),
% 1.22/0.52    inference(resolution,[],[f27,f40])).
% 1.22/0.52  fof(f40,plain,(
% 1.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f22])).
% 1.22/0.52  fof(f22,plain,(
% 1.22/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.52    inference(flattening,[],[f21])).
% 1.22/0.52  fof(f21,plain,(
% 1.22/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.22/0.52    inference(ennf_transformation,[],[f7])).
% 1.22/0.52  fof(f7,axiom,(
% 1.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 1.22/0.52  % SZS output end Proof for theBenchmark
% 1.22/0.52  % (13079)------------------------------
% 1.22/0.52  % (13079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (13079)Termination reason: Refutation
% 1.22/0.52  
% 1.22/0.52  % (13079)Memory used [KB]: 10746
% 1.22/0.52  % (13079)Time elapsed: 0.109 s
% 1.22/0.52  % (13079)------------------------------
% 1.22/0.52  % (13079)------------------------------
% 1.22/0.52  % (13076)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.22/0.52  % (13085)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.52  % (13096)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.22/0.52  % (13073)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.53  % (13087)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.53  % (13089)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.53  % (13074)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.53  % (13075)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.53  % (13099)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.53  % (13075)Refutation not found, incomplete strategy% (13075)------------------------------
% 1.37/0.53  % (13075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (13075)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (13075)Memory used [KB]: 6140
% 1.37/0.53  % (13075)Time elapsed: 0.129 s
% 1.37/0.53  % (13075)------------------------------
% 1.37/0.53  % (13075)------------------------------
% 1.37/0.53  % (13070)Success in time 0.176 s
%------------------------------------------------------------------------------
