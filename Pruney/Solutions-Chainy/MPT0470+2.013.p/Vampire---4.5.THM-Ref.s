%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 454 expanded)
%              Number of leaves         :   21 ( 129 expanded)
%              Depth                    :   18
%              Number of atoms          :  196 ( 921 expanded)
%              Number of equality atoms :   83 ( 480 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f547,plain,(
    $false ),
    inference(subsumption_resolution,[],[f546,f228])).

fof(f228,plain,(
    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f214])).

fof(f214,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f47,f213])).

fof(f213,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f212,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f212,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f210,f152])).

fof(f152,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2) ),
    inference(resolution,[],[f85,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f85,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0)) ),
    inference(resolution,[],[f67,f48])).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f210,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) ),
    inference(backward_demodulation,[],[f165,f207])).

fof(f207,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f123,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f71,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f123,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f121,f49])).

fof(f49,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f121,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f104,f81])).

fof(f81,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f54,f48])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,sK0)),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f59,f46])).

fof(f46,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f165,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) ),
    inference(resolution,[],[f116,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f116,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f91,f81])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,sK0)) ) ),
    inference(resolution,[],[f68,f46])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f47,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f546,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f521,f144])).

fof(f144,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f143,f96])).

fof(f96,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f95,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f95,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f66,f62])).

fof(f62,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f143,plain,(
    k4_relat_1(k1_xboole_0) = k4_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f141,f96])).

fof(f141,plain,(
    k4_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k4_xboole_0(sK0,sK0)) ),
    inference(resolution,[],[f111,f46])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_xboole_0(k4_relat_1(X0),k4_relat_1(sK0)) = k4_relat_1(k4_xboole_0(X0,sK0)) ) ),
    inference(resolution,[],[f80,f46])).

% (22819)Refutation not found, incomplete strategy% (22819)------------------------------
% (22819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22819)Termination reason: Refutation not found, incomplete strategy

% (22819)Memory used [KB]: 10746
% (22819)Time elapsed: 0.142 s
% (22819)------------------------------
% (22819)------------------------------
% (22803)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% (22809)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (22820)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (22820)Refutation not found, incomplete strategy% (22820)------------------------------
% (22820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22820)Termination reason: Refutation not found, incomplete strategy

% (22820)Memory used [KB]: 1663
% (22820)Time elapsed: 0.141 s
% (22820)------------------------------
% (22820)------------------------------
% (22801)Refutation not found, incomplete strategy% (22801)------------------------------
% (22801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22801)Termination reason: Refutation not found, incomplete strategy

% (22801)Memory used [KB]: 10618
% (22801)Time elapsed: 0.153 s
% (22801)------------------------------
% (22801)------------------------------
fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f79,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k6_subset_1(X0,X1)) = k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f60,f63])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

fof(f521,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f292,f518])).

fof(f518,plain,(
    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f517,f52])).

fof(f517,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f515,f152])).

fof(f515,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))))) ),
    inference(backward_demodulation,[],[f378,f510])).

fof(f510,plain,(
    k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f283,f97])).

fof(f283,plain,(
    r1_tarski(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f258,f276])).

fof(f276,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f148,f46])).

fof(f148,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X1)) ) ),
    inference(backward_demodulation,[],[f108,f144])).

fof(f108,plain,(
    ! [X1] :
      ( k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f61,f81])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f258,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f252,f49])).

fof(f252,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f106,f81])).

fof(f106,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k1_relat_1(k5_relat_1(X2,k4_relat_1(sK0))),k1_relat_1(X2)) ) ),
    inference(resolution,[],[f59,f83])).

fof(f83,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f56,f46])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f378,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))))) ),
    inference(resolution,[],[f284,f58])).

fof(f284,plain,(
    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f243,f276])).

fof(f243,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f93,f81])).

fof(f93,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | v1_relat_1(k5_relat_1(X2,k4_relat_1(sK0))) ) ),
    inference(resolution,[],[f68,f83])).

fof(f292,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f291,f276])).

fof(f291,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f285,f144])).

fof(f285,plain,(
    k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f110,f81])).

fof(f110,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k4_relat_1(k5_relat_1(X2,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X2)) ) ),
    inference(forward_demodulation,[],[f109,f86])).

fof(f86,plain,(
    sK0 = k4_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f57,f46])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f109,plain,(
    ! [X2] :
      ( k4_relat_1(k5_relat_1(X2,k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f61,f83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (22816)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.50  % (22797)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (22791)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (22799)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (22796)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (22808)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.50  % (22814)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (22806)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (22798)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (22795)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (22802)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (22800)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (22794)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (22811)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (22805)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (22810)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (22801)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (22792)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (22793)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (22804)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (22815)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (22813)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (22807)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (22807)Refutation not found, incomplete strategy% (22807)------------------------------
% 0.20/0.53  % (22807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (22807)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (22807)Memory used [KB]: 10618
% 0.20/0.53  % (22807)Time elapsed: 0.129 s
% 0.20/0.53  % (22807)------------------------------
% 0.20/0.53  % (22807)------------------------------
% 0.20/0.53  % (22812)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (22818)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (22817)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (22819)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (22798)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f547,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f546,f228])).
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f214])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.53    inference(backward_demodulation,[],[f47,f213])).
% 0.20/0.53  fof(f213,plain,(
% 0.20/0.53    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.53    inference(forward_demodulation,[],[f212,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)),
% 0.20/0.53    inference(forward_demodulation,[],[f210,f152])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2)) )),
% 0.20/0.53    inference(resolution,[],[f85,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0))) )),
% 0.20/0.53    inference(resolution,[],[f67,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))),
% 0.20/0.53    inference(backward_demodulation,[],[f165,f207])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.53    inference(resolution,[],[f123,f97])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(resolution,[],[f71,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)),
% 0.20/0.53    inference(forward_demodulation,[],[f121,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,axiom,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0))),
% 0.20/0.53    inference(resolution,[],[f104,f81])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    v1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f54,f48])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k1_relat_1(k5_relat_1(X0,sK0)),k1_relat_1(X0))) )),
% 0.20/0.53    inference(resolution,[],[f59,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    v1_relat_1(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.53    inference(negated_conjecture,[],[f27])).
% 0.20/0.53  fof(f27,conjecture,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))),
% 0.20/0.53    inference(resolution,[],[f116,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.53    inference(resolution,[],[f91,f81])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,sK0))) )),
% 0.20/0.53    inference(resolution,[],[f68,f46])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f546,plain,(
% 0.20/0.53    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.53    inference(forward_demodulation,[],[f521,f144])).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(forward_demodulation,[],[f143,f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f95,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 0.20/0.53    inference(superposition,[],[f66,f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.53    inference(rectify,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    k4_relat_1(k1_xboole_0) = k4_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0))),
% 0.20/0.53    inference(forward_demodulation,[],[f141,f96])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    k4_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k4_xboole_0(sK0,sK0))),
% 0.20/0.53    inference(resolution,[],[f111,f46])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | k4_xboole_0(k4_relat_1(X0),k4_relat_1(sK0)) = k4_relat_1(k4_xboole_0(X0,sK0))) )),
% 0.20/0.53    inference(resolution,[],[f80,f46])).
% 0.20/0.53  % (22819)Refutation not found, incomplete strategy% (22819)------------------------------
% 0.20/0.53  % (22819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (22819)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (22819)Memory used [KB]: 10746
% 0.20/0.53  % (22819)Time elapsed: 0.142 s
% 0.20/0.53  % (22819)------------------------------
% 0.20/0.53  % (22819)------------------------------
% 0.20/0.54  % (22803)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (22809)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (22820)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (22820)Refutation not found, incomplete strategy% (22820)------------------------------
% 0.20/0.54  % (22820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22820)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22820)Memory used [KB]: 1663
% 0.20/0.54  % (22820)Time elapsed: 0.141 s
% 0.20/0.54  % (22820)------------------------------
% 0.20/0.54  % (22820)------------------------------
% 0.20/0.54  % (22801)Refutation not found, incomplete strategy% (22801)------------------------------
% 0.20/0.54  % (22801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22801)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22801)Memory used [KB]: 10618
% 0.20/0.54  % (22801)Time elapsed: 0.153 s
% 0.20/0.54  % (22801)------------------------------
% 0.20/0.54  % (22801)------------------------------
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f79,f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,axiom,(
% 0.20/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f60,f63])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).
% 0.20/0.55  fof(f521,plain,(
% 0.20/0.55    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)),
% 0.20/0.55    inference(backward_demodulation,[],[f292,f518])).
% 0.20/0.55  fof(f518,plain,(
% 0.20/0.55    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.55    inference(forward_demodulation,[],[f517,f52])).
% 0.20/0.55  fof(f517,plain,(
% 0.20/0.55    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)),
% 0.20/0.55    inference(forward_demodulation,[],[f515,f152])).
% 0.20/0.55  fof(f515,plain,(
% 0.20/0.55    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))),
% 0.20/0.55    inference(backward_demodulation,[],[f378,f510])).
% 0.20/0.55  fof(f510,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.20/0.55    inference(resolution,[],[f283,f97])).
% 0.20/0.55  fof(f283,plain,(
% 0.20/0.55    r1_tarski(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0)),
% 0.20/0.55    inference(backward_demodulation,[],[f258,f276])).
% 0.20/0.55  fof(f276,plain,(
% 0.20/0.55    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.55    inference(resolution,[],[f148,f46])).
% 0.20/0.55  fof(f148,plain,(
% 0.20/0.55    ( ! [X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X1))) )),
% 0.20/0.55    inference(backward_demodulation,[],[f108,f144])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    ( ! [X1] : (k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(resolution,[],[f61,f81])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.20/0.55  fof(f258,plain,(
% 0.20/0.55    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_xboole_0)),
% 0.20/0.55    inference(forward_demodulation,[],[f252,f49])).
% 0.20/0.55  fof(f252,plain,(
% 0.20/0.55    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_relat_1(k1_xboole_0))),
% 0.20/0.55    inference(resolution,[],[f106,f81])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    ( ! [X2] : (~v1_relat_1(X2) | r1_tarski(k1_relat_1(k5_relat_1(X2,k4_relat_1(sK0))),k1_relat_1(X2))) )),
% 0.20/0.55    inference(resolution,[],[f59,f83])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.55    inference(resolution,[],[f56,f46])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.20/0.55  fof(f378,plain,(
% 0.20/0.55    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))),
% 0.20/0.55    inference(resolution,[],[f284,f58])).
% 0.20/0.55  fof(f284,plain,(
% 0.20/0.55    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.20/0.55    inference(backward_demodulation,[],[f243,f276])).
% 0.20/0.55  fof(f243,plain,(
% 0.20/0.55    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 0.20/0.55    inference(resolution,[],[f93,f81])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    ( ! [X2] : (~v1_relat_1(X2) | v1_relat_1(k5_relat_1(X2,k4_relat_1(sK0)))) )),
% 0.20/0.55    inference(resolution,[],[f68,f83])).
% 0.20/0.55  fof(f292,plain,(
% 0.20/0.55    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.20/0.55    inference(forward_demodulation,[],[f291,f276])).
% 0.20/0.55  fof(f291,plain,(
% 0.20/0.55    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 0.20/0.55    inference(forward_demodulation,[],[f285,f144])).
% 0.20/0.55  fof(f285,plain,(
% 0.20/0.55    k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0))),
% 0.20/0.55    inference(resolution,[],[f110,f81])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    ( ! [X2] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(X2,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X2))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f109,f86])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    sK0 = k4_relat_1(k4_relat_1(sK0))),
% 0.20/0.55    inference(resolution,[],[f57,f46])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    ( ! [X2] : (k4_relat_1(k5_relat_1(X2,k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.55    inference(resolution,[],[f61,f83])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (22798)------------------------------
% 0.20/0.55  % (22798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22798)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (22798)Memory used [KB]: 2174
% 0.20/0.55  % (22798)Time elapsed: 0.140 s
% 0.20/0.55  % (22798)------------------------------
% 0.20/0.55  % (22798)------------------------------
% 0.20/0.55  % (22790)Success in time 0.193 s
%------------------------------------------------------------------------------
