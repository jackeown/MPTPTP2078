%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 157 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  150 ( 347 expanded)
%              Number of equality atoms :   52 (  95 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f689,plain,(
    $false ),
    inference(resolution,[],[f681,f113])).

fof(f113,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f31,f95,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

% (7711)Refutation not found, incomplete strategy% (7711)------------------------------
% (7711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7722)Refutation not found, incomplete strategy% (7722)------------------------------
% (7722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7722)Termination reason: Refutation not found, incomplete strategy

% (7722)Memory used [KB]: 10874
% (7722)Time elapsed: 0.160 s
% (7722)------------------------------
% (7722)------------------------------
% (7710)Termination reason: Refutation not found, incomplete strategy

% (7710)Memory used [KB]: 10746
% (7710)Time elapsed: 0.150 s
% (7710)------------------------------
% (7710)------------------------------
% (7717)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (7717)Refutation not found, incomplete strategy% (7717)------------------------------
% (7717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7709)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (7717)Termination reason: Refutation not found, incomplete strategy

% (7717)Memory used [KB]: 10618
% (7717)Time elapsed: 0.141 s
% (7717)------------------------------
% (7717)------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f95,plain,(
    ! [X0] : r2_hidden(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f88,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f88,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),sK0) ),
    inference(unit_resulting_resolution,[],[f32,f80,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f80,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f69,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f69,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f31,f30,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f31,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f681,plain,(
    ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f680])).

fof(f680,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f258,f677])).

fof(f677,plain,(
    ! [X0] : k4_subset_1(sK0,sK2,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) ),
    inference(backward_demodulation,[],[f310,f676])).

fof(f676,plain,(
    ! [X0] : k3_tarski(k2_tarski(sK2,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) ),
    inference(forward_demodulation,[],[f668,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f668,plain,(
    ! [X0] : k3_tarski(k2_tarski(k4_xboole_0(sK0,X0),sK2)) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[],[f51,f577])).

fof(f577,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f28,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f132,f99])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f63,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f63,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f31,f59,f38])).

fof(f59,plain,(
    ! [X0,X1] : r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f32,f54])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f129])).

% (7711)Termination reason: Refutation not found, incomplete strategy

% (7711)Memory used [KB]: 10746
% (7711)Time elapsed: 0.162 s
% (7711)------------------------------
% (7711)------------------------------
fof(f129,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f41,f40])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k3_tarski(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(definition_unfolding,[],[f46,f34,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f310,plain,(
    ! [X0] : k4_subset_1(sK0,sK2,k4_xboole_0(sK0,X0)) = k3_tarski(k2_tarski(sK2,k4_xboole_0(sK0,X0))) ),
    inference(unit_resulting_resolution,[],[f28,f63,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f34])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f258,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_subset_1(sK0,sK2,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f152,f249])).

fof(f249,plain,(
    ! [X0] : k4_subset_1(sK0,sK2,k4_xboole_0(sK0,X0)) = k4_subset_1(sK0,k4_xboole_0(sK0,X0),sK2) ),
    inference(unit_resulting_resolution,[],[f28,f63,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f152,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f150,f145])).

fof(f145,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(sK0,sK1,X0) ),
    inference(unit_resulting_resolution,[],[f30,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f150,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | k4_xboole_0(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f102,f145])).

fof(f102,plain,
    ( k4_xboole_0(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2)
    | ~ m1_subset_1(k7_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f100,f98])).

fof(f98,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f30,f40])).

fof(f100,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) != k4_xboole_0(sK0,k7_subset_1(sK0,sK1,sK2))
    | ~ m1_subset_1(k7_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f29,f40])).

fof(f29,plain,(
    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:01:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (7724)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.51  % (7715)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (7715)Refutation not found, incomplete strategy% (7715)------------------------------
% 0.22/0.52  % (7715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7715)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7715)Memory used [KB]: 6140
% 0.22/0.52  % (7715)Time elapsed: 0.004 s
% 0.22/0.52  % (7715)------------------------------
% 0.22/0.52  % (7715)------------------------------
% 0.22/0.52  % (7705)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (7707)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (7704)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (7706)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (7729)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (7708)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (7702)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (7703)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (7728)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (7722)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (7727)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (7704)Refutation not found, incomplete strategy% (7704)------------------------------
% 0.22/0.55  % (7704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7704)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (7704)Memory used [KB]: 6268
% 0.22/0.55  % (7704)Time elapsed: 0.136 s
% 0.22/0.55  % (7704)------------------------------
% 0.22/0.55  % (7704)------------------------------
% 0.22/0.55  % (7723)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (7725)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (7720)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (7716)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (7718)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (7719)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (7700)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (7720)Refutation not found, incomplete strategy% (7720)------------------------------
% 0.22/0.55  % (7720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7720)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (7720)Memory used [KB]: 10746
% 0.22/0.55  % (7720)Time elapsed: 0.141 s
% 0.22/0.55  % (7720)------------------------------
% 0.22/0.55  % (7720)------------------------------
% 0.22/0.55  % (7700)Refutation not found, incomplete strategy% (7700)------------------------------
% 0.22/0.55  % (7700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7700)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (7700)Memory used [KB]: 1791
% 0.22/0.55  % (7700)Time elapsed: 0.134 s
% 0.22/0.55  % (7700)------------------------------
% 0.22/0.55  % (7700)------------------------------
% 0.22/0.55  % (7721)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (7713)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (7710)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (7721)Refutation not found, incomplete strategy% (7721)------------------------------
% 0.22/0.55  % (7721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7721)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (7721)Memory used [KB]: 1791
% 0.22/0.55  % (7721)Time elapsed: 0.140 s
% 0.22/0.55  % (7721)------------------------------
% 0.22/0.55  % (7721)------------------------------
% 0.22/0.55  % (7710)Refutation not found, incomplete strategy% (7710)------------------------------
% 0.22/0.55  % (7710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7712)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (7726)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (7714)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (7711)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (7701)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (7724)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f689,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(resolution,[],[f681,f113])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f31,f95,f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  % (7711)Refutation not found, incomplete strategy% (7711)------------------------------
% 0.22/0.57  % (7711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (7722)Refutation not found, incomplete strategy% (7722)------------------------------
% 0.22/0.57  % (7722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (7722)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (7722)Memory used [KB]: 10874
% 0.22/0.57  % (7722)Time elapsed: 0.160 s
% 0.22/0.57  % (7722)------------------------------
% 0.22/0.57  % (7722)------------------------------
% 0.22/0.57  % (7710)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (7710)Memory used [KB]: 10746
% 0.22/0.57  % (7710)Time elapsed: 0.150 s
% 0.22/0.57  % (7710)------------------------------
% 0.22/0.57  % (7710)------------------------------
% 0.22/0.57  % (7717)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (7717)Refutation not found, incomplete strategy% (7717)------------------------------
% 0.22/0.57  % (7717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (7709)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.58  % (7717)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (7717)Memory used [KB]: 10618
% 0.22/0.58  % (7717)Time elapsed: 0.141 s
% 0.22/0.58  % (7717)------------------------------
% 0.22/0.58  % (7717)------------------------------
% 1.61/0.58  fof(f9,axiom,(
% 1.61/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.61/0.58  fof(f95,plain,(
% 1.61/0.58    ( ! [X0] : (r2_hidden(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))) )),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f88,f54])).
% 1.61/0.58  fof(f54,plain,(
% 1.61/0.58    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 1.61/0.58    inference(equality_resolution,[],[f42])).
% 1.61/0.58  fof(f42,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.61/0.58    inference(cnf_transformation,[],[f6])).
% 1.61/0.58  fof(f6,axiom,(
% 1.61/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.61/0.58  fof(f88,plain,(
% 1.61/0.58    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),sK0)) )),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f32,f80,f48])).
% 1.61/0.58  fof(f48,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f23])).
% 1.61/0.58  fof(f23,plain,(
% 1.61/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.61/0.58    inference(flattening,[],[f22])).
% 1.61/0.58  fof(f22,plain,(
% 1.61/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.61/0.58    inference(ennf_transformation,[],[f1])).
% 1.61/0.58  fof(f1,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.61/0.58  fof(f80,plain,(
% 1.61/0.58    r1_tarski(sK1,sK0)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f69,f53])).
% 1.61/0.58  fof(f53,plain,(
% 1.61/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.61/0.58    inference(equality_resolution,[],[f43])).
% 1.61/0.58  fof(f43,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.61/0.58    inference(cnf_transformation,[],[f6])).
% 1.61/0.58  fof(f69,plain,(
% 1.61/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f31,f30,f39])).
% 1.61/0.58  fof(f39,plain,(
% 1.61/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f18])).
% 1.61/0.58  fof(f30,plain,(
% 1.61/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.61/0.58    inference(cnf_transformation,[],[f17])).
% 1.61/0.58  fof(f17,plain,(
% 1.61/0.58    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.58    inference(ennf_transformation,[],[f16])).
% 1.61/0.58  fof(f16,negated_conjecture,(
% 1.61/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 1.61/0.58    inference(negated_conjecture,[],[f15])).
% 1.61/0.58  fof(f15,conjecture,(
% 1.61/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 1.61/0.58  fof(f32,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f2])).
% 1.61/0.58  fof(f2,axiom,(
% 1.61/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.61/0.58  fof(f31,plain,(
% 1.61/0.58    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f11])).
% 1.61/0.58  fof(f11,axiom,(
% 1.61/0.58    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.61/0.58  fof(f681,plain,(
% 1.61/0.58    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 1.61/0.58    inference(trivial_inequality_removal,[],[f680])).
% 1.61/0.58  fof(f680,plain,(
% 1.61/0.58    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 1.61/0.58    inference(backward_demodulation,[],[f258,f677])).
% 1.61/0.58  fof(f677,plain,(
% 1.61/0.58    ( ! [X0] : (k4_subset_1(sK0,sK2,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2))) )),
% 1.61/0.58    inference(backward_demodulation,[],[f310,f676])).
% 1.61/0.58  fof(f676,plain,(
% 1.61/0.58    ( ! [X0] : (k3_tarski(k2_tarski(sK2,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2))) )),
% 1.61/0.58    inference(forward_demodulation,[],[f668,f33])).
% 1.61/0.58  fof(f33,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f5])).
% 1.61/0.58  fof(f5,axiom,(
% 1.61/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.61/0.58  fof(f668,plain,(
% 1.61/0.58    ( ! [X0] : (k3_tarski(k2_tarski(k4_xboole_0(sK0,X0),sK2)) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2))) )),
% 1.61/0.58    inference(superposition,[],[f51,f577])).
% 1.61/0.58  fof(f577,plain,(
% 1.61/0.58    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f28,f138])).
% 1.61/0.58  fof(f138,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.58    inference(forward_demodulation,[],[f132,f99])).
% 1.61/0.58  fof(f99,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))) )),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f63,f40])).
% 1.61/0.58  fof(f40,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f19])).
% 1.61/0.58  fof(f19,plain,(
% 1.61/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.58    inference(ennf_transformation,[],[f10])).
% 1.61/0.58  fof(f10,axiom,(
% 1.61/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.61/0.58  fof(f63,plain,(
% 1.61/0.58    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f31,f59,f38])).
% 1.61/0.58  fof(f59,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f32,f54])).
% 1.61/0.58  fof(f132,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.58    inference(duplicate_literal_removal,[],[f129])).
% 1.61/0.58  % (7711)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (7711)Memory used [KB]: 10746
% 1.61/0.58  % (7711)Time elapsed: 0.162 s
% 1.61/0.58  % (7711)------------------------------
% 1.61/0.58  % (7711)------------------------------
% 1.61/0.58  fof(f129,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.58    inference(superposition,[],[f41,f40])).
% 1.61/0.58  fof(f41,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f20])).
% 1.61/0.58  fof(f20,plain,(
% 1.61/0.58    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.58    inference(ennf_transformation,[],[f12])).
% 1.61/0.58  fof(f12,axiom,(
% 1.61/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.61/0.58  fof(f28,plain,(
% 1.61/0.58    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.61/0.58    inference(cnf_transformation,[],[f17])).
% 1.61/0.58  fof(f51,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k3_tarski(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))))) )),
% 1.61/0.58    inference(definition_unfolding,[],[f46,f34,f35])).
% 1.61/0.58  fof(f35,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f3])).
% 1.61/0.58  fof(f3,axiom,(
% 1.61/0.58    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.61/0.58  fof(f34,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f7])).
% 1.61/0.58  fof(f7,axiom,(
% 1.61/0.58    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.61/0.58  fof(f46,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f4])).
% 1.61/0.58  fof(f4,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.61/0.58  fof(f310,plain,(
% 1.61/0.58    ( ! [X0] : (k4_subset_1(sK0,sK2,k4_xboole_0(sK0,X0)) = k3_tarski(k2_tarski(sK2,k4_xboole_0(sK0,X0)))) )),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f28,f63,f52])).
% 1.61/0.58  fof(f52,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.58    inference(definition_unfolding,[],[f49,f34])).
% 1.61/0.58  fof(f49,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f25])).
% 1.61/0.58  fof(f25,plain,(
% 1.61/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.58    inference(flattening,[],[f24])).
% 1.61/0.58  fof(f24,plain,(
% 1.61/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.61/0.58    inference(ennf_transformation,[],[f13])).
% 1.61/0.58  fof(f13,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.61/0.58  fof(f258,plain,(
% 1.61/0.58    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_subset_1(sK0,sK2,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 1.61/0.58    inference(backward_demodulation,[],[f152,f249])).
% 1.61/0.58  fof(f249,plain,(
% 1.61/0.58    ( ! [X0] : (k4_subset_1(sK0,sK2,k4_xboole_0(sK0,X0)) = k4_subset_1(sK0,k4_xboole_0(sK0,X0),sK2)) )),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f28,f63,f50])).
% 1.61/0.58  fof(f50,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f27])).
% 1.61/0.58  fof(f27,plain,(
% 1.61/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.58    inference(flattening,[],[f26])).
% 1.61/0.58  fof(f26,plain,(
% 1.61/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.61/0.58    inference(ennf_transformation,[],[f8])).
% 1.61/0.58  fof(f8,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 1.61/0.58  fof(f152,plain,(
% 1.61/0.58    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 1.61/0.58    inference(forward_demodulation,[],[f150,f145])).
% 1.61/0.58  fof(f145,plain,(
% 1.61/0.58    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(sK0,sK1,X0)) )),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f30,f47])).
% 1.61/0.58  fof(f47,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f21])).
% 1.61/0.58  fof(f21,plain,(
% 1.61/0.58    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.58    inference(ennf_transformation,[],[f14])).
% 1.61/0.58  fof(f14,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.61/0.58  fof(f150,plain,(
% 1.61/0.58    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | k4_xboole_0(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2)),
% 1.61/0.58    inference(backward_demodulation,[],[f102,f145])).
% 1.61/0.58  fof(f102,plain,(
% 1.61/0.58    k4_xboole_0(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) | ~m1_subset_1(k7_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 1.61/0.58    inference(forward_demodulation,[],[f100,f98])).
% 1.61/0.58  fof(f98,plain,(
% 1.61/0.58    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f30,f40])).
% 1.61/0.58  fof(f100,plain,(
% 1.61/0.58    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) != k4_xboole_0(sK0,k7_subset_1(sK0,sK1,sK2)) | ~m1_subset_1(k7_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 1.61/0.58    inference(superposition,[],[f29,f40])).
% 1.61/0.58  fof(f29,plain,(
% 1.61/0.58    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)),
% 1.61/0.58    inference(cnf_transformation,[],[f17])).
% 1.61/0.58  % SZS output end Proof for theBenchmark
% 1.61/0.58  % (7724)------------------------------
% 1.61/0.58  % (7724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (7724)Termination reason: Refutation
% 1.61/0.58  
% 1.61/0.58  % (7724)Memory used [KB]: 7164
% 1.61/0.58  % (7724)Time elapsed: 0.102 s
% 1.61/0.58  % (7724)------------------------------
% 1.61/0.58  % (7724)------------------------------
% 1.61/0.58  % (7699)Success in time 0.209 s
%------------------------------------------------------------------------------
