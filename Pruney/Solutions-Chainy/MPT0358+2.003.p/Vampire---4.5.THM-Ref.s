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
% DateTime   : Thu Dec  3 12:44:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 144 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :  161 ( 362 expanded)
%              Number of equality atoms :   47 ( 121 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f60,f64,f139])).

% (27135)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f139,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f137,f116])).

fof(f116,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f115,f58])).

fof(f58,plain,
    ( k1_xboole_0 != sK1
    | spl2_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f115,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 = sK1
    | ~ spl2_1 ),
    inference(resolution,[],[f73,f53])).

fof(f53,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_1
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

% (27139)Refutation not found, incomplete strategy% (27139)------------------------------
% (27139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27123)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (27139)Termination reason: Refutation not found, incomplete strategy

% (27139)Memory used [KB]: 10618
% (27139)Time elapsed: 0.084 s
% (27139)------------------------------
% (27139)------------------------------
% (27143)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (27124)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (27137)Refutation not found, incomplete strategy% (27137)------------------------------
% (27137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27137)Termination reason: Refutation not found, incomplete strategy

% (27137)Memory used [KB]: 10746
% (27137)Time elapsed: 0.179 s
% (27137)------------------------------
% (27137)------------------------------
% (27127)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (27117)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (27141)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (27128)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (27128)Refutation not found, incomplete strategy% (27128)------------------------------
% (27128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27128)Termination reason: Refutation not found, incomplete strategy

% (27128)Memory used [KB]: 10618
% (27128)Time elapsed: 0.153 s
% (27128)------------------------------
% (27128)------------------------------
% (27125)Refutation not found, incomplete strategy% (27125)------------------------------
% (27125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27125)Termination reason: Refutation not found, incomplete strategy

% (27125)Memory used [KB]: 10618
% (27125)Time elapsed: 0.157 s
% (27125)------------------------------
% (27125)------------------------------
% (27117)Refutation not found, incomplete strategy% (27117)------------------------------
% (27117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27117)Termination reason: Refutation not found, incomplete strategy

% (27117)Memory used [KB]: 1663
% (27117)Time elapsed: 0.163 s
% (27117)------------------------------
% (27117)------------------------------
fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f42,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f137,plain,(
    r1_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f133,f126])).

fof(f126,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f124,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f124,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f122,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f122,plain,(
    r1_tarski(sK1,sK0) ),
    inference(forward_demodulation,[],[f121,f49])).

fof(f49,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f34,f46])).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f121,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f120,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f120,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f117,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,k3_subset_1(sK0,X0))
      | ~ r1_tarski(X0,k3_subset_1(sK0,sK1)) ) ),
    inference(resolution,[],[f45,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k1_subset_1(sK0)
        | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & ( sK1 = k1_subset_1(sK0)
        | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f133,plain,(
    r1_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f96,f126])).

fof(f96,plain,(
    r1_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f40,f91])).

fof(f91,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f50,f29])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

% (27127)Refutation not found, incomplete strategy% (27127)------------------------------
% (27127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27127)Termination reason: Refutation not found, incomplete strategy

% (27127)Memory used [KB]: 10618
% (27127)Time elapsed: 0.164 s
% (27127)------------------------------
% (27127)------------------------------
fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f64,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f32,f62])).

fof(f62,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f54,f57])).

fof(f57,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f54,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f60,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f48,f56,f52])).

fof(f48,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f30,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f47,f56,f52])).

fof(f47,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f31,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.55  % (27121)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (27119)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (27133)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (27144)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (27119)Refutation not found, incomplete strategy% (27119)------------------------------
% 0.22/0.56  % (27119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27119)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (27119)Memory used [KB]: 10618
% 0.22/0.56  % (27119)Time elapsed: 0.142 s
% 0.22/0.56  % (27119)------------------------------
% 0.22/0.56  % (27119)------------------------------
% 0.22/0.56  % (27129)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (27132)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (27132)Refutation not found, incomplete strategy% (27132)------------------------------
% 0.22/0.56  % (27132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27132)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (27132)Memory used [KB]: 6140
% 0.22/0.56  % (27132)Time elapsed: 0.004 s
% 0.22/0.56  % (27132)------------------------------
% 0.22/0.56  % (27132)------------------------------
% 0.22/0.57  % (27139)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (27137)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.57  % (27120)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.57  % (27136)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.57  % (27125)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (27131)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.57  % (27145)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (27120)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f141,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f59,f60,f64,f139])).
% 0.22/0.57  % (27135)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.57  fof(f139,plain,(
% 0.22/0.57    ~spl2_1 | spl2_2),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f138])).
% 0.22/0.57  fof(f138,plain,(
% 0.22/0.57    $false | (~spl2_1 | spl2_2)),
% 0.22/0.57    inference(subsumption_resolution,[],[f137,f116])).
% 0.22/0.57  fof(f116,plain,(
% 0.22/0.57    ~r1_xboole_0(sK1,k3_subset_1(sK0,sK1)) | (~spl2_1 | spl2_2)),
% 0.22/0.57    inference(subsumption_resolution,[],[f115,f58])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    k1_xboole_0 != sK1 | spl2_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    spl2_2 <=> k1_xboole_0 = sK1),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.57  fof(f115,plain,(
% 0.22/0.57    ~r1_xboole_0(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 = sK1 | ~spl2_1),
% 0.22/0.57    inference(resolution,[],[f73,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl2_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    spl2_1 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.57  % (27139)Refutation not found, incomplete strategy% (27139)------------------------------
% 0.22/0.57  % (27139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (27123)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (27139)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (27139)Memory used [KB]: 10618
% 0.22/0.57  % (27139)Time elapsed: 0.084 s
% 0.22/0.57  % (27139)------------------------------
% 0.22/0.57  % (27139)------------------------------
% 0.22/0.58  % (27143)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.58  % (27124)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.58  % (27137)Refutation not found, incomplete strategy% (27137)------------------------------
% 0.22/0.58  % (27137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (27137)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (27137)Memory used [KB]: 10746
% 0.22/0.58  % (27137)Time elapsed: 0.179 s
% 0.22/0.58  % (27137)------------------------------
% 0.22/0.58  % (27137)------------------------------
% 0.22/0.58  % (27127)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.58  % (27117)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.58  % (27141)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.58  % (27128)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.59  % (27128)Refutation not found, incomplete strategy% (27128)------------------------------
% 0.22/0.59  % (27128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (27128)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (27128)Memory used [KB]: 10618
% 0.22/0.59  % (27128)Time elapsed: 0.153 s
% 0.22/0.59  % (27128)------------------------------
% 0.22/0.59  % (27128)------------------------------
% 0.22/0.59  % (27125)Refutation not found, incomplete strategy% (27125)------------------------------
% 0.22/0.59  % (27125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (27125)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (27125)Memory used [KB]: 10618
% 0.22/0.59  % (27125)Time elapsed: 0.157 s
% 0.22/0.59  % (27125)------------------------------
% 0.22/0.59  % (27125)------------------------------
% 0.22/0.59  % (27117)Refutation not found, incomplete strategy% (27117)------------------------------
% 0.22/0.59  % (27117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (27117)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (27117)Memory used [KB]: 1663
% 0.22/0.59  % (27117)Time elapsed: 0.163 s
% 0.22/0.59  % (27117)------------------------------
% 0.22/0.59  % (27117)------------------------------
% 0.22/0.59  fof(f73,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1) | k1_xboole_0 = X0) )),
% 0.22/0.59    inference(resolution,[],[f42,f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.59    inference(flattening,[],[f19])).
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.59  fof(f137,plain,(
% 0.22/0.59    r1_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.59    inference(forward_demodulation,[],[f133,f126])).
% 0.22/0.59  fof(f126,plain,(
% 0.22/0.59    sK1 = k3_xboole_0(sK0,sK1)),
% 0.22/0.59    inference(superposition,[],[f124,f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.59  fof(f124,plain,(
% 0.22/0.59    sK1 = k3_xboole_0(sK1,sK0)),
% 0.22/0.59    inference(resolution,[],[f122,f43])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f21])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.59  fof(f122,plain,(
% 0.22/0.59    r1_tarski(sK1,sK0)),
% 0.22/0.59    inference(forward_demodulation,[],[f121,f49])).
% 0.22/0.59  fof(f49,plain,(
% 0.22/0.59    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.59    inference(definition_unfolding,[],[f34,f46])).
% 0.22/0.59  fof(f46,plain,(
% 0.22/0.59    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f36,f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f9])).
% 0.22/0.59  fof(f9,axiom,(
% 0.22/0.59    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,axiom,(
% 0.22/0.59    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.59  fof(f121,plain,(
% 0.22/0.59    r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0))),
% 0.22/0.59    inference(subsumption_resolution,[],[f120,f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.59  fof(f120,plain,(
% 0.22/0.59    r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0)) | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK1))),
% 0.22/0.59    inference(resolution,[],[f117,f35])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,axiom,(
% 0.22/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.59  fof(f117,plain,(
% 0.22/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK1,k3_subset_1(sK0,X0)) | ~r1_tarski(X0,k3_subset_1(sK0,sK1))) )),
% 0.22/0.59    inference(resolution,[],[f45,f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.59    inference(cnf_transformation,[],[f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(flattening,[],[f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(nnf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.59    inference(negated_conjecture,[],[f15])).
% 0.22/0.59  fof(f15,conjecture,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_tarski(X2,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(flattening,[],[f23])).
% 0.22/0.59  fof(f23,plain,(
% 0.22/0.59    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 0.22/0.59  fof(f133,plain,(
% 0.22/0.59    r1_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))),
% 0.22/0.59    inference(backward_demodulation,[],[f96,f126])).
% 0.22/0.59  fof(f96,plain,(
% 0.22/0.59    r1_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_subset_1(sK0,sK1))),
% 0.22/0.59    inference(superposition,[],[f40,f91])).
% 0.22/0.59  fof(f91,plain,(
% 0.22/0.59    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.59    inference(resolution,[],[f50,f29])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f44,f41])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f22])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f4])).
% 0.22/0.59  % (27127)Refutation not found, incomplete strategy% (27127)------------------------------
% 0.22/0.59  % (27127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (27127)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (27127)Memory used [KB]: 10618
% 0.22/0.59  % (27127)Time elapsed: 0.164 s
% 0.22/0.59  % (27127)------------------------------
% 0.22/0.59  % (27127)------------------------------
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.22/0.59  fof(f64,plain,(
% 0.22/0.59    spl2_1 | ~spl2_2),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f63])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    $false | (spl2_1 | ~spl2_2)),
% 0.22/0.59    inference(resolution,[],[f32,f62])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | (spl2_1 | ~spl2_2)),
% 0.22/0.59    inference(forward_demodulation,[],[f54,f57])).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    k1_xboole_0 = sK1 | ~spl2_2),
% 0.22/0.59    inference(avatar_component_clause,[],[f56])).
% 0.22/0.59  fof(f54,plain,(
% 0.22/0.59    ~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | spl2_1),
% 0.22/0.59    inference(avatar_component_clause,[],[f52])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    spl2_1 | spl2_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f48,f56,f52])).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.59    inference(definition_unfolding,[],[f30,f33])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.59    inference(cnf_transformation,[],[f28])).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    ~spl2_1 | ~spl2_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f47,f56,f52])).
% 0.22/0.59  fof(f47,plain,(
% 0.22/0.59    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.59    inference(definition_unfolding,[],[f31,f33])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.59    inference(cnf_transformation,[],[f28])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (27120)------------------------------
% 0.22/0.59  % (27120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (27120)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (27120)Memory used [KB]: 10746
% 0.22/0.59  % (27120)Time elapsed: 0.165 s
% 0.22/0.59  % (27120)------------------------------
% 0.22/0.59  % (27120)------------------------------
% 0.22/0.59  % (27116)Success in time 0.231 s
%------------------------------------------------------------------------------
