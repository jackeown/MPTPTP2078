%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:30 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 293 expanded)
%              Number of leaves         :   14 (  84 expanded)
%              Depth                    :   22
%              Number of atoms          :  125 ( 521 expanded)
%              Number of equality atoms :   59 ( 232 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f467,plain,(
    $false ),
    inference(subsumption_resolution,[],[f466,f140])).

fof(f140,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f139,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f139,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f46,f60])).

fof(f60,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f48,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f466,plain,(
    ~ r1_tarski(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f463,f442])).

fof(f442,plain,(
    k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f441])).

fof(f441,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f435,f42])).

fof(f435,plain,
    ( sK1 = k5_xboole_0(sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f221,f384])).

fof(f384,plain,
    ( sK0 = k5_xboole_0(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f382,f136])).

fof(f136,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f46,f102])).

fof(f102,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f88,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f88,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f71,f32])).

fof(f71,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f67,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f67,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f22,f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f382,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(k5_xboole_0(sK0,sK1),sK0)
    | sK0 = k5_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f164,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f164,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f163,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f163,plain,
    ( r1_tarski(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f162,f42])).

fof(f162,plain,
    ( r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f157,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f157,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f53,f109])).

fof(f109,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f63,f107])).

fof(f107,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f92,f102])).

fof(f92,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f63,plain,
    ( sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

% (31329)Refutation not found, incomplete strategy% (31329)------------------------------
% (31329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31329)Termination reason: Refutation not found, incomplete strategy

% (31329)Memory used [KB]: 10746
% (31329)Time elapsed: 0.151 s
% (31329)------------------------------
% (31329)------------------------------
fof(f20,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f46,f43])).

fof(f221,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(backward_demodulation,[],[f79,f219])).

fof(f219,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f211,f41])).

fof(f211,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f79,f42])).

fof(f79,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f23,f42])).

fof(f463,plain,(
    ~ r1_tarski(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f450])).

fof(f450,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f111,f442])).

fof(f111,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f44,f107])).

fof(f44,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f21,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:24:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.23/0.53  % (31306)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.53  % (31308)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.53  % (31318)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.53  % (31314)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.53  % (31327)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.53  % (31304)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.53  % (31321)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.53  % (31311)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.53  % (31311)Refutation not found, incomplete strategy% (31311)------------------------------
% 0.23/0.53  % (31311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (31311)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (31311)Memory used [KB]: 10746
% 0.23/0.53  % (31311)Time elapsed: 0.112 s
% 0.23/0.53  % (31311)------------------------------
% 0.23/0.53  % (31311)------------------------------
% 0.23/0.53  % (31305)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.54  % (31317)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.54  % (31317)Refutation not found, incomplete strategy% (31317)------------------------------
% 0.23/0.54  % (31317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (31317)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (31317)Memory used [KB]: 10618
% 0.23/0.54  % (31317)Time elapsed: 0.112 s
% 0.23/0.54  % (31317)------------------------------
% 0.23/0.54  % (31317)------------------------------
% 0.23/0.54  % (31302)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.54  % (31319)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.54  % (31330)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.54  % (31322)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.54  % (31319)Refutation not found, incomplete strategy% (31319)------------------------------
% 0.23/0.54  % (31319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (31319)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (31319)Memory used [KB]: 1663
% 0.23/0.54  % (31319)Time elapsed: 0.097 s
% 0.23/0.54  % (31319)------------------------------
% 0.23/0.54  % (31319)------------------------------
% 0.23/0.54  % (31330)Refutation not found, incomplete strategy% (31330)------------------------------
% 0.23/0.54  % (31330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (31330)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (31330)Memory used [KB]: 1663
% 0.23/0.54  % (31330)Time elapsed: 0.001 s
% 0.23/0.54  % (31330)------------------------------
% 0.23/0.54  % (31330)------------------------------
% 0.23/0.54  % (31313)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.54  % (31326)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.23/0.54  % (31309)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.54  % (31329)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.54  % (31324)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.54  % (31310)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.54  % (31307)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.54  % (31325)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.55  % (31312)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.55  % (31328)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.55  % (31328)Refutation not found, incomplete strategy% (31328)------------------------------
% 0.23/0.55  % (31328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (31328)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (31328)Memory used [KB]: 6268
% 0.23/0.55  % (31328)Time elapsed: 0.129 s
% 0.23/0.55  % (31328)------------------------------
% 0.23/0.55  % (31328)------------------------------
% 0.23/0.55  % (31320)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.55  % (31316)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.55  % (31301)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.55  % (31313)Refutation not found, incomplete strategy% (31313)------------------------------
% 0.23/0.55  % (31313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (31325)Refutation not found, incomplete strategy% (31325)------------------------------
% 0.23/0.55  % (31325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (31325)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (31325)Memory used [KB]: 10746
% 0.23/0.55  % (31325)Time elapsed: 0.123 s
% 0.23/0.55  % (31325)------------------------------
% 0.23/0.55  % (31325)------------------------------
% 0.23/0.55  % (31303)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.55  % (31313)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (31313)Memory used [KB]: 10618
% 0.23/0.55  % (31315)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.55  % (31313)Time elapsed: 0.130 s
% 0.23/0.55  % (31313)------------------------------
% 0.23/0.55  % (31313)------------------------------
% 0.23/0.55  % (31323)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.56  % (31320)Refutation found. Thanks to Tanya!
% 0.23/0.56  % SZS status Theorem for theBenchmark
% 0.23/0.56  % SZS output start Proof for theBenchmark
% 0.23/0.56  fof(f467,plain,(
% 0.23/0.56    $false),
% 0.23/0.56    inference(subsumption_resolution,[],[f466,f140])).
% 0.23/0.56  fof(f140,plain,(
% 0.23/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.56    inference(forward_demodulation,[],[f139,f42])).
% 0.23/0.56  fof(f42,plain,(
% 0.23/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f8])).
% 0.23/0.56  fof(f8,axiom,(
% 0.23/0.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.23/0.56  fof(f139,plain,(
% 0.23/0.56    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,X0),X0)) )),
% 0.23/0.56    inference(superposition,[],[f46,f60])).
% 0.23/0.56  fof(f60,plain,(
% 0.23/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.23/0.56    inference(unit_resulting_resolution,[],[f48,f32])).
% 0.23/0.56  fof(f32,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.23/0.56    inference(cnf_transformation,[],[f17])).
% 0.23/0.56  fof(f17,plain,(
% 0.23/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.23/0.56    inference(ennf_transformation,[],[f4])).
% 0.23/0.56  fof(f4,axiom,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.23/0.56  fof(f48,plain,(
% 0.23/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.56    inference(equality_resolution,[],[f25])).
% 0.23/0.56  fof(f25,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.56    inference(cnf_transformation,[],[f2])).
% 0.23/0.56  fof(f2,axiom,(
% 0.23/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.56  fof(f46,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f33,f40])).
% 0.23/0.56  fof(f40,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f3])).
% 0.23/0.56  fof(f3,axiom,(
% 0.23/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.56  fof(f33,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f5])).
% 0.23/0.56  fof(f5,axiom,(
% 0.23/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.23/0.56  fof(f466,plain,(
% 0.23/0.56    ~r1_tarski(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0))),
% 0.23/0.56    inference(forward_demodulation,[],[f463,f442])).
% 0.23/0.56  fof(f442,plain,(
% 0.23/0.56    k1_xboole_0 = sK1),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f441])).
% 0.23/0.56  fof(f441,plain,(
% 0.23/0.56    k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.23/0.56    inference(forward_demodulation,[],[f435,f42])).
% 0.23/0.56  fof(f435,plain,(
% 0.23/0.56    sK1 = k5_xboole_0(sK0,sK0) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(superposition,[],[f221,f384])).
% 0.23/0.56  fof(f384,plain,(
% 0.23/0.56    sK0 = k5_xboole_0(sK0,sK1) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(subsumption_resolution,[],[f382,f136])).
% 0.23/0.56  fof(f136,plain,(
% 0.23/0.56    r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 0.23/0.56    inference(superposition,[],[f46,f102])).
% 0.23/0.56  fof(f102,plain,(
% 0.23/0.56    sK1 = k3_xboole_0(sK0,sK1)),
% 0.23/0.56    inference(superposition,[],[f88,f43])).
% 0.23/0.56  fof(f43,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f1])).
% 0.23/0.56  fof(f1,axiom,(
% 0.23/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.56  fof(f88,plain,(
% 0.23/0.56    sK1 = k3_xboole_0(sK1,sK0)),
% 0.23/0.56    inference(unit_resulting_resolution,[],[f71,f32])).
% 0.23/0.56  fof(f71,plain,(
% 0.23/0.56    r1_tarski(sK1,sK0)),
% 0.23/0.56    inference(unit_resulting_resolution,[],[f67,f50])).
% 0.23/0.56  fof(f50,plain,(
% 0.23/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.23/0.56    inference(equality_resolution,[],[f29])).
% 0.23/0.56  fof(f29,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.23/0.56    inference(cnf_transformation,[],[f9])).
% 0.23/0.56  fof(f9,axiom,(
% 0.23/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.23/0.56  fof(f67,plain,(
% 0.23/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.56    inference(unit_resulting_resolution,[],[f22,f39,f38])).
% 0.23/0.56  fof(f38,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f19])).
% 0.23/0.56  fof(f19,plain,(
% 0.23/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f10])).
% 0.23/0.56  fof(f10,axiom,(
% 0.23/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.23/0.56  fof(f39,plain,(
% 0.23/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f13])).
% 0.23/0.56  fof(f13,axiom,(
% 0.23/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.23/0.56  fof(f22,plain,(
% 0.23/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.56    inference(cnf_transformation,[],[f16])).
% 0.23/0.56  fof(f16,plain,(
% 0.23/0.56    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f15])).
% 0.23/0.56  fof(f15,negated_conjecture,(
% 0.23/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.23/0.56    inference(negated_conjecture,[],[f14])).
% 0.23/0.56  fof(f14,conjecture,(
% 0.23/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.23/0.56  fof(f382,plain,(
% 0.23/0.56    k1_xboole_0 = sK1 | ~r1_tarski(k5_xboole_0(sK0,sK1),sK0) | sK0 = k5_xboole_0(sK0,sK1)),
% 0.23/0.56    inference(resolution,[],[f164,f26])).
% 0.23/0.56  fof(f26,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.23/0.56    inference(cnf_transformation,[],[f2])).
% 0.23/0.56  fof(f164,plain,(
% 0.23/0.56    r1_tarski(sK0,k5_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(forward_demodulation,[],[f163,f41])).
% 0.23/0.56  fof(f41,plain,(
% 0.23/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.56    inference(cnf_transformation,[],[f6])).
% 0.23/0.56  fof(f6,axiom,(
% 0.23/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.23/0.56  fof(f163,plain,(
% 0.23/0.56    r1_tarski(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(forward_demodulation,[],[f162,f42])).
% 0.23/0.56  fof(f162,plain,(
% 0.23/0.56    r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(forward_demodulation,[],[f157,f23])).
% 0.23/0.56  fof(f23,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f7])).
% 0.23/0.56  fof(f7,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.23/0.56  fof(f157,plain,(
% 0.23/0.56    r1_tarski(k5_xboole_0(k5_xboole_0(sK0,sK1),sK1),k5_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(superposition,[],[f53,f109])).
% 0.23/0.56  fof(f109,plain,(
% 0.23/0.56    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(backward_demodulation,[],[f63,f107])).
% 0.23/0.56  fof(f107,plain,(
% 0.23/0.56    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.23/0.56    inference(backward_demodulation,[],[f92,f102])).
% 0.23/0.56  fof(f92,plain,(
% 0.23/0.56    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.23/0.56    inference(unit_resulting_resolution,[],[f22,f47])).
% 0.23/0.56  fof(f47,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f34,f40])).
% 0.23/0.56  fof(f34,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f18])).
% 0.23/0.56  fof(f18,plain,(
% 0.23/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f12])).
% 0.23/0.56  fof(f12,axiom,(
% 0.23/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.23/0.56  fof(f63,plain,(
% 0.23/0.56    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(resolution,[],[f32,f45])).
% 0.23/0.56  fof(f45,plain,(
% 0.23/0.56    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.23/0.56    inference(definition_unfolding,[],[f20,f27])).
% 0.23/0.56  fof(f27,plain,(
% 0.23/0.56    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f11])).
% 0.23/0.56  fof(f11,axiom,(
% 0.23/0.56    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.23/0.56  % (31329)Refutation not found, incomplete strategy% (31329)------------------------------
% 0.23/0.56  % (31329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (31329)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (31329)Memory used [KB]: 10746
% 0.23/0.56  % (31329)Time elapsed: 0.151 s
% 0.23/0.56  % (31329)------------------------------
% 0.23/0.56  % (31329)------------------------------
% 0.23/0.57  fof(f20,plain,(
% 0.23/0.57    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.23/0.57    inference(cnf_transformation,[],[f16])).
% 0.23/0.57  fof(f53,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0)) )),
% 0.23/0.57    inference(superposition,[],[f46,f43])).
% 0.23/0.57  fof(f221,plain,(
% 0.23/0.57    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 0.23/0.57    inference(backward_demodulation,[],[f79,f219])).
% 0.23/0.57  fof(f219,plain,(
% 0.23/0.57    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.23/0.57    inference(forward_demodulation,[],[f211,f41])).
% 0.23/0.57  fof(f211,plain,(
% 0.23/0.57    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0)) )),
% 0.23/0.57    inference(superposition,[],[f79,f42])).
% 0.23/0.57  fof(f79,plain,(
% 0.23/0.57    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 0.23/0.57    inference(superposition,[],[f23,f42])).
% 0.23/0.57  fof(f463,plain,(
% 0.23/0.57    ~r1_tarski(sK1,k5_xboole_0(sK0,sK1))),
% 0.23/0.57    inference(trivial_inequality_removal,[],[f450])).
% 0.23/0.57  fof(f450,plain,(
% 0.23/0.57    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK1,k5_xboole_0(sK0,sK1))),
% 0.23/0.57    inference(backward_demodulation,[],[f111,f442])).
% 0.23/0.57  fof(f111,plain,(
% 0.23/0.57    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k5_xboole_0(sK0,sK1))),
% 0.23/0.57    inference(backward_demodulation,[],[f44,f107])).
% 0.23/0.57  fof(f44,plain,(
% 0.23/0.57    ~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 != sK1),
% 0.23/0.57    inference(definition_unfolding,[],[f21,f27])).
% 0.23/0.57  fof(f21,plain,(
% 0.23/0.57    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.23/0.57    inference(cnf_transformation,[],[f16])).
% 0.23/0.57  % SZS output end Proof for theBenchmark
% 0.23/0.57  % (31320)------------------------------
% 0.23/0.57  % (31320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (31320)Termination reason: Refutation
% 0.23/0.57  
% 0.23/0.57  % (31320)Memory used [KB]: 1918
% 0.23/0.57  % (31320)Time elapsed: 0.138 s
% 0.23/0.57  % (31320)------------------------------
% 0.23/0.57  % (31320)------------------------------
% 0.23/0.57  % (31300)Success in time 0.209 s
%------------------------------------------------------------------------------
