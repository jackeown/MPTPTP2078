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
% DateTime   : Thu Dec  3 13:20:10 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 221 expanded)
%              Number of equality atoms :   32 (  32 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(subsumption_resolution,[],[f94,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f94,plain,(
    ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f80,f89])).

fof(f89,plain,(
    k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    inference(resolution,[],[f87,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f87,plain,(
    v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f86,f29])).

fof(f29,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f86,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f85,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f75,f37])).

% (26956)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (26954)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (26957)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (26966)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (26953)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (26971)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (26953)Refutation not found, incomplete strategy% (26953)------------------------------
% (26953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26953)Termination reason: Refutation not found, incomplete strategy

% (26953)Memory used [KB]: 6140
% (26953)Time elapsed: 0.168 s
% (26953)------------------------------
% (26953)------------------------------
% (26971)Refutation not found, incomplete strategy% (26971)------------------------------
% (26971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26971)Termination reason: Refutation not found, incomplete strategy

% (26971)Memory used [KB]: 10618
% (26971)Time elapsed: 0.167 s
% (26971)------------------------------
% (26971)------------------------------
% (26958)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (26966)Refutation not found, incomplete strategy% (26966)------------------------------
% (26966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26958)Refutation not found, incomplete strategy% (26958)------------------------------
% (26958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26958)Termination reason: Refutation not found, incomplete strategy

% (26958)Memory used [KB]: 10618
% (26958)Time elapsed: 0.167 s
% (26958)------------------------------
% (26958)------------------------------
% (26966)Termination reason: Refutation not found, incomplete strategy

% (26966)Memory used [KB]: 10618
% (26966)Time elapsed: 0.167 s
% (26966)------------------------------
% (26966)------------------------------
% (26960)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (26961)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (26960)Refutation not found, incomplete strategy% (26960)------------------------------
% (26960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26960)Termination reason: Refutation not found, incomplete strategy

% (26960)Memory used [KB]: 10618
% (26960)Time elapsed: 0.168 s
% (26960)------------------------------
% (26960)------------------------------
fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f75,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(resolution,[],[f71,f27])).

fof(f27,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f62,f28])).

fof(f28,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f34,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f80,plain,(
    ~ r1_tarski(k6_domain_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f67,f74])).

fof(f74,plain,(
    k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f72,f29])).

fof(f72,plain,
    ( v1_xboole_0(sK0)
    | k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f52,f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k2_enumset1(X1,X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : ~ r1_tarski(k2_enumset1(X0,X1,X2,X3),X3) ),
    inference(resolution,[],[f54,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f54,plain,(
    ! [X2,X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X1,X2,X5)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r2_hidden(X5,X4)
      | k2_enumset1(X0,X1,X2,X5) != X4 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X3 != X5
      | r2_hidden(X5,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:36:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.57  % (26959)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (26951)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.58  % (26959)Refutation not found, incomplete strategy% (26959)------------------------------
% 0.21/0.58  % (26959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (26972)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.60/0.58  % (26964)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.60/0.58  % (26955)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.60/0.58  % (26964)Refutation not found, incomplete strategy% (26964)------------------------------
% 1.60/0.58  % (26964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (26959)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (26959)Memory used [KB]: 10618
% 1.60/0.58  % (26959)Time elapsed: 0.135 s
% 1.60/0.58  % (26959)------------------------------
% 1.60/0.58  % (26959)------------------------------
% 1.60/0.58  % (26964)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.59  % (26964)Memory used [KB]: 6268
% 1.60/0.59  % (26964)Time elapsed: 0.090 s
% 1.60/0.59  % (26964)------------------------------
% 1.60/0.59  % (26964)------------------------------
% 1.60/0.59  % (26952)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.60/0.59  % (26955)Refutation found. Thanks to Tanya!
% 1.60/0.59  % SZS status Theorem for theBenchmark
% 1.60/0.59  % SZS output start Proof for theBenchmark
% 1.60/0.59  fof(f98,plain,(
% 1.60/0.59    $false),
% 1.60/0.59    inference(subsumption_resolution,[],[f94,f30])).
% 1.60/0.59  fof(f30,plain,(
% 1.60/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f2])).
% 1.60/0.59  fof(f2,axiom,(
% 1.60/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.60/0.59  fof(f94,plain,(
% 1.60/0.59    ~r1_tarski(k1_xboole_0,sK1)),
% 1.60/0.59    inference(backward_demodulation,[],[f80,f89])).
% 1.60/0.59  fof(f89,plain,(
% 1.60/0.59    k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 1.60/0.59    inference(resolution,[],[f87,f32])).
% 1.60/0.59  fof(f32,plain,(
% 1.60/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.60/0.59    inference(cnf_transformation,[],[f16])).
% 1.60/0.59  fof(f16,plain,(
% 1.60/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.60/0.59    inference(ennf_transformation,[],[f1])).
% 1.60/0.59  fof(f1,axiom,(
% 1.60/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.60/0.59  fof(f87,plain,(
% 1.60/0.59    v1_xboole_0(k6_domain_1(sK0,sK1))),
% 1.60/0.59    inference(subsumption_resolution,[],[f86,f29])).
% 1.60/0.59  fof(f29,plain,(
% 1.60/0.59    ~v1_xboole_0(sK0)),
% 1.60/0.59    inference(cnf_transformation,[],[f15])).
% 1.60/0.59  fof(f15,plain,(
% 1.60/0.59    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.60/0.59    inference(flattening,[],[f14])).
% 1.60/0.59  fof(f14,plain,(
% 1.60/0.59    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.60/0.59    inference(ennf_transformation,[],[f13])).
% 1.60/0.59  fof(f13,negated_conjecture,(
% 1.60/0.59    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.60/0.59    inference(negated_conjecture,[],[f12])).
% 1.60/0.59  fof(f12,conjecture,(
% 1.60/0.59    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 1.60/0.59  fof(f86,plain,(
% 1.60/0.59    v1_xboole_0(k6_domain_1(sK0,sK1)) | v1_xboole_0(sK0)),
% 1.60/0.59    inference(subsumption_resolution,[],[f85,f26])).
% 1.60/0.59  fof(f26,plain,(
% 1.60/0.59    m1_subset_1(sK1,sK0)),
% 1.60/0.59    inference(cnf_transformation,[],[f15])).
% 1.60/0.59  fof(f85,plain,(
% 1.60/0.59    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0)),
% 1.60/0.59    inference(resolution,[],[f75,f37])).
% 1.60/0.59  % (26956)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.60/0.59  % (26954)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.60/0.59  % (26957)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.60/0.59  % (26966)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.81/0.60  % (26953)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.81/0.60  % (26971)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.81/0.60  % (26953)Refutation not found, incomplete strategy% (26953)------------------------------
% 1.81/0.60  % (26953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (26953)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.60  
% 1.81/0.60  % (26953)Memory used [KB]: 6140
% 1.81/0.60  % (26953)Time elapsed: 0.168 s
% 1.81/0.60  % (26953)------------------------------
% 1.81/0.60  % (26953)------------------------------
% 1.81/0.60  % (26971)Refutation not found, incomplete strategy% (26971)------------------------------
% 1.81/0.60  % (26971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (26971)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.60  
% 1.81/0.60  % (26971)Memory used [KB]: 10618
% 1.81/0.60  % (26971)Time elapsed: 0.167 s
% 1.81/0.60  % (26971)------------------------------
% 1.81/0.60  % (26971)------------------------------
% 1.81/0.60  % (26958)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.81/0.60  % (26966)Refutation not found, incomplete strategy% (26966)------------------------------
% 1.81/0.60  % (26966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (26958)Refutation not found, incomplete strategy% (26958)------------------------------
% 1.81/0.60  % (26958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (26958)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.60  
% 1.81/0.60  % (26958)Memory used [KB]: 10618
% 1.81/0.60  % (26958)Time elapsed: 0.167 s
% 1.81/0.60  % (26958)------------------------------
% 1.81/0.60  % (26958)------------------------------
% 1.81/0.60  % (26966)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.60  
% 1.81/0.60  % (26966)Memory used [KB]: 10618
% 1.81/0.60  % (26966)Time elapsed: 0.167 s
% 1.81/0.60  % (26966)------------------------------
% 1.81/0.60  % (26966)------------------------------
% 1.81/0.60  % (26960)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.81/0.60  % (26961)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.81/0.61  % (26960)Refutation not found, incomplete strategy% (26960)------------------------------
% 1.81/0.61  % (26960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (26960)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.61  
% 1.81/0.61  % (26960)Memory used [KB]: 10618
% 1.81/0.61  % (26960)Time elapsed: 0.168 s
% 1.81/0.61  % (26960)------------------------------
% 1.81/0.61  % (26960)------------------------------
% 1.81/0.61  fof(f37,plain,(
% 1.81/0.61    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f23])).
% 1.81/0.61  fof(f23,plain,(
% 1.81/0.61    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.81/0.61    inference(flattening,[],[f22])).
% 1.81/0.61  fof(f22,plain,(
% 1.81/0.61    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f9])).
% 1.81/0.61  fof(f9,axiom,(
% 1.81/0.61    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.81/0.61  fof(f75,plain,(
% 1.81/0.61    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k6_domain_1(sK0,sK1))),
% 1.81/0.61    inference(resolution,[],[f71,f27])).
% 1.81/0.61  fof(f27,plain,(
% 1.81/0.61    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 1.81/0.61    inference(cnf_transformation,[],[f15])).
% 1.81/0.61  fof(f71,plain,(
% 1.81/0.61    ( ! [X0] : (~v1_subset_1(X0,sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 1.81/0.61    inference(resolution,[],[f62,f28])).
% 1.81/0.61  fof(f28,plain,(
% 1.81/0.61    v1_zfmisc_1(sK0)),
% 1.81/0.61    inference(cnf_transformation,[],[f15])).
% 1.81/0.61  fof(f62,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) )),
% 1.81/0.61    inference(subsumption_resolution,[],[f34,f33])).
% 1.81/0.61  fof(f33,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f17])).
% 1.81/0.61  fof(f17,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.81/0.61    inference(ennf_transformation,[],[f7])).
% 1.81/0.61  fof(f7,axiom,(
% 1.81/0.61    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.81/0.61  fof(f34,plain,(
% 1.81/0.61    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f19])).
% 1.81/0.61  fof(f19,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.81/0.61    inference(flattening,[],[f18])).
% 1.81/0.61  fof(f18,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f11])).
% 1.81/0.61  fof(f11,axiom,(
% 1.81/0.61    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 1.81/0.61  fof(f80,plain,(
% 1.81/0.61    ~r1_tarski(k6_domain_1(sK0,sK1),sK1)),
% 1.81/0.61    inference(superposition,[],[f67,f74])).
% 1.81/0.61  fof(f74,plain,(
% 1.81/0.61    k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.81/0.61    inference(subsumption_resolution,[],[f72,f29])).
% 1.81/0.61  fof(f72,plain,(
% 1.81/0.61    v1_xboole_0(sK0) | k6_domain_1(sK0,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.81/0.61    inference(resolution,[],[f52,f26])).
% 1.81/0.61  fof(f52,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k2_enumset1(X1,X1,X1,X1)) )),
% 1.81/0.61    inference(definition_unfolding,[],[f36,f51])).
% 1.81/0.61  fof(f51,plain,(
% 1.81/0.61    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.81/0.61    inference(definition_unfolding,[],[f31,f50])).
% 1.81/0.61  fof(f50,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.81/0.61    inference(definition_unfolding,[],[f35,f39])).
% 1.81/0.61  fof(f39,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f5])).
% 1.81/0.61  fof(f5,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.81/0.61  fof(f35,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f4])).
% 1.81/0.61  fof(f4,axiom,(
% 1.81/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.81/0.61  fof(f31,plain,(
% 1.81/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f3])).
% 1.81/0.61  fof(f3,axiom,(
% 1.81/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.81/0.61  fof(f36,plain,(
% 1.81/0.61    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f21])).
% 1.81/0.61  fof(f21,plain,(
% 1.81/0.61    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.81/0.61    inference(flattening,[],[f20])).
% 1.81/0.61  fof(f20,plain,(
% 1.81/0.61    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f10])).
% 1.81/0.61  fof(f10,axiom,(
% 1.81/0.61    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.81/0.61  fof(f67,plain,(
% 1.81/0.61    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_enumset1(X0,X1,X2,X3),X3)) )),
% 1.81/0.61    inference(resolution,[],[f54,f38])).
% 1.81/0.61  fof(f38,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f24])).
% 1.81/0.61  fof(f24,plain,(
% 1.81/0.61    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f8])).
% 1.81/0.61  fof(f8,axiom,(
% 1.81/0.61    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.81/0.61  fof(f54,plain,(
% 1.81/0.61    ( ! [X2,X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X1,X2,X5))) )),
% 1.81/0.61    inference(equality_resolution,[],[f53])).
% 1.81/0.61  fof(f53,plain,(
% 1.81/0.61    ( ! [X4,X2,X0,X5,X1] : (r2_hidden(X5,X4) | k2_enumset1(X0,X1,X2,X5) != X4) )),
% 1.81/0.61    inference(equality_resolution,[],[f49])).
% 1.81/0.61  fof(f49,plain,(
% 1.81/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (X3 != X5 | r2_hidden(X5,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 1.81/0.61    inference(cnf_transformation,[],[f25])).
% 1.81/0.61  fof(f25,plain,(
% 1.81/0.61    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 1.81/0.61    inference(ennf_transformation,[],[f6])).
% 1.81/0.61  fof(f6,axiom,(
% 1.81/0.61    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
% 1.81/0.61  % SZS output end Proof for theBenchmark
% 1.81/0.61  % (26955)------------------------------
% 1.81/0.61  % (26955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (26955)Termination reason: Refutation
% 1.81/0.61  
% 1.81/0.61  % (26955)Memory used [KB]: 6268
% 1.81/0.61  % (26955)Time elapsed: 0.150 s
% 1.81/0.61  % (26955)------------------------------
% 1.81/0.61  % (26955)------------------------------
% 1.81/0.61  % (26948)Success in time 0.238 s
%------------------------------------------------------------------------------
