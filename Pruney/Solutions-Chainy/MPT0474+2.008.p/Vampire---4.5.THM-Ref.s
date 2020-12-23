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
% DateTime   : Thu Dec  3 12:48:12 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 114 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 243 expanded)
%              Number of equality atoms :   46 ( 113 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f184,f184,f219,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
      | sP0(X0,X1)
      | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) ) ),
    inference(cnf_transformation,[],[f36])).

% (23554)Refutation not found, incomplete strategy% (23554)------------------------------
% (23554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23554)Termination reason: Refutation not found, incomplete strategy

% (23554)Memory used [KB]: 10618
% (23554)Time elapsed: 0.126 s
% (23554)------------------------------
% (23554)------------------------------
fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ r2_hidden(k4_tarski(X5,X4),X0) )
            & ( r2_hidden(k4_tarski(X5,X4),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ r2_hidden(k4_tarski(X5,X4),X0) )
            & ( r2_hidden(k4_tarski(X5,X4),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

% (23550)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (23568)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (23551)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (23565)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (23547)Termination reason: Refutation not found, incomplete strategy

% (23547)Memory used [KB]: 10618
% (23547)Time elapsed: 0.127 s
% (23547)------------------------------
% (23547)------------------------------
% (23557)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (23565)Refutation not found, incomplete strategy% (23565)------------------------------
% (23565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

% (23565)Termination reason: Refutation not found, incomplete strategy
fof(f23,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
        <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f219,plain,(
    ~ sP0(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f218,f189])).

fof(f189,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f184,f63])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK7(X0)
        & r2_hidden(sK7(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK7(X0)
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

% (23565)Memory used [KB]: 10746
fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f218,plain,
    ( ~ sP0(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,
    ( ~ sP0(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f215,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f18,f24,f23])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( k4_relat_1(X0) = X1
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(f215,plain,
    ( ~ sP1(k1_xboole_0,k1_xboole_0)
    | ~ sP0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | ~ sP0(k1_xboole_0,X0)
      | ~ sP1(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f52,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_relat_1(X1) = X0
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k4_relat_1(X1) = X0
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k4_relat_1(X1) != X0 ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ( ( k4_relat_1(X0) = X1
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | k4_relat_1(X0) != X1 ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f52,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f15])).

fof(f15,negated_conjecture,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

fof(f184,plain,(
    ! [X6] : ~ r2_hidden(X6,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f175,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f175,plain,(
    ! [X6] :
      ( k1_xboole_0 = k2_xboole_0(k2_tarski(X6,X6),k2_tarski(X6,X6))
      | ~ r2_hidden(X6,k1_xboole_0) ) ),
    inference(superposition,[],[f93,f129])).

fof(f129,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f88,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f66,f67,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f93,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)) = k4_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X2,X2),X1))
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) = k4_xboole_0(k2_tarski(X0,X2),k4_xboole_0(k2_tarski(X0,X2),X1))
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f87,f67])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f54,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f54,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:19:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (23560)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (23546)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (23569)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (23547)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (23548)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (23553)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (23574)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (23561)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (23552)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (23553)Refutation not found, incomplete strategy% (23553)------------------------------
% 0.21/0.52  % (23553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23553)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23553)Memory used [KB]: 10618
% 0.21/0.52  % (23553)Time elapsed: 0.099 s
% 0.21/0.52  % (23553)------------------------------
% 0.21/0.52  % (23553)------------------------------
% 0.21/0.52  % (23555)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (23564)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (23555)Refutation not found, incomplete strategy% (23555)------------------------------
% 0.21/0.52  % (23555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23555)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23555)Memory used [KB]: 10618
% 0.21/0.52  % (23555)Time elapsed: 0.106 s
% 0.21/0.52  % (23555)------------------------------
% 0.21/0.52  % (23555)------------------------------
% 0.21/0.52  % (23549)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (23567)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (23570)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (23567)Refutation not found, incomplete strategy% (23567)------------------------------
% 0.21/0.52  % (23567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23567)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23567)Memory used [KB]: 10746
% 0.21/0.52  % (23567)Time elapsed: 0.069 s
% 0.21/0.52  % (23567)------------------------------
% 0.21/0.52  % (23567)------------------------------
% 0.21/0.52  % (23559)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (23556)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (23549)Refutation not found, incomplete strategy% (23549)------------------------------
% 0.21/0.52  % (23549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23549)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23549)Memory used [KB]: 6140
% 0.21/0.52  % (23549)Time elapsed: 0.116 s
% 0.21/0.52  % (23549)------------------------------
% 0.21/0.52  % (23549)------------------------------
% 0.21/0.53  % (23545)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (23558)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (23572)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.53  % (23547)Refutation not found, incomplete strategy% (23547)------------------------------
% 1.39/0.53  % (23547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.53  % (23554)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.53  % (23563)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.53  % (23562)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.53  % (23573)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.53  % (23574)Refutation found. Thanks to Tanya!
% 1.39/0.53  % SZS status Theorem for theBenchmark
% 1.39/0.53  % SZS output start Proof for theBenchmark
% 1.39/0.53  fof(f221,plain,(
% 1.39/0.53    $false),
% 1.39/0.53    inference(unit_resulting_resolution,[],[f184,f184,f219,f59])).
% 1.39/0.53  fof(f59,plain,(
% 1.39/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | sP0(X0,X1) | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f36])).
% 1.39/0.53  % (23554)Refutation not found, incomplete strategy% (23554)------------------------------
% 1.39/0.53  % (23554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.53  % (23554)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.53  
% 1.39/0.53  % (23554)Memory used [KB]: 10618
% 1.39/0.53  % (23554)Time elapsed: 0.126 s
% 1.39/0.53  % (23554)------------------------------
% 1.39/0.53  % (23554)------------------------------
% 1.39/0.53  fof(f36,plain,(
% 1.39/0.53    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP0(X0,X1)))),
% 1.39/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f34,f35])).
% 1.39/0.53  fof(f35,plain,(
% 1.39/0.53    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1))))),
% 1.39/0.53    introduced(choice_axiom,[])).
% 1.39/0.53  fof(f34,plain,(
% 1.39/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP0(X0,X1)))),
% 1.39/0.53    inference(rectify,[],[f33])).
% 1.39/0.54  % (23550)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.39/0.54  % (23568)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.54  % (23551)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.39/0.54  % (23565)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.54  % (23547)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (23547)Memory used [KB]: 10618
% 1.39/0.54  % (23547)Time elapsed: 0.127 s
% 1.39/0.54  % (23547)------------------------------
% 1.39/0.54  % (23547)------------------------------
% 1.39/0.54  % (23557)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.54  % (23565)Refutation not found, incomplete strategy% (23565)------------------------------
% 1.39/0.54  % (23565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  fof(f33,plain,(
% 1.39/0.55    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~sP0(X0,X1)))),
% 1.39/0.55    inference(nnf_transformation,[],[f23])).
% 1.39/0.55  % (23565)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  fof(f23,plain,(
% 1.39/0.55    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.39/0.55  
% 1.39/0.55  fof(f219,plain,(
% 1.39/0.55    ~sP0(k1_xboole_0,k1_xboole_0)),
% 1.39/0.55    inference(subsumption_resolution,[],[f218,f189])).
% 1.39/0.55  fof(f189,plain,(
% 1.39/0.55    v1_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(resolution,[],[f184,f63])).
% 1.39/0.55  fof(f63,plain,(
% 1.39/0.55    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f38])).
% 1.39/0.55  fof(f38,plain,(
% 1.39/0.55    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK7(X0) & r2_hidden(sK7(X0),X0)))),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f37])).
% 1.39/0.55  fof(f37,plain,(
% 1.39/0.55    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK7(X0) & r2_hidden(sK7(X0),X0)))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  % (23565)Memory used [KB]: 10746
% 1.39/0.55  fof(f20,plain,(
% 1.39/0.55    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f17])).
% 1.39/0.55  fof(f17,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.39/0.55    inference(unused_predicate_definition_removal,[],[f12])).
% 1.39/0.55  fof(f12,axiom,(
% 1.39/0.55    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.39/0.55  fof(f218,plain,(
% 1.39/0.55    ~sP0(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(duplicate_literal_removal,[],[f217])).
% 1.39/0.55  fof(f217,plain,(
% 1.39/0.55    ~sP0(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(resolution,[],[f215,f61])).
% 1.39/0.55  fof(f61,plain,(
% 1.39/0.55    ( ! [X0,X1] : (sP1(X1,X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f25])).
% 1.39/0.55  fof(f25,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (sP1(X1,X0) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(definition_folding,[],[f18,f24,f23])).
% 1.39/0.55  fof(f24,plain,(
% 1.39/0.55    ! [X1,X0] : ((k4_relat_1(X0) = X1 <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.39/0.55  fof(f18,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f13])).
% 1.39/0.55  fof(f13,axiom,(
% 1.39/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).
% 1.39/0.55  fof(f215,plain,(
% 1.39/0.55    ~sP1(k1_xboole_0,k1_xboole_0) | ~sP0(k1_xboole_0,k1_xboole_0)),
% 1.39/0.55    inference(equality_resolution,[],[f111])).
% 1.39/0.55  fof(f111,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 != X0 | ~sP0(k1_xboole_0,X0) | ~sP1(X0,k1_xboole_0)) )),
% 1.39/0.55    inference(superposition,[],[f52,f56])).
% 1.39/0.55  fof(f56,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k4_relat_1(X1) = X0 | ~sP0(X1,X0) | ~sP1(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f32])).
% 1.39/0.55  fof(f32,plain,(
% 1.39/0.55    ! [X0,X1] : (((k4_relat_1(X1) = X0 | ~sP0(X1,X0)) & (sP0(X1,X0) | k4_relat_1(X1) != X0)) | ~sP1(X0,X1))),
% 1.39/0.55    inference(rectify,[],[f31])).
% 1.39/0.55  fof(f31,plain,(
% 1.39/0.55    ! [X1,X0] : (((k4_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k4_relat_1(X0) != X1)) | ~sP1(X1,X0))),
% 1.39/0.55    inference(nnf_transformation,[],[f24])).
% 1.39/0.55  fof(f52,plain,(
% 1.39/0.55    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(cnf_transformation,[],[f16])).
% 1.39/0.55  fof(f16,plain,(
% 1.39/0.55    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(flattening,[],[f15])).
% 1.39/0.55  fof(f15,negated_conjecture,(
% 1.39/0.55    ~k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(negated_conjecture,[],[f14])).
% 1.39/0.55  fof(f14,conjecture,(
% 1.39/0.55    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).
% 1.39/0.55  fof(f184,plain,(
% 1.39/0.55    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f175,f74])).
% 1.39/0.55  fof(f74,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f10])).
% 1.39/0.55  fof(f10,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.39/0.55  fof(f175,plain,(
% 1.39/0.55    ( ! [X6] : (k1_xboole_0 = k2_xboole_0(k2_tarski(X6,X6),k2_tarski(X6,X6)) | ~r2_hidden(X6,k1_xboole_0)) )),
% 1.39/0.55    inference(superposition,[],[f93,f129])).
% 1.39/0.55  fof(f129,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.39/0.55    inference(superposition,[],[f88,f53])).
% 1.39/0.55  fof(f53,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f6])).
% 1.39/0.55  fof(f6,axiom,(
% 1.39/0.55    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.39/0.55  fof(f88,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.39/0.55    inference(definition_unfolding,[],[f66,f67,f67])).
% 1.39/0.55  fof(f67,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f5])).
% 1.39/0.55  fof(f5,axiom,(
% 1.39/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.39/0.55  fof(f66,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f1])).
% 1.39/0.55  fof(f1,axiom,(
% 1.39/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.39/0.55  fof(f93,plain,(
% 1.39/0.55    ( ! [X2,X1] : (k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)) = k4_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X2,X2),X1)) | ~r2_hidden(X2,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f89])).
% 1.39/0.55  fof(f89,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) = k4_xboole_0(k2_tarski(X0,X2),k4_xboole_0(k2_tarski(X0,X2),X1)) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 1.39/0.55    inference(definition_unfolding,[],[f76,f87,f67])).
% 1.39/0.55  fof(f87,plain,(
% 1.39/0.55    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))) )),
% 1.39/0.55    inference(definition_unfolding,[],[f54,f86])).
% 1.39/0.55  fof(f86,plain,(
% 1.39/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,axiom,(
% 1.39/0.55    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 1.39/0.55  fof(f54,plain,(
% 1.39/0.55    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f8])).
% 1.39/0.55  fof(f8,axiom,(
% 1.39/0.55    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 1.39/0.55  fof(f76,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f22])).
% 1.39/0.55  fof(f22,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 1.39/0.55    inference(flattening,[],[f21])).
% 1.39/0.55  fof(f21,plain,(
% 1.39/0.55    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 1.39/0.55    inference(ennf_transformation,[],[f11])).
% 1.39/0.55  fof(f11,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (23574)------------------------------
% 1.39/0.55  % (23574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (23574)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (23574)Memory used [KB]: 1791
% 1.39/0.55  % (23574)Time elapsed: 0.128 s
% 1.39/0.55  % (23574)------------------------------
% 1.39/0.55  % (23574)------------------------------
% 1.39/0.55  % (23565)Time elapsed: 0.140 s
% 1.39/0.55  % (23565)------------------------------
% 1.39/0.55  % (23565)------------------------------
% 1.39/0.55  % (23544)Success in time 0.188 s
%------------------------------------------------------------------------------
