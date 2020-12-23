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
% DateTime   : Thu Dec  3 12:50:19 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 121 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   19
%              Number of atoms          :  116 ( 188 expanded)
%              Number of equality atoms :   43 (  87 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f272,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f101,f270])).

fof(f270,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f269])).

% (10892)Refutation not found, incomplete strategy% (10892)------------------------------
% (10892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f269,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f265])).

% (10892)Termination reason: Refutation not found, incomplete strategy

% (10892)Memory used [KB]: 10618
% (10892)Time elapsed: 0.148 s
% (10892)------------------------------
% (10892)------------------------------
fof(f265,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(superposition,[],[f55,f254])).

fof(f254,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(resolution,[],[f251,f95])).

fof(f95,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f49,f24])).

fof(f24,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f251,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2(k1_xboole_0,k10_relat_1(k1_xboole_0,X0)),X0,k1_xboole_0),k1_xboole_0)
        | k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f249,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl6_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f249,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2(k1_xboole_0,k10_relat_1(k1_xboole_0,X0)),X0,k1_xboole_0),k2_relat_1(k1_xboole_0))
        | k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(resolution,[],[f147,f74])).

fof(f74,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f147,plain,
    ( ! [X4,X3] :
        ( ~ v1_relat_1(X3)
        | r2_hidden(sK5(sK2(k1_xboole_0,k10_relat_1(X3,X4)),X4,X3),k2_relat_1(X3))
        | k1_xboole_0 = k10_relat_1(X3,X4) )
    | ~ spl6_2 ),
    inference(resolution,[],[f139,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f139,plain,
    ( ! [X15] :
        ( r2_hidden(sK2(k1_xboole_0,X15),X15)
        | k1_xboole_0 = X15 )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f136,f60])).

fof(f136,plain,(
    ! [X15] :
      ( r2_hidden(sK2(k1_xboole_0,X15),X15)
      | k2_relat_1(k1_xboole_0) = X15 ) ),
    inference(resolution,[],[f31,f95])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f55,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl6_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f101,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f97,f72])).

fof(f97,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f95,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f61,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f56,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n009.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 10:45:41 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.53  % (10894)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.53  % (10889)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.53  % (10897)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.53  % (10897)Refutation not found, incomplete strategy% (10897)------------------------------
% 0.23/0.53  % (10897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (10905)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.53  % (10897)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (10897)Memory used [KB]: 6140
% 0.23/0.53  % (10897)Time elapsed: 0.004 s
% 0.23/0.53  % (10897)------------------------------
% 0.23/0.53  % (10897)------------------------------
% 0.23/0.53  % (10902)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.53  % (10905)Refutation not found, incomplete strategy% (10905)------------------------------
% 0.23/0.53  % (10905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (10905)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (10905)Memory used [KB]: 1663
% 0.23/0.54  % (10905)Time elapsed: 0.109 s
% 0.23/0.54  % (10905)------------------------------
% 0.23/0.54  % (10905)------------------------------
% 0.23/0.54  % (10896)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.54  % (10886)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.54  % (10886)Refutation not found, incomplete strategy% (10886)------------------------------
% 0.23/0.54  % (10886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (10886)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (10886)Memory used [KB]: 6140
% 0.23/0.54  % (10886)Time elapsed: 0.117 s
% 0.23/0.54  % (10886)------------------------------
% 0.23/0.54  % (10886)------------------------------
% 0.23/0.54  % (10910)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.54  % (10904)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.54  % (10898)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.54  % (10887)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.55  % (10899)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.55  % (10904)Refutation not found, incomplete strategy% (10904)------------------------------
% 0.23/0.55  % (10904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (10904)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (10904)Memory used [KB]: 10618
% 0.23/0.55  % (10904)Time elapsed: 0.085 s
% 0.23/0.55  % (10904)------------------------------
% 0.23/0.55  % (10904)------------------------------
% 0.23/0.55  % (10902)Refutation not found, incomplete strategy% (10902)------------------------------
% 0.23/0.55  % (10902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (10884)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.55  % (10902)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (10902)Memory used [KB]: 10746
% 0.23/0.55  % (10902)Time elapsed: 0.115 s
% 0.23/0.55  % (10902)------------------------------
% 0.23/0.55  % (10902)------------------------------
% 0.23/0.55  % (10883)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.55  % (10882)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.55  % (10882)Refutation not found, incomplete strategy% (10882)------------------------------
% 0.23/0.55  % (10882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (10882)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (10882)Memory used [KB]: 1663
% 0.23/0.55  % (10882)Time elapsed: 0.093 s
% 0.23/0.55  % (10882)------------------------------
% 0.23/0.55  % (10882)------------------------------
% 0.23/0.55  % (10884)Refutation not found, incomplete strategy% (10884)------------------------------
% 0.23/0.55  % (10884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (10884)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (10884)Memory used [KB]: 10618
% 0.23/0.55  % (10884)Time elapsed: 0.124 s
% 0.23/0.55  % (10884)------------------------------
% 0.23/0.55  % (10884)------------------------------
% 0.23/0.55  % (10893)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.55  % (10893)Refutation not found, incomplete strategy% (10893)------------------------------
% 0.23/0.55  % (10893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (10893)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (10893)Memory used [KB]: 10618
% 0.23/0.55  % (10893)Time elapsed: 0.134 s
% 0.23/0.55  % (10893)------------------------------
% 0.23/0.55  % (10893)------------------------------
% 0.23/0.55  % (10885)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.55  % (10888)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.56  % (10911)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.56  % (10909)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.56  % (10891)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.56  % (10903)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.56  % (10900)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.56  % (10903)Refutation not found, incomplete strategy% (10903)------------------------------
% 0.23/0.56  % (10903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (10903)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (10903)Memory used [KB]: 1663
% 0.23/0.56  % (10903)Time elapsed: 0.139 s
% 0.23/0.56  % (10903)------------------------------
% 0.23/0.56  % (10903)------------------------------
% 0.23/0.56  % (10891)Refutation not found, incomplete strategy% (10891)------------------------------
% 0.23/0.56  % (10891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (10891)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (10891)Memory used [KB]: 10618
% 0.23/0.56  % (10891)Time elapsed: 0.138 s
% 0.23/0.56  % (10891)------------------------------
% 0.23/0.56  % (10891)------------------------------
% 0.23/0.56  % (10899)Refutation not found, incomplete strategy% (10899)------------------------------
% 0.23/0.56  % (10899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (10899)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (10899)Memory used [KB]: 10618
% 0.23/0.56  % (10899)Time elapsed: 0.137 s
% 0.23/0.56  % (10899)------------------------------
% 0.23/0.56  % (10899)------------------------------
% 0.23/0.56  % (10895)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.56  % (10890)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.56  % (10908)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.56  % (10890)Refutation not found, incomplete strategy% (10890)------------------------------
% 0.23/0.56  % (10890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (10890)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (10890)Memory used [KB]: 10618
% 0.23/0.56  % (10890)Time elapsed: 0.137 s
% 0.23/0.56  % (10890)------------------------------
% 0.23/0.56  % (10890)------------------------------
% 0.23/0.56  % (10908)Refutation not found, incomplete strategy% (10908)------------------------------
% 0.23/0.56  % (10908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (10908)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (10908)Memory used [KB]: 10618
% 0.23/0.56  % (10908)Time elapsed: 0.137 s
% 0.23/0.56  % (10908)------------------------------
% 0.23/0.56  % (10908)------------------------------
% 0.23/0.56  % (10901)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.57  % (10892)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.57  % (10907)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.57  % (10907)Refutation not found, incomplete strategy% (10907)------------------------------
% 0.23/0.57  % (10907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (10907)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (10907)Memory used [KB]: 6140
% 0.23/0.57  % (10907)Time elapsed: 0.153 s
% 0.23/0.57  % (10907)------------------------------
% 0.23/0.57  % (10907)------------------------------
% 0.23/0.57  % (10898)Refutation found. Thanks to Tanya!
% 0.23/0.57  % SZS status Theorem for theBenchmark
% 0.23/0.57  % SZS output start Proof for theBenchmark
% 0.23/0.57  fof(f272,plain,(
% 0.23/0.57    $false),
% 0.23/0.57    inference(avatar_sat_refutation,[],[f56,f61,f101,f270])).
% 0.23/0.57  fof(f270,plain,(
% 0.23/0.57    spl6_1 | ~spl6_2 | ~spl6_4),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f269])).
% 0.23/0.57  % (10892)Refutation not found, incomplete strategy% (10892)------------------------------
% 0.23/0.57  % (10892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  fof(f269,plain,(
% 0.23/0.57    $false | (spl6_1 | ~spl6_2 | ~spl6_4)),
% 0.23/0.57    inference(trivial_inequality_removal,[],[f265])).
% 0.23/0.57  % (10892)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (10892)Memory used [KB]: 10618
% 0.23/0.57  % (10892)Time elapsed: 0.148 s
% 0.23/0.57  % (10892)------------------------------
% 0.23/0.57  % (10892)------------------------------
% 0.23/0.57  fof(f265,plain,(
% 0.23/0.57    k1_xboole_0 != k1_xboole_0 | (spl6_1 | ~spl6_2 | ~spl6_4)),
% 0.23/0.57    inference(superposition,[],[f55,f254])).
% 0.23/0.57  fof(f254,plain,(
% 0.23/0.57    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl6_2 | ~spl6_4)),
% 0.23/0.57    inference(resolution,[],[f251,f95])).
% 0.23/0.57  fof(f95,plain,(
% 0.23/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.57    inference(resolution,[],[f49,f24])).
% 0.23/0.57  fof(f24,plain,(
% 0.23/0.57    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f1])).
% 0.23/0.57  fof(f1,axiom,(
% 0.23/0.57    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.23/0.57  fof(f49,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f33,f48])).
% 0.23/0.57  fof(f48,plain,(
% 0.23/0.57    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f25,f47])).
% 0.23/0.57  fof(f47,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f28,f46])).
% 0.23/0.57  fof(f46,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f34,f45])).
% 0.23/0.57  fof(f45,plain,(
% 0.23/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f39,f44])).
% 0.23/0.57  fof(f44,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f40,f43])).
% 0.23/0.57  fof(f43,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f41,f42])).
% 0.23/0.57  fof(f42,plain,(
% 0.23/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f8])).
% 0.23/0.57  fof(f8,axiom,(
% 0.23/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.23/0.57  fof(f41,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f7])).
% 0.23/0.57  fof(f7,axiom,(
% 0.23/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.23/0.57  fof(f40,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f6])).
% 0.23/0.57  fof(f6,axiom,(
% 0.23/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.23/0.57  fof(f39,plain,(
% 0.23/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f5])).
% 0.23/0.57  fof(f5,axiom,(
% 0.23/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.57  fof(f34,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f4])).
% 0.23/0.57  fof(f4,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.57  fof(f28,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f3])).
% 0.23/0.57  fof(f3,axiom,(
% 0.23/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.57  fof(f25,plain,(
% 0.23/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f2])).
% 0.23/0.57  fof(f2,axiom,(
% 0.23/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.57  fof(f33,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f19])).
% 0.23/0.57  fof(f19,plain,(
% 0.23/0.57    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.57    inference(ennf_transformation,[],[f9])).
% 0.23/0.57  fof(f9,axiom,(
% 0.23/0.57    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.23/0.57  fof(f251,plain,(
% 0.23/0.57    ( ! [X0] : (r2_hidden(sK5(sK2(k1_xboole_0,k10_relat_1(k1_xboole_0,X0)),X0,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl6_2 | ~spl6_4)),
% 0.23/0.57    inference(forward_demodulation,[],[f249,f60])).
% 0.23/0.57  fof(f60,plain,(
% 0.23/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_2),
% 0.23/0.57    inference(avatar_component_clause,[],[f58])).
% 0.23/0.57  fof(f58,plain,(
% 0.23/0.57    spl6_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.23/0.57  fof(f249,plain,(
% 0.23/0.57    ( ! [X0] : (r2_hidden(sK5(sK2(k1_xboole_0,k10_relat_1(k1_xboole_0,X0)),X0,k1_xboole_0),k2_relat_1(k1_xboole_0)) | k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl6_2 | ~spl6_4)),
% 0.23/0.57    inference(resolution,[],[f147,f74])).
% 0.23/0.57  fof(f74,plain,(
% 0.23/0.57    v1_relat_1(k1_xboole_0) | ~spl6_4),
% 0.23/0.57    inference(avatar_component_clause,[],[f72])).
% 0.23/0.57  fof(f72,plain,(
% 0.23/0.57    spl6_4 <=> v1_relat_1(k1_xboole_0)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.23/0.57  fof(f147,plain,(
% 0.23/0.57    ( ! [X4,X3] : (~v1_relat_1(X3) | r2_hidden(sK5(sK2(k1_xboole_0,k10_relat_1(X3,X4)),X4,X3),k2_relat_1(X3)) | k1_xboole_0 = k10_relat_1(X3,X4)) ) | ~spl6_2),
% 0.23/0.57    inference(resolution,[],[f139,f35])).
% 0.23/0.57  fof(f35,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK5(X0,X1,X2),k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f20])).
% 0.23/0.57  fof(f20,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.23/0.57    inference(ennf_transformation,[],[f12])).
% 0.23/0.57  fof(f12,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.23/0.57  fof(f139,plain,(
% 0.23/0.57    ( ! [X15] : (r2_hidden(sK2(k1_xboole_0,X15),X15) | k1_xboole_0 = X15) ) | ~spl6_2),
% 0.23/0.57    inference(forward_demodulation,[],[f136,f60])).
% 0.23/0.57  fof(f136,plain,(
% 0.23/0.57    ( ! [X15] : (r2_hidden(sK2(k1_xboole_0,X15),X15) | k2_relat_1(k1_xboole_0) = X15) )),
% 0.23/0.57    inference(resolution,[],[f31,f95])).
% 0.23/0.57  fof(f31,plain,(
% 0.23/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.23/0.57    inference(cnf_transformation,[],[f11])).
% 0.23/0.57  fof(f11,axiom,(
% 0.23/0.57    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.23/0.57  fof(f55,plain,(
% 0.23/0.57    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl6_1),
% 0.23/0.57    inference(avatar_component_clause,[],[f53])).
% 0.23/0.57  fof(f53,plain,(
% 0.23/0.57    spl6_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.23/0.57  fof(f101,plain,(
% 0.23/0.57    spl6_4),
% 0.23/0.57    inference(avatar_split_clause,[],[f97,f72])).
% 0.23/0.57  fof(f97,plain,(
% 0.23/0.57    v1_relat_1(k1_xboole_0)),
% 0.23/0.57    inference(resolution,[],[f95,f26])).
% 0.23/0.57  fof(f26,plain,(
% 0.23/0.57    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f18])).
% 0.23/0.57  fof(f18,plain,(
% 0.23/0.57    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.23/0.57    inference(ennf_transformation,[],[f16])).
% 0.23/0.57  fof(f16,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.23/0.57    inference(unused_predicate_definition_removal,[],[f10])).
% 0.23/0.57  fof(f10,axiom,(
% 0.23/0.57    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.23/0.57  fof(f61,plain,(
% 0.23/0.57    spl6_2),
% 0.23/0.57    inference(avatar_split_clause,[],[f23,f58])).
% 0.23/0.57  fof(f23,plain,(
% 0.23/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.23/0.57    inference(cnf_transformation,[],[f13])).
% 0.23/0.57  fof(f13,axiom,(
% 0.23/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.23/0.57  fof(f56,plain,(
% 0.23/0.57    ~spl6_1),
% 0.23/0.57    inference(avatar_split_clause,[],[f21,f53])).
% 0.23/0.57  fof(f21,plain,(
% 0.23/0.57    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.23/0.57    inference(cnf_transformation,[],[f17])).
% 0.23/0.57  fof(f17,plain,(
% 0.23/0.57    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.23/0.57    inference(ennf_transformation,[],[f15])).
% 0.23/0.57  fof(f15,negated_conjecture,(
% 0.23/0.57    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.23/0.57    inference(negated_conjecture,[],[f14])).
% 0.23/0.57  fof(f14,conjecture,(
% 0.23/0.57    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.23/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.23/0.57  % SZS output end Proof for theBenchmark
% 0.23/0.57  % (10898)------------------------------
% 0.23/0.57  % (10898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (10898)Termination reason: Refutation
% 0.23/0.57  
% 0.23/0.57  % (10898)Memory used [KB]: 10874
% 0.23/0.57  % (10898)Time elapsed: 0.141 s
% 0.23/0.57  % (10898)------------------------------
% 0.23/0.57  % (10898)------------------------------
% 0.23/0.57  % (10881)Success in time 0.189 s
%------------------------------------------------------------------------------
