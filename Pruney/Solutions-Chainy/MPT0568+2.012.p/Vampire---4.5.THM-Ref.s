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
% DateTime   : Thu Dec  3 12:50:11 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   40 (  42 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 (  79 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f52])).

fof(f52,plain,(
    ~ spl1_2 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | ~ spl1_2 ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl1_2 ),
    inference(superposition,[],[f17,f45])).

fof(f45,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl1_2 ),
    inference(resolution,[],[f44,f20])).

fof(f20,plain,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).

fof(f44,plain,
    ( ! [X0] :
        ( r2_xboole_0(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
        | k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) )
    | ~ spl1_2 ),
    inference(resolution,[],[f37,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f37,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl1_2
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f17,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(f43,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f42])).

fof(f42,plain,
    ( $false
    | spl1_1 ),
    inference(resolution,[],[f41,f28])).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

% (10257)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f21,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f41,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_1 ),
    inference(resolution,[],[f34,f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f34,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl1_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f38,plain,
    ( ~ spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f30,f36,f32])).

fof(f30,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f24,f18])).

fof(f18,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:53:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.46/0.56  % (10241)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.56  % (10244)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.46/0.56  % (10243)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.57  % (10244)Refutation found. Thanks to Tanya!
% 1.46/0.57  % SZS status Theorem for theBenchmark
% 1.46/0.57  % (10249)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.57  % (10252)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.46/0.57  % (10259)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.57  % (10243)Refutation not found, incomplete strategy% (10243)------------------------------
% 1.46/0.57  % (10243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (10260)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.57  % SZS output start Proof for theBenchmark
% 1.46/0.57  fof(f54,plain,(
% 1.46/0.57    $false),
% 1.46/0.57    inference(avatar_sat_refutation,[],[f38,f43,f52])).
% 1.46/0.57  fof(f52,plain,(
% 1.46/0.57    ~spl1_2),
% 1.46/0.57    inference(avatar_contradiction_clause,[],[f51])).
% 1.46/0.57  fof(f51,plain,(
% 1.46/0.57    $false | ~spl1_2),
% 1.46/0.57    inference(trivial_inequality_removal,[],[f49])).
% 1.46/0.57  fof(f49,plain,(
% 1.46/0.57    k1_xboole_0 != k1_xboole_0 | ~spl1_2),
% 1.46/0.57    inference(superposition,[],[f17,f45])).
% 1.46/0.57  fof(f45,plain,(
% 1.46/0.57    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | ~spl1_2),
% 1.46/0.57    inference(resolution,[],[f44,f20])).
% 1.46/0.57  fof(f20,plain,(
% 1.46/0.57    ( ! [X0] : (~r2_xboole_0(X0,k1_xboole_0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f2])).
% 1.46/0.57  fof(f2,axiom,(
% 1.46/0.57    ! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).
% 1.46/0.57  fof(f44,plain,(
% 1.46/0.57    ( ! [X0] : (r2_xboole_0(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | ~spl1_2),
% 1.46/0.57    inference(resolution,[],[f37,f27])).
% 1.46/0.57  fof(f27,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f16])).
% 1.46/0.57  fof(f16,plain,(
% 1.46/0.57    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.46/0.57    inference(flattening,[],[f15])).
% 1.46/0.57  fof(f15,plain,(
% 1.46/0.57    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.46/0.57    inference(nnf_transformation,[],[f1])).
% 1.46/0.57  fof(f1,axiom,(
% 1.46/0.57    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.46/0.57  fof(f37,plain,(
% 1.46/0.57    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl1_2),
% 1.46/0.57    inference(avatar_component_clause,[],[f36])).
% 1.46/0.57  fof(f36,plain,(
% 1.46/0.57    spl1_2 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.46/0.57  fof(f17,plain,(
% 1.46/0.57    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f14])).
% 1.46/0.57  fof(f14,plain,(
% 1.46/0.57    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).
% 1.46/0.57  fof(f13,plain,(
% 1.46/0.57    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f10,plain,(
% 1.46/0.57    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 1.46/0.57    inference(ennf_transformation,[],[f9])).
% 1.46/0.57  fof(f9,negated_conjecture,(
% 1.46/0.57    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.46/0.57    inference(negated_conjecture,[],[f8])).
% 1.46/0.57  fof(f8,conjecture,(
% 1.46/0.57    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 1.46/0.57  fof(f43,plain,(
% 1.46/0.57    spl1_1),
% 1.46/0.57    inference(avatar_contradiction_clause,[],[f42])).
% 1.46/0.57  fof(f42,plain,(
% 1.46/0.57    $false | spl1_1),
% 1.46/0.57    inference(resolution,[],[f41,f28])).
% 1.46/0.57  fof(f28,plain,(
% 1.46/0.57    v1_xboole_0(k1_xboole_0)),
% 1.46/0.57    inference(definition_unfolding,[],[f21,f22])).
% 1.46/0.57  fof(f22,plain,(
% 1.46/0.57    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f3])).
% 1.46/0.57  % (10257)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.46/0.57  fof(f3,axiom,(
% 1.46/0.57    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.46/0.57  fof(f21,plain,(
% 1.46/0.57    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f4])).
% 1.46/0.57  fof(f4,axiom,(
% 1.46/0.57    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).
% 1.46/0.57  fof(f41,plain,(
% 1.46/0.57    ~v1_xboole_0(k1_xboole_0) | spl1_1),
% 1.46/0.57    inference(resolution,[],[f34,f23])).
% 1.46/0.57  fof(f23,plain,(
% 1.46/0.57    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f11])).
% 1.46/0.57  fof(f11,plain,(
% 1.46/0.57    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.46/0.57    inference(ennf_transformation,[],[f5])).
% 1.46/0.57  fof(f5,axiom,(
% 1.46/0.57    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.46/0.57  fof(f34,plain,(
% 1.46/0.57    ~v1_relat_1(k1_xboole_0) | spl1_1),
% 1.46/0.57    inference(avatar_component_clause,[],[f32])).
% 1.46/0.57  fof(f32,plain,(
% 1.46/0.57    spl1_1 <=> v1_relat_1(k1_xboole_0)),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.46/0.57  fof(f38,plain,(
% 1.46/0.57    ~spl1_1 | spl1_2),
% 1.46/0.57    inference(avatar_split_clause,[],[f30,f36,f32])).
% 1.46/0.57  fof(f30,plain,(
% 1.46/0.57    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.46/0.57    inference(superposition,[],[f24,f18])).
% 1.46/0.57  fof(f18,plain,(
% 1.46/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.46/0.57    inference(cnf_transformation,[],[f7])).
% 1.46/0.57  fof(f7,axiom,(
% 1.46/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.46/0.57  fof(f24,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f12])).
% 1.46/0.57  fof(f12,plain,(
% 1.46/0.57    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f6])).
% 1.46/0.57  fof(f6,axiom,(
% 1.46/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.46/0.57  % SZS output end Proof for theBenchmark
% 1.46/0.57  % (10244)------------------------------
% 1.46/0.57  % (10244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (10244)Termination reason: Refutation
% 1.46/0.57  
% 1.46/0.57  % (10244)Memory used [KB]: 6140
% 1.46/0.57  % (10244)Time elapsed: 0.126 s
% 1.46/0.57  % (10244)------------------------------
% 1.46/0.57  % (10244)------------------------------
% 1.46/0.57  % (10257)Refutation not found, incomplete strategy% (10257)------------------------------
% 1.46/0.57  % (10257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (10231)Success in time 0.207 s
%------------------------------------------------------------------------------
