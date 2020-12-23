%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 (  82 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f52,f59])).

fof(f59,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f31,f37])).

fof(f37,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_1
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( v1_relat_1(sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f6,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_relat_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relat_1)).

fof(f52,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f50])).

fof(f50,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f21,f49])).

fof(f49,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f48,f41])).

fof(f41,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_2
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f43,f25])).

% (29612)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f43,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f28,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f21,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f15])).

fof(f15,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(f42,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f34,f39,f36])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f24,f23])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:28:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (29602)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (29607)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.50  % (29619)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (29620)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (29601)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (29601)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f42,f52,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ~spl2_1),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    $false | ~spl2_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f31,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    spl2_1 <=> ! [X0] : ~v1_relat_1(X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    v1_relat_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    v1_relat_1(sK1) & ~v1_xboole_0(sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f6,f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0] : (v1_relat_1(X0) & ~v1_xboole_0(X0)) => (v1_relat_1(sK1) & ~v1_xboole_0(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ? [X0] : (v1_relat_1(X0) & ~v1_xboole_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relat_1)).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ~spl2_2),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    $false | ~spl2_2),
% 0.22/0.51    inference(subsumption_resolution,[],[f21,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl2_2),
% 0.22/0.51    inference(subsumption_resolution,[],[f48,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    v1_relat_1(k1_xboole_0) | ~spl2_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    spl2_2 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.51    inference(resolution,[],[f43,f25])).
% 0.22/0.51  % (29612)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(resolution,[],[f28,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    spl2_1 | spl2_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f34,f39,f36])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(resolution,[],[f24,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (29601)------------------------------
% 0.22/0.51  % (29601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29601)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (29601)Memory used [KB]: 6140
% 0.22/0.51  % (29601)Time elapsed: 0.097 s
% 0.22/0.51  % (29601)------------------------------
% 0.22/0.51  % (29601)------------------------------
% 0.22/0.51  % (29608)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (29599)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (29610)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (29596)Success in time 0.142 s
%------------------------------------------------------------------------------
