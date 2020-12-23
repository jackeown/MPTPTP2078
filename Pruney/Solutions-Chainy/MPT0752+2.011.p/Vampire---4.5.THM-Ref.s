%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 (  85 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  168 ( 241 expanded)
%              Number of equality atoms :   33 (  41 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f63,f69,f74,f112,f139,f152])).

fof(f152,plain,
    ( spl2_5
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl2_5
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f148,f73])).

fof(f73,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_5
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f148,plain,
    ( v5_ordinal1(k1_xboole_0)
    | ~ spl2_9 ),
    inference(superposition,[],[f37,f138])).

fof(f138,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl2_9
  <=> k1_xboole_0 = sK1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f37,plain,(
    ! [X0] : v5_ordinal1(sK1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v5_ordinal1(sK1(X0))
      & v1_funct_1(sK1(X0))
      & v5_relat_1(sK1(X0),X0)
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f20])).

% (21201)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v5_ordinal1(X1)
          & v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
     => ( v5_ordinal1(sK1(X0))
        & v1_funct_1(sK1(X0))
        & v5_relat_1(sK1(X0),X0)
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] :
      ( v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_ordinal1)).

fof(f139,plain,
    ( spl2_9
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f122,f109,f136])).

fof(f109,plain,
    ( spl2_7
  <=> k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

% (21201)Refutation not found, incomplete strategy% (21201)------------------------------
% (21201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21212)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (21201)Termination reason: Refutation not found, incomplete strategy

% (21201)Memory used [KB]: 6012
% (21201)Time elapsed: 0.089 s
% (21201)------------------------------
% (21201)------------------------------
% (21213)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (21219)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (21208)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f122,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f119,f34])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f119,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0))
    | ~ spl2_7 ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1(k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0))
    | ~ spl2_7 ),
    inference(superposition,[],[f33,f111])).

fof(f111,plain,
    ( k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f112,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f87,f109])).

fof(f87,plain,(
    k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f85,f34])).

fof(f85,plain,
    ( k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0))
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(resolution,[],[f83,f35])).

fof(f35,plain,(
    ! [X0] : v5_relat_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v5_relat_1(X0,k1_xboole_0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f78,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f78,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f74,plain,
    ( ~ spl2_4
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f64,f71,f60,f66])).

fof(f66,plain,
    ( spl2_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f60,plain,
    ( spl2_3
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f64,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f25,f39])).

fof(f39,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

fof(f25,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ~ v5_ordinal1(k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
   => ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,sK0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f69,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f58,f53,f66])).

fof(f53,plain,
    ( spl2_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f58,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f29,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f63,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f57,f53,f60])).

fof(f57,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f30,f55])).

fof(f30,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f56,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:36:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (21198)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (21204)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (21204)Refutation not found, incomplete strategy% (21204)------------------------------
% 0.22/0.50  % (21204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21204)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (21204)Memory used [KB]: 1663
% 0.22/0.50  % (21204)Time elapsed: 0.080 s
% 0.22/0.50  % (21204)------------------------------
% 0.22/0.50  % (21204)------------------------------
% 0.22/0.50  % (21198)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (21199)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (21203)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (21210)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (21218)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (21216)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f56,f63,f69,f74,f112,f139,f152])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    spl2_5 | ~spl2_9),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f151])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    $false | (spl2_5 | ~spl2_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f148,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ~v5_ordinal1(k1_xboole_0) | spl2_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    spl2_5 <=> v5_ordinal1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    v5_ordinal1(k1_xboole_0) | ~spl2_9),
% 0.22/0.51    inference(superposition,[],[f37,f138])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    k1_xboole_0 = sK1(k1_xboole_0) | ~spl2_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f136])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    spl2_9 <=> k1_xboole_0 = sK1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0] : (v5_ordinal1(sK1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (v5_ordinal1(sK1(X0)) & v1_funct_1(sK1(X0)) & v5_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f20])).
% 0.22/0.51  % (21201)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v5_ordinal1(sK1(X0)) & v1_funct_1(sK1(X0)) & v5_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : ? [X1] : (v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_ordinal1)).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    spl2_9 | ~spl2_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f122,f109,f136])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    spl2_7 <=> k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.51  % (21201)Refutation not found, incomplete strategy% (21201)------------------------------
% 0.22/0.51  % (21201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21212)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (21201)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21201)Memory used [KB]: 6012
% 0.22/0.51  % (21201)Time elapsed: 0.089 s
% 0.22/0.51  % (21201)------------------------------
% 0.22/0.51  % (21201)------------------------------
% 0.22/0.51  % (21213)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (21219)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (21208)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    k1_xboole_0 = sK1(k1_xboole_0) | ~spl2_7),
% 0.22/0.51    inference(subsumption_resolution,[],[f119,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    k1_xboole_0 = sK1(k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0)) | ~spl2_7),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1(k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0)) | ~spl2_7),
% 0.22/0.51    inference(superposition,[],[f33,f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0)) | ~spl2_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f109])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    spl2_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f87,f109])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f85,f34])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0)) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.22/0.52    inference(resolution,[],[f83,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0] : (v5_relat_1(sK1(X0),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X0] : (~v5_relat_1(X0,k1_xboole_0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(resolution,[],[f78,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(resolution,[],[f44,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ~spl2_4 | ~spl2_3 | ~spl2_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f64,f71,f60,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    spl2_4 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    spl2_3 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f25,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) => (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.22/0.52    inference(negated_conjecture,[],[f11])).
% 0.22/0.52  fof(f11,conjecture,(
% 0.22/0.52    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl2_4 | ~spl2_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f58,f53,f66])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    spl2_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    v1_relat_1(k1_xboole_0) | ~spl2_2),
% 0.22/0.52    inference(superposition,[],[f29,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl2_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f53])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    spl2_3 | ~spl2_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f57,f53,f60])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    v1_funct_1(k1_xboole_0) | ~spl2_2),
% 0.22/0.52    inference(superposition,[],[f30,f55])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    spl2_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f27,f53])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (21198)------------------------------
% 0.22/0.52  % (21198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21198)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (21198)Memory used [KB]: 6140
% 0.22/0.52  % (21198)Time elapsed: 0.089 s
% 0.22/0.52  % (21198)------------------------------
% 0.22/0.52  % (21198)------------------------------
% 0.22/0.52  % (21195)Success in time 0.156 s
%------------------------------------------------------------------------------
