%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 183 expanded)
%              Number of leaves         :    9 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  149 ( 685 expanded)
%              Number of equality atoms :   23 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f898,plain,(
    $false ),
    inference(subsumption_resolution,[],[f888,f821])).

fof(f821,plain,(
    ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
    inference(resolution,[],[f807,f27])).

fof(f27,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
      | ~ r1_tarski(sK0,sK1) )
    & ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
      | r1_tarski(sK0,sK1) )
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
              | ~ r1_tarski(X0,X1) )
            & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
              | r1_tarski(X0,X1) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
            | ~ r1_tarski(sK0,X1) )
          & ( r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
            | r1_tarski(sK0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
          | ~ r1_tarski(sK0,X1) )
        & ( r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
          | r1_tarski(sK0,X1) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
        | ~ r1_tarski(sK0,sK1) )
      & ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
        | r1_tarski(sK0,sK1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | ~ r1_tarski(X0,X1) )
          & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | r1_tarski(X0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | ~ r1_tarski(X0,X1) )
          & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | r1_tarski(X0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_tarski(X0,X1)
          <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
            <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
          <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).

fof(f807,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f40,f791])).

fof(f791,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f785,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f785,plain,
    ( r1_tarski(sK0,sK1)
    | sK1 = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f766,f56])).

fof(f56,plain,(
    ! [X1] : sK1 = k2_xboole_0(k7_relat_1(sK1,X1),sK1) ),
    inference(resolution,[],[f39,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

% (2390)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f39,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k2_xboole_0(k7_relat_1(X1,X2),X1) = X1 ) ),
    inference(resolution,[],[f31,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f766,plain,(
    ! [X29] :
      ( r1_tarski(sK0,k2_xboole_0(k7_relat_1(sK1,k1_relat_1(sK0)),X29))
      | sK1 = k2_xboole_0(sK0,sK1) ) ),
    inference(superposition,[],[f43,f494])).

fof(f494,plain,
    ( k7_relat_1(sK1,k1_relat_1(sK0)) = k2_xboole_0(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f49,f31])).

fof(f49,plain,
    ( r1_tarski(sK0,sK1)
    | k7_relat_1(sK1,k1_relat_1(sK0)) = k2_xboole_0(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
    inference(resolution,[],[f26,f31])).

fof(f26,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f35,f36])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f888,plain,(
    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
    inference(superposition,[],[f820,f125])).

fof(f125,plain,(
    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f123,f36])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | sK0 = k7_relat_1(sK0,X0) ) ),
    inference(resolution,[],[f29,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f820,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK0,X0),k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f807,f486])).

fof(f486,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,sK1)
      | r1_tarski(k7_relat_1(sK0,X1),k7_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f483,f25])).

fof(f483,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(sK0,X0)
      | r1_tarski(k7_relat_1(sK0,X1),k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f30,f24])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:43:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (2373)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (2369)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (2371)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (2374)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (2370)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (2389)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (2373)Refutation not found, incomplete strategy% (2373)------------------------------
% 0.22/0.54  % (2373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2369)Refutation not found, incomplete strategy% (2369)------------------------------
% 0.22/0.55  % (2369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2369)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2369)Memory used [KB]: 10618
% 0.22/0.55  % (2369)Time elapsed: 0.110 s
% 0.22/0.55  % (2369)------------------------------
% 0.22/0.55  % (2369)------------------------------
% 0.22/0.55  % (2373)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2373)Memory used [KB]: 6140
% 0.22/0.55  % (2373)Time elapsed: 0.116 s
% 0.22/0.55  % (2373)------------------------------
% 0.22/0.55  % (2373)------------------------------
% 0.22/0.55  % (2387)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.55  % (2374)Refutation not found, incomplete strategy% (2374)------------------------------
% 0.22/0.55  % (2374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2374)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2374)Memory used [KB]: 10618
% 0.22/0.55  % (2374)Time elapsed: 0.113 s
% 0.22/0.55  % (2374)------------------------------
% 0.22/0.55  % (2374)------------------------------
% 0.22/0.55  % (2385)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.56  % (2393)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.56  % (2375)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.56  % (2382)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.57  % (2383)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.57  % (2379)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.57  % (2372)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.57  % (2379)Refutation not found, incomplete strategy% (2379)------------------------------
% 0.22/0.57  % (2379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (2379)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (2379)Memory used [KB]: 10618
% 0.22/0.57  % (2379)Time elapsed: 0.140 s
% 0.22/0.57  % (2379)------------------------------
% 0.22/0.57  % (2379)------------------------------
% 0.22/0.57  % (2389)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f898,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f888,f821])).
% 0.22/0.57  fof(f821,plain,(
% 0.22/0.57    ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))),
% 0.22/0.57    inference(resolution,[],[f807,f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ~r1_tarski(sK0,sK1) | ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ((~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)) & (r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : ((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : ((~r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~r1_tarski(sK0,X1)) & (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | r1_tarski(sK0,X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ? [X1] : ((~r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~r1_tarski(sK0,X1)) & (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | r1_tarski(sK0,X1)) & v1_relat_1(X1)) => ((~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)) & (r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)) & v1_relat_1(sK1))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : ((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : ((r1_tarski(X0,X1) <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,negated_conjecture,(
% 0.22/0.57    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.22/0.57    inference(negated_conjecture,[],[f7])).
% 0.22/0.57  fof(f7,conjecture,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).
% 0.22/0.57  fof(f807,plain,(
% 0.22/0.57    r1_tarski(sK0,sK1)),
% 0.22/0.57    inference(superposition,[],[f40,f791])).
% 0.22/0.57  fof(f791,plain,(
% 0.22/0.57    sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.57    inference(subsumption_resolution,[],[f785,f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.57  fof(f785,plain,(
% 0.22/0.57    r1_tarski(sK0,sK1) | sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.57    inference(superposition,[],[f766,f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ( ! [X1] : (sK1 = k2_xboole_0(k7_relat_1(sK1,X1),sK1)) )),
% 0.22/0.57    inference(resolution,[],[f39,f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    v1_relat_1(sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  % (2390)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ( ! [X2,X1] : (~v1_relat_1(X1) | k2_xboole_0(k7_relat_1(X1,X2),X1) = X1) )),
% 0.22/0.57    inference(resolution,[],[f31,f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.57  fof(f766,plain,(
% 0.22/0.57    ( ! [X29] : (r1_tarski(sK0,k2_xboole_0(k7_relat_1(sK1,k1_relat_1(sK0)),X29)) | sK1 = k2_xboole_0(sK0,sK1)) )),
% 0.22/0.57    inference(superposition,[],[f43,f494])).
% 0.22/0.57  fof(f494,plain,(
% 0.22/0.57    k7_relat_1(sK1,k1_relat_1(sK0)) = k2_xboole_0(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.57    inference(resolution,[],[f49,f31])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    r1_tarski(sK0,sK1) | k7_relat_1(sK1,k1_relat_1(sK0)) = k2_xboole_0(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))),
% 0.22/0.57    inference(resolution,[],[f26,f31])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 0.22/0.57    inference(resolution,[],[f40,f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.57    inference(ennf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(resolution,[],[f35,f36])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.58    inference(equality_resolution,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.58    inference(flattening,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.58  fof(f888,plain,(
% 0.22/0.58    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))),
% 0.22/0.58    inference(superposition,[],[f820,f125])).
% 0.22/0.58  fof(f125,plain,(
% 0.22/0.58    sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.22/0.58    inference(resolution,[],[f123,f36])).
% 0.22/0.58  fof(f123,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | sK0 = k7_relat_1(sK0,X0)) )),
% 0.22/0.58    inference(resolution,[],[f29,f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    v1_relat_1(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,plain,(
% 0.22/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(flattening,[],[f11])).
% 0.22/0.58  fof(f11,plain,(
% 0.22/0.58    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.58  fof(f820,plain,(
% 0.22/0.58    ( ! [X0] : (r1_tarski(k7_relat_1(sK0,X0),k7_relat_1(sK1,X0))) )),
% 0.22/0.58    inference(resolution,[],[f807,f486])).
% 0.22/0.58  fof(f486,plain,(
% 0.22/0.58    ( ! [X1] : (~r1_tarski(sK0,sK1) | r1_tarski(k7_relat_1(sK0,X1),k7_relat_1(sK1,X1))) )),
% 0.22/0.58    inference(resolution,[],[f483,f25])).
% 0.22/0.58  fof(f483,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(sK0,X0) | r1_tarski(k7_relat_1(sK0,X1),k7_relat_1(X0,X1))) )),
% 0.22/0.58    inference(resolution,[],[f30,f24])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(flattening,[],[f13])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (2389)------------------------------
% 0.22/0.58  % (2389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (2389)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (2389)Memory used [KB]: 6780
% 0.22/0.58  % (2389)Time elapsed: 0.139 s
% 0.22/0.58  % (2389)------------------------------
% 0.22/0.58  % (2389)------------------------------
% 0.22/0.58  % (2367)Success in time 0.213 s
%------------------------------------------------------------------------------
