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
% DateTime   : Thu Dec  3 12:41:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 (  86 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f55])).

fof(f55,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f52,f25])).

fof(f25,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

% (876)Refutation not found, incomplete strategy% (876)------------------------------
% (876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (876)Termination reason: Refutation not found, incomplete strategy

% (876)Memory used [KB]: 6012
% (876)Time elapsed: 0.099 s
% (876)------------------------------
% (876)------------------------------
fof(f52,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl3_2 ),
    inference(resolution,[],[f50,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f50,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1))
    | spl3_2 ),
    inference(resolution,[],[f43,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f43,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f49,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f48])).

fof(f48,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f46,f18])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f46,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(resolution,[],[f39,f19])).

fof(f39,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f35,f41,f37])).

fof(f35,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f24,f17])).

fof(f17,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (873)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (890)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (875)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (894)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (876)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (892)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (880)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (887)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (874)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (885)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (886)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (887)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f44,f49,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    $false | spl3_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f52,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  % (876)Refutation not found, incomplete strategy% (876)------------------------------
% 0.21/0.51  % (876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (876)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (876)Memory used [KB]: 6012
% 0.21/0.51  % (876)Time elapsed: 0.099 s
% 0.21/0.51  % (876)------------------------------
% 0.21/0.51  % (876)------------------------------
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK1) | spl3_2),
% 0.21/0.51    inference(resolution,[],[f50,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k2_xboole_0(sK0,sK1)) | spl3_2),
% 0.21/0.51    inference(resolution,[],[f43,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ~r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) | spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    spl3_2 <=> r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    spl3_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    $false | spl3_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f46,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ~r1_tarski(sK0,k2_xboole_0(sK0,sK1)) | spl3_1),
% 0.21/0.51    inference(resolution,[],[f39,f19])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    spl3_1 <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f41,f37])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ~r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.21/0.51    inference(resolution,[],[f24,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (887)------------------------------
% 0.21/0.51  % (887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (887)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (887)Memory used [KB]: 6140
% 0.21/0.51  % (887)Time elapsed: 0.061 s
% 0.21/0.51  % (887)------------------------------
% 0.21/0.51  % (887)------------------------------
% 0.21/0.52  % (870)Success in time 0.158 s
%------------------------------------------------------------------------------
