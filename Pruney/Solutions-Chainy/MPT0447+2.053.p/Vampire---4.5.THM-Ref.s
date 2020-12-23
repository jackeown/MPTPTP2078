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
% DateTime   : Thu Dec  3 12:47:16 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 146 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  133 ( 493 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f847,plain,(
    $false ),
    inference(subsumption_resolution,[],[f846,f662])).

fof(f662,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(superposition,[],[f283,f46])).

fof(f46,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f25,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f283,plain,(
    ! [X0] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f65,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f65,plain,(
    ! [X2] : r1_tarski(k2_xboole_0(k1_relat_1(sK0),X2),k2_xboole_0(k1_relat_1(sK1),X2)) ),
    inference(resolution,[],[f54,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f54,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f53,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f51,f25])).

fof(f51,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f26,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f846,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f839,f27])).

fof(f27,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f839,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f787,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f36,f41])).

fof(f41,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f24,f29])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f787,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f212,f739])).

fof(f739,plain,(
    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f738,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f738,plain,
    ( r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1)) ),
    inference(superposition,[],[f463,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f463,plain,(
    r1_tarski(k2_xboole_0(k1_xboole_0,k2_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(resolution,[],[f108,f28])).

fof(f108,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_relat_1(sK1))
      | r1_tarski(k2_xboole_0(X2,k2_relat_1(sK1)),k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f34,f46])).

fof(f212,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK1),X1)
      | r1_tarski(k2_relat_1(sK0),X1) ) ),
    inference(superposition,[],[f35,f72])).

fof(f72,plain,(
    k2_relat_1(sK1) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f56,f33])).

fof(f56,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f55,f24])).

fof(f55,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f52,f25])).

fof(f52,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:58:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (31365)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (31382)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (31361)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (31368)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (31359)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (31375)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (31362)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (31368)Refutation not found, incomplete strategy% (31368)------------------------------
% 0.21/0.52  % (31368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31368)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31368)Memory used [KB]: 10490
% 0.21/0.52  % (31368)Time elapsed: 0.077 s
% 0.21/0.52  % (31368)------------------------------
% 0.21/0.52  % (31368)------------------------------
% 1.23/0.52  % (31360)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.23/0.52  % (31366)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.23/0.52  % (31366)Refutation not found, incomplete strategy% (31366)------------------------------
% 1.23/0.52  % (31366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (31366)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (31366)Memory used [KB]: 10490
% 1.23/0.52  % (31366)Time elapsed: 0.096 s
% 1.23/0.52  % (31366)------------------------------
% 1.23/0.52  % (31366)------------------------------
% 1.23/0.52  % (31370)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.23/0.52  % (31361)Refutation not found, incomplete strategy% (31361)------------------------------
% 1.23/0.52  % (31361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (31361)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (31361)Memory used [KB]: 10490
% 1.23/0.52  % (31361)Time elapsed: 0.109 s
% 1.23/0.52  % (31361)------------------------------
% 1.23/0.52  % (31361)------------------------------
% 1.23/0.52  % (31376)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.23/0.52  % (31378)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.23/0.53  % (31379)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.23/0.53  % (31380)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.40/0.54  % (31377)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.40/0.54  % (31369)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.40/0.54  % (31358)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.40/0.54  % (31371)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.40/0.54  % (31363)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.40/0.55  % (31364)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.40/0.55  % (31367)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.40/0.55  % (31381)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.40/0.55  % (31374)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.40/0.56  % (31373)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.40/0.56  % (31369)Refutation found. Thanks to Tanya!
% 1.40/0.56  % SZS status Theorem for theBenchmark
% 1.40/0.56  % SZS output start Proof for theBenchmark
% 1.40/0.56  fof(f847,plain,(
% 1.40/0.56    $false),
% 1.40/0.56    inference(subsumption_resolution,[],[f846,f662])).
% 1.40/0.56  fof(f662,plain,(
% 1.40/0.56    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 1.40/0.56    inference(superposition,[],[f283,f46])).
% 1.40/0.56  fof(f46,plain,(
% 1.40/0.56    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),
% 1.40/0.56    inference(resolution,[],[f25,f29])).
% 1.40/0.56  fof(f29,plain,(
% 1.40/0.56    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f13])).
% 1.40/0.56  fof(f13,plain,(
% 1.40/0.56    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f7])).
% 1.40/0.56  fof(f7,axiom,(
% 1.40/0.56    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.40/0.56  fof(f25,plain,(
% 1.40/0.56    v1_relat_1(sK1)),
% 1.40/0.56    inference(cnf_transformation,[],[f23])).
% 1.40/0.56  fof(f23,plain,(
% 1.40/0.56    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22,f21])).
% 1.40/0.56  fof(f21,plain,(
% 1.40/0.56    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f22,plain,(
% 1.40/0.56    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f12,plain,(
% 1.40/0.56    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.40/0.56    inference(flattening,[],[f11])).
% 1.40/0.56  fof(f11,plain,(
% 1.40/0.56    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f10])).
% 1.40/0.56  fof(f10,negated_conjecture,(
% 1.40/0.56    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.40/0.56    inference(negated_conjecture,[],[f9])).
% 1.40/0.56  fof(f9,conjecture,(
% 1.40/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 1.40/0.56  fof(f283,plain,(
% 1.40/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X0))) )),
% 1.40/0.56    inference(resolution,[],[f65,f35])).
% 1.40/0.56  fof(f35,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f18])).
% 1.40/0.56  fof(f18,plain,(
% 1.40/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.40/0.56    inference(ennf_transformation,[],[f1])).
% 1.40/0.56  fof(f1,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.40/0.56  fof(f65,plain,(
% 1.40/0.56    ( ! [X2] : (r1_tarski(k2_xboole_0(k1_relat_1(sK0),X2),k2_xboole_0(k1_relat_1(sK1),X2))) )),
% 1.40/0.56    inference(resolution,[],[f54,f34])).
% 1.40/0.56  fof(f34,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f17])).
% 1.40/0.56  fof(f17,plain,(
% 1.40/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 1.40/0.56    inference(ennf_transformation,[],[f6])).
% 1.40/0.56  fof(f6,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 1.40/0.56  fof(f54,plain,(
% 1.40/0.56    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 1.40/0.56    inference(subsumption_resolution,[],[f53,f24])).
% 1.40/0.56  fof(f24,plain,(
% 1.40/0.56    v1_relat_1(sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f23])).
% 1.40/0.56  fof(f53,plain,(
% 1.40/0.56    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK0)),
% 1.40/0.56    inference(subsumption_resolution,[],[f51,f25])).
% 1.40/0.56  fof(f51,plain,(
% 1.40/0.56    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 1.40/0.56    inference(resolution,[],[f26,f30])).
% 1.40/0.56  fof(f30,plain,(
% 1.40/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f15])).
% 1.40/0.56  fof(f15,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.56    inference(flattening,[],[f14])).
% 1.40/0.56  fof(f14,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f8])).
% 1.40/0.56  fof(f8,axiom,(
% 1.40/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.40/0.56  fof(f26,plain,(
% 1.40/0.56    r1_tarski(sK0,sK1)),
% 1.40/0.56    inference(cnf_transformation,[],[f23])).
% 1.40/0.56  fof(f846,plain,(
% 1.40/0.56    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 1.40/0.56    inference(subsumption_resolution,[],[f839,f27])).
% 1.40/0.56  fof(f27,plain,(
% 1.40/0.56    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 1.40/0.56    inference(cnf_transformation,[],[f23])).
% 1.40/0.56  fof(f839,plain,(
% 1.40/0.56    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 1.40/0.56    inference(resolution,[],[f787,f99])).
% 1.40/0.56  fof(f99,plain,(
% 1.40/0.56    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 1.40/0.56    inference(superposition,[],[f36,f41])).
% 1.40/0.56  fof(f41,plain,(
% 1.40/0.56    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 1.40/0.56    inference(resolution,[],[f24,f29])).
% 1.40/0.56  fof(f36,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f20])).
% 1.40/0.56  fof(f20,plain,(
% 1.40/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.40/0.56    inference(flattening,[],[f19])).
% 1.40/0.56  fof(f19,plain,(
% 1.40/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.40/0.56    inference(ennf_transformation,[],[f5])).
% 1.40/0.56  fof(f5,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.40/0.56  fof(f787,plain,(
% 1.40/0.56    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 1.40/0.56    inference(resolution,[],[f212,f739])).
% 1.40/0.56  fof(f739,plain,(
% 1.40/0.56    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1))),
% 1.40/0.56    inference(subsumption_resolution,[],[f738,f28])).
% 1.40/0.56  fof(f28,plain,(
% 1.40/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f3])).
% 1.40/0.56  fof(f3,axiom,(
% 1.40/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.40/0.56  fof(f738,plain,(
% 1.40/0.56    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1)) | ~r1_tarski(k1_xboole_0,k2_relat_1(sK1))),
% 1.40/0.56    inference(superposition,[],[f463,f33])).
% 1.40/0.56  fof(f33,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f16])).
% 1.40/0.56  fof(f16,plain,(
% 1.40/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.40/0.56    inference(ennf_transformation,[],[f2])).
% 1.40/0.56  fof(f2,axiom,(
% 1.40/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.40/0.56  fof(f463,plain,(
% 1.40/0.56    r1_tarski(k2_xboole_0(k1_xboole_0,k2_relat_1(sK1)),k3_relat_1(sK1))),
% 1.40/0.56    inference(resolution,[],[f108,f28])).
% 1.40/0.56  fof(f108,plain,(
% 1.40/0.56    ( ! [X2] : (~r1_tarski(X2,k1_relat_1(sK1)) | r1_tarski(k2_xboole_0(X2,k2_relat_1(sK1)),k3_relat_1(sK1))) )),
% 1.40/0.56    inference(superposition,[],[f34,f46])).
% 1.40/0.56  fof(f212,plain,(
% 1.40/0.56    ( ! [X1] : (~r1_tarski(k2_relat_1(sK1),X1) | r1_tarski(k2_relat_1(sK0),X1)) )),
% 1.40/0.56    inference(superposition,[],[f35,f72])).
% 1.40/0.56  fof(f72,plain,(
% 1.40/0.56    k2_relat_1(sK1) = k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.40/0.56    inference(resolution,[],[f56,f33])).
% 1.40/0.56  fof(f56,plain,(
% 1.40/0.56    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.40/0.56    inference(subsumption_resolution,[],[f55,f24])).
% 1.40/0.56  fof(f55,plain,(
% 1.40/0.56    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK0)),
% 1.40/0.56    inference(subsumption_resolution,[],[f52,f25])).
% 1.40/0.56  fof(f52,plain,(
% 1.40/0.56    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 1.40/0.56    inference(resolution,[],[f26,f31])).
% 1.40/0.56  fof(f31,plain,(
% 1.40/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f15])).
% 1.40/0.56  % SZS output end Proof for theBenchmark
% 1.40/0.56  % (31369)------------------------------
% 1.40/0.56  % (31369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (31369)Termination reason: Refutation
% 1.40/0.56  
% 1.40/0.56  % (31369)Memory used [KB]: 2174
% 1.40/0.56  % (31369)Time elapsed: 0.135 s
% 1.40/0.56  % (31369)------------------------------
% 1.40/0.56  % (31369)------------------------------
% 1.40/0.57  % (31357)Success in time 0.204 s
%------------------------------------------------------------------------------
