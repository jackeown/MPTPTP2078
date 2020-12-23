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
% DateTime   : Thu Dec  3 12:47:10 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 142 expanded)
%              Number of leaves         :   11 (  43 expanded)
%              Depth                    :   18
%              Number of atoms          :  147 ( 495 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1311,f1357])).

fof(f1357,plain,(
    ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f1356])).

fof(f1356,plain,
    ( $false
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f1307,f354])).

fof(f354,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl2_18
  <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f1307,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1283,f33])).

fof(f33,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f1283,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(superposition,[],[f84,f1275])).

fof(f1275,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k3_relat_1(sK1),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f1274,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f1274,plain,
    ( k3_relat_1(sK1) = k2_xboole_0(k3_relat_1(sK1),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f367,f32])).

fof(f32,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f367,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | k3_relat_1(sK1) = k2_xboole_0(k3_relat_1(sK1),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f366,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f366,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | ~ v1_relat_1(X1)
      | k3_relat_1(sK1) = k2_xboole_0(k2_relat_1(X1),k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f155,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f155,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k3_relat_1(sK1))
      | ~ r1_tarski(X0,sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f154,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f154,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k3_relat_1(sK1))
      | ~ r1_tarski(X0,sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f99,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f99,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | r1_tarski(X0,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f46,f52])).

fof(f52,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f31,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f84,plain,(
    ! [X1] :
      ( r1_tarski(k3_relat_1(sK0),k2_xboole_0(X1,k2_relat_1(sK0)))
      | ~ r1_tarski(k1_relat_1(sK0),X1) ) ),
    inference(superposition,[],[f47,f51])).

fof(f51,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f30,f34])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f1311,plain,(
    spl2_18 ),
    inference(avatar_contradiction_clause,[],[f1310])).

fof(f1310,plain,
    ( $false
    | spl2_18 ),
    inference(subsumption_resolution,[],[f1309,f30])).

fof(f1309,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_18 ),
    inference(subsumption_resolution,[],[f1308,f32])).

fof(f1308,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | spl2_18 ),
    inference(resolution,[],[f353,f270])).

fof(f270,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k3_relat_1(sK1))
      | ~ r1_tarski(X0,sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f269,f31])).

fof(f269,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k3_relat_1(sK1))
      | ~ r1_tarski(X0,sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f256,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f256,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | r1_tarski(X0,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f101,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f101,plain,(
    ! [X2] :
      ( r1_tarski(k2_xboole_0(X2,k2_relat_1(sK1)),k3_relat_1(sK1))
      | ~ r1_tarski(X2,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f47,f52])).

fof(f353,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | spl2_18 ),
    inference(avatar_component_clause,[],[f352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:12:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (30544)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (30562)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (30554)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (30557)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (30541)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (30546)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (30542)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (30540)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (30559)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (30545)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (30551)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (30556)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (30550)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (30548)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (30552)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (30560)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (30543)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (30553)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (30564)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (30549)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (30558)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (30563)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (30555)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (30565)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.42/0.57  % (30561)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.42/0.57  % (30547)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.63/0.58  % (30541)Refutation found. Thanks to Tanya!
% 1.63/0.58  % SZS status Theorem for theBenchmark
% 1.63/0.58  % SZS output start Proof for theBenchmark
% 1.63/0.58  fof(f1358,plain,(
% 1.63/0.58    $false),
% 1.63/0.58    inference(avatar_sat_refutation,[],[f1311,f1357])).
% 1.63/0.58  fof(f1357,plain,(
% 1.63/0.58    ~spl2_18),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f1356])).
% 1.63/0.58  fof(f1356,plain,(
% 1.63/0.58    $false | ~spl2_18),
% 1.63/0.58    inference(subsumption_resolution,[],[f1307,f354])).
% 1.63/0.58  fof(f354,plain,(
% 1.63/0.58    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~spl2_18),
% 1.63/0.58    inference(avatar_component_clause,[],[f352])).
% 1.63/0.58  fof(f352,plain,(
% 1.63/0.58    spl2_18 <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.63/0.58  fof(f1307,plain,(
% 1.63/0.58    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 1.63/0.58    inference(subsumption_resolution,[],[f1283,f33])).
% 1.63/0.58  fof(f33,plain,(
% 1.63/0.58    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 1.63/0.58    inference(cnf_transformation,[],[f26])).
% 1.63/0.58  fof(f26,plain,(
% 1.63/0.58    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.63/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25,f24])).
% 1.63/0.58  fof(f24,plain,(
% 1.63/0.58    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.63/0.58    introduced(choice_axiom,[])).
% 1.63/0.58  fof(f25,plain,(
% 1.63/0.58    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 1.63/0.58    introduced(choice_axiom,[])).
% 1.63/0.58  fof(f15,plain,(
% 1.63/0.58    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.63/0.58    inference(flattening,[],[f14])).
% 1.63/0.58  fof(f14,plain,(
% 1.63/0.58    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f13])).
% 1.63/0.58  fof(f13,negated_conjecture,(
% 1.63/0.58    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.63/0.58    inference(negated_conjecture,[],[f12])).
% 1.63/0.58  fof(f12,conjecture,(
% 1.63/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 1.63/0.58  fof(f1283,plain,(
% 1.63/0.58    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 1.63/0.58    inference(superposition,[],[f84,f1275])).
% 1.63/0.58  fof(f1275,plain,(
% 1.63/0.58    k3_relat_1(sK1) = k2_xboole_0(k3_relat_1(sK1),k2_relat_1(sK0))),
% 1.63/0.58    inference(subsumption_resolution,[],[f1274,f30])).
% 1.63/0.58  fof(f30,plain,(
% 1.63/0.58    v1_relat_1(sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f26])).
% 1.63/0.58  fof(f1274,plain,(
% 1.63/0.58    k3_relat_1(sK1) = k2_xboole_0(k3_relat_1(sK1),k2_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 1.63/0.58    inference(resolution,[],[f367,f32])).
% 1.63/0.58  fof(f32,plain,(
% 1.63/0.58    r1_tarski(sK0,sK1)),
% 1.63/0.58    inference(cnf_transformation,[],[f26])).
% 1.63/0.58  fof(f367,plain,(
% 1.63/0.58    ( ! [X1] : (~r1_tarski(X1,sK1) | k3_relat_1(sK1) = k2_xboole_0(k3_relat_1(sK1),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.63/0.58    inference(forward_demodulation,[],[f366,f39])).
% 1.63/0.58  fof(f39,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f1])).
% 1.63/0.58  fof(f1,axiom,(
% 1.63/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.63/0.58  fof(f366,plain,(
% 1.63/0.58    ( ! [X1] : (~r1_tarski(X1,sK1) | ~v1_relat_1(X1) | k3_relat_1(sK1) = k2_xboole_0(k2_relat_1(X1),k3_relat_1(sK1))) )),
% 1.63/0.58    inference(resolution,[],[f155,f40])).
% 1.63/0.58  fof(f40,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.63/0.58    inference(cnf_transformation,[],[f20])).
% 1.63/0.58  fof(f20,plain,(
% 1.63/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.63/0.58    inference(ennf_transformation,[],[f5])).
% 1.63/0.58  fof(f5,axiom,(
% 1.63/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.63/0.58  fof(f155,plain,(
% 1.63/0.58    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k3_relat_1(sK1)) | ~r1_tarski(X0,sK1) | ~v1_relat_1(X0)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f154,f31])).
% 1.63/0.59  fof(f31,plain,(
% 1.63/0.59    v1_relat_1(sK1)),
% 1.63/0.59    inference(cnf_transformation,[],[f26])).
% 1.63/0.59  fof(f154,plain,(
% 1.63/0.59    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k3_relat_1(sK1)) | ~r1_tarski(X0,sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(X0)) )),
% 1.63/0.59    inference(resolution,[],[f99,f36])).
% 1.63/0.59  fof(f36,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f18])).
% 1.63/0.59  fof(f18,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.63/0.59    inference(flattening,[],[f17])).
% 1.63/0.59  fof(f17,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.63/0.59    inference(ennf_transformation,[],[f11])).
% 1.63/0.59  fof(f11,axiom,(
% 1.63/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.63/0.59  fof(f99,plain,(
% 1.63/0.59    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | r1_tarski(X0,k3_relat_1(sK1))) )),
% 1.63/0.59    inference(superposition,[],[f46,f52])).
% 1.63/0.59  fof(f52,plain,(
% 1.63/0.59    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),
% 1.63/0.59    inference(resolution,[],[f31,f34])).
% 1.63/0.59  fof(f34,plain,(
% 1.63/0.59    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f16])).
% 1.63/0.59  fof(f16,plain,(
% 1.63/0.59    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.63/0.59    inference(ennf_transformation,[],[f10])).
% 1.63/0.59  fof(f10,axiom,(
% 1.63/0.59    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 1.63/0.59  fof(f46,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f21])).
% 1.63/0.59  fof(f21,plain,(
% 1.63/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.63/0.59    inference(ennf_transformation,[],[f3])).
% 1.63/0.59  fof(f3,axiom,(
% 1.63/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.63/0.59  fof(f84,plain,(
% 1.63/0.59    ( ! [X1] : (r1_tarski(k3_relat_1(sK0),k2_xboole_0(X1,k2_relat_1(sK0))) | ~r1_tarski(k1_relat_1(sK0),X1)) )),
% 1.63/0.59    inference(superposition,[],[f47,f51])).
% 1.63/0.59  fof(f51,plain,(
% 1.63/0.59    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 1.63/0.59    inference(resolution,[],[f30,f34])).
% 1.63/0.59  fof(f47,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f22])).
% 1.63/0.59  fof(f22,plain,(
% 1.63/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 1.63/0.59    inference(ennf_transformation,[],[f7])).
% 1.63/0.59  fof(f7,axiom,(
% 1.63/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).
% 1.63/0.59  fof(f1311,plain,(
% 1.63/0.59    spl2_18),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f1310])).
% 1.63/0.59  fof(f1310,plain,(
% 1.63/0.59    $false | spl2_18),
% 1.63/0.59    inference(subsumption_resolution,[],[f1309,f30])).
% 1.63/0.59  fof(f1309,plain,(
% 1.63/0.59    ~v1_relat_1(sK0) | spl2_18),
% 1.63/0.59    inference(subsumption_resolution,[],[f1308,f32])).
% 1.63/0.59  fof(f1308,plain,(
% 1.63/0.59    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0) | spl2_18),
% 1.63/0.59    inference(resolution,[],[f353,f270])).
% 1.63/0.59  fof(f270,plain,(
% 1.63/0.59    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) | ~r1_tarski(X0,sK1) | ~v1_relat_1(X0)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f269,f31])).
% 1.63/0.59  fof(f269,plain,(
% 1.63/0.59    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k3_relat_1(sK1)) | ~r1_tarski(X0,sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(X0)) )),
% 1.63/0.59    inference(resolution,[],[f256,f35])).
% 1.63/0.59  fof(f35,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f18])).
% 1.63/0.59  fof(f256,plain,(
% 1.63/0.59    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k3_relat_1(sK1))) )),
% 1.63/0.59    inference(resolution,[],[f101,f48])).
% 1.63/0.59  fof(f48,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f23])).
% 1.63/0.59  fof(f23,plain,(
% 1.63/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.63/0.59    inference(ennf_transformation,[],[f4])).
% 1.63/0.59  fof(f4,axiom,(
% 1.63/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.63/0.59  fof(f101,plain,(
% 1.63/0.59    ( ! [X2] : (r1_tarski(k2_xboole_0(X2,k2_relat_1(sK1)),k3_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK1))) )),
% 1.63/0.59    inference(superposition,[],[f47,f52])).
% 1.63/0.59  fof(f353,plain,(
% 1.63/0.59    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | spl2_18),
% 1.63/0.59    inference(avatar_component_clause,[],[f352])).
% 1.63/0.59  % SZS output end Proof for theBenchmark
% 1.63/0.59  % (30541)------------------------------
% 1.63/0.59  % (30541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (30541)Termination reason: Refutation
% 1.63/0.59  
% 1.63/0.59  % (30541)Memory used [KB]: 11385
% 1.63/0.59  % (30541)Time elapsed: 0.154 s
% 1.63/0.59  % (30541)------------------------------
% 1.63/0.59  % (30541)------------------------------
% 1.63/0.59  % (30537)Success in time 0.225 s
%------------------------------------------------------------------------------
