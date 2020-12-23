%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 115 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 301 expanded)
%              Number of equality atoms :   33 ( 112 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f365,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f273,f364])).

fof(f364,plain,(
    ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f362,f139])).

fof(f139,plain,(
    k9_relat_1(sK0,sK1) = k9_relat_1(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f135,f45])).

fof(f45,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(sK0,X2)) = k9_relat_1(sK0,X2) ),
    inference(resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f135,plain,(
    k9_relat_1(sK0,k3_xboole_0(sK1,sK2)) = k2_relat_1(k7_relat_1(sK0,sK1)) ),
    inference(superposition,[],[f45,f85])).

fof(f85,plain,(
    k7_relat_1(sK0,sK1) = k7_relat_1(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f80,f44])).

fof(f44,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f28,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f80,plain,(
    k7_relat_1(sK0,sK1) = k7_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f47,f28])).

fof(f47,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,sK1) = k7_relat_1(k7_relat_1(X1,sK1),sK2) ) ),
    inference(resolution,[],[f29,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f29,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f362,plain,
    ( k9_relat_1(sK0,sK1) != k9_relat_1(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f361,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f361,plain,
    ( k9_relat_1(sK0,sK1) != k9_relat_1(sK0,k3_xboole_0(sK2,sK1))
    | ~ spl3_11 ),
    inference(superposition,[],[f30,f287])).

fof(f287,plain,
    ( ! [X3] : k9_relat_1(k7_relat_1(sK0,sK2),X3) = k9_relat_1(sK0,k3_xboole_0(sK2,X3))
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f286,f45])).

fof(f286,plain,
    ( ! [X3] : k9_relat_1(k7_relat_1(sK0,sK2),X3) = k2_relat_1(k7_relat_1(sK0,k3_xboole_0(sK2,X3)))
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f277,f44])).

fof(f277,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(k7_relat_1(sK0,sK2),X3)) = k9_relat_1(k7_relat_1(sK0,sK2),X3)
    | ~ spl3_11 ),
    inference(resolution,[],[f262,f34])).

fof(f262,plain,
    ( v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl3_11
  <=> v1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f30,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f273,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl3_11 ),
    inference(subsumption_resolution,[],[f271,f28])).

fof(f271,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_11 ),
    inference(resolution,[],[f263,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f263,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:57:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (24023)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (24021)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (24040)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (24032)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (24038)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (24022)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (24036)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (24024)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (24026)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (24030)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (24018)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (24031)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (24043)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (24034)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (24028)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (24019)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (24029)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (24020)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (24033)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (24041)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (24035)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (24019)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f365,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f273,f364])).
% 0.21/0.54  fof(f364,plain,(
% 0.21/0.54    ~spl3_11),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f363])).
% 0.21/0.54  fof(f363,plain,(
% 0.21/0.54    $false | ~spl3_11),
% 0.21/0.54    inference(subsumption_resolution,[],[f362,f139])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    k9_relat_1(sK0,sK1) = k9_relat_1(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.54    inference(forward_demodulation,[],[f135,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X2] : (k2_relat_1(k7_relat_1(sK0,X2)) = k9_relat_1(sK0,X2)) )),
% 0.21/0.54    inference(resolution,[],[f28,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    v1_relat_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) => (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    k9_relat_1(sK0,k3_xboole_0(sK1,sK2)) = k2_relat_1(k7_relat_1(sK0,sK1))),
% 0.21/0.54    inference(superposition,[],[f45,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    k7_relat_1(sK0,sK1) = k7_relat_1(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.54    inference(superposition,[],[f80,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(resolution,[],[f28,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    k7_relat_1(sK0,sK1) = k7_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.21/0.54    inference(resolution,[],[f47,f28])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_relat_1(X1) | k7_relat_1(X1,sK1) = k7_relat_1(k7_relat_1(X1,sK1),sK2)) )),
% 0.21/0.54    inference(resolution,[],[f29,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    r1_tarski(sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f362,plain,(
% 0.21/0.54    k9_relat_1(sK0,sK1) != k9_relat_1(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_11),
% 0.21/0.54    inference(forward_demodulation,[],[f361,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    k9_relat_1(sK0,sK1) != k9_relat_1(sK0,k3_xboole_0(sK2,sK1)) | ~spl3_11),
% 0.21/0.54    inference(superposition,[],[f30,f287])).
% 0.21/0.54  fof(f287,plain,(
% 0.21/0.54    ( ! [X3] : (k9_relat_1(k7_relat_1(sK0,sK2),X3) = k9_relat_1(sK0,k3_xboole_0(sK2,X3))) ) | ~spl3_11),
% 0.21/0.54    inference(forward_demodulation,[],[f286,f45])).
% 0.21/0.54  fof(f286,plain,(
% 0.21/0.54    ( ! [X3] : (k9_relat_1(k7_relat_1(sK0,sK2),X3) = k2_relat_1(k7_relat_1(sK0,k3_xboole_0(sK2,X3)))) ) | ~spl3_11),
% 0.21/0.54    inference(forward_demodulation,[],[f277,f44])).
% 0.21/0.54  fof(f277,plain,(
% 0.21/0.54    ( ! [X3] : (k2_relat_1(k7_relat_1(k7_relat_1(sK0,sK2),X3)) = k9_relat_1(k7_relat_1(sK0,sK2),X3)) ) | ~spl3_11),
% 0.21/0.54    inference(resolution,[],[f262,f34])).
% 0.21/0.54  fof(f262,plain,(
% 0.21/0.54    v1_relat_1(k7_relat_1(sK0,sK2)) | ~spl3_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f261])).
% 0.21/0.54  fof(f261,plain,(
% 0.21/0.54    spl3_11 <=> v1_relat_1(k7_relat_1(sK0,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f273,plain,(
% 0.21/0.54    spl3_11),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f272])).
% 0.21/0.54  fof(f272,plain,(
% 0.21/0.54    $false | spl3_11),
% 0.21/0.54    inference(subsumption_resolution,[],[f271,f28])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    ~v1_relat_1(sK0) | spl3_11),
% 0.21/0.54    inference(resolution,[],[f263,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.54  fof(f263,plain,(
% 0.21/0.54    ~v1_relat_1(k7_relat_1(sK0,sK2)) | spl3_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f261])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (24019)------------------------------
% 0.21/0.54  % (24019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24019)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (24019)Memory used [KB]: 10746
% 0.21/0.54  % (24019)Time elapsed: 0.117 s
% 0.21/0.54  % (24019)------------------------------
% 0.21/0.54  % (24019)------------------------------
% 0.21/0.54  % (24037)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (24039)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (24015)Success in time 0.176 s
%------------------------------------------------------------------------------
