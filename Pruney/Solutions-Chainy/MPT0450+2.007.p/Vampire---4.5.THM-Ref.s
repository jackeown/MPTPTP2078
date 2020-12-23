%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:18 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 106 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  166 ( 262 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f920,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f114,f133,f344,f635,f919])).

fof(f919,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f918])).

fof(f918,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f634,f891])).

fof(f891,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f428,f228,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f228,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(unit_resulting_resolution,[],[f91,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f91,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f428,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f159,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f71,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f159,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f101,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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

fof(f634,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f632])).

fof(f632,plain,
    ( spl3_10
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f635,plain,
    ( ~ spl3_10
    | ~ spl3_1
    | ~ spl3_2
    | spl3_7 ),
    inference(avatar_split_clause,[],[f371,f341,f111,f106,f632])).

fof(f106,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f111,plain,
    ( spl3_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f341,plain,
    ( spl3_7
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f371,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f113,f126,f343,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f343,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f341])).

fof(f126,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f108,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f108,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f113,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f344,plain,
    ( ~ spl3_7
    | ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f265,f130,f106,f341])).

fof(f130,plain,
    ( spl3_3
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f265,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f252,f262])).

fof(f262,plain,
    ( ! [X0] : r1_tarski(k3_relat_1(k3_xboole_0(sK0,X0)),k3_relat_1(sK0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f108,f126,f72,f68])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f252,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))
    | spl3_3 ),
    inference(resolution,[],[f98,f132])).

fof(f132,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f133,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f64,f130])).

fof(f64,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(f114,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f63,f111])).

fof(f63,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f109,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f62,f106])).

fof(f62,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:39:45 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.50  % (22557)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.50  % (22568)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.51  % (22570)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.51  % (22580)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.51  % (22572)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.51  % (22567)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.52  % (22564)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.52  % (22578)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.52  % (22559)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.52  % (22558)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.52  % (22560)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.53  % (22563)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.53  % (22576)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.53  % (22562)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.54  % (22566)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.54  % (22561)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.54  % (22575)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.54  % (22573)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.54  % (22571)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.55  % (22579)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.55  % (22577)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.55  % (22563)Refutation not found, incomplete strategy% (22563)------------------------------
% 0.23/0.55  % (22563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (22563)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (22563)Memory used [KB]: 10618
% 0.23/0.55  % (22563)Time elapsed: 0.108 s
% 0.23/0.55  % (22563)------------------------------
% 0.23/0.55  % (22563)------------------------------
% 0.23/0.55  % (22582)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.55  % (22580)Refutation found. Thanks to Tanya!
% 0.23/0.55  % SZS status Theorem for theBenchmark
% 0.23/0.55  % SZS output start Proof for theBenchmark
% 0.23/0.55  fof(f920,plain,(
% 0.23/0.55    $false),
% 0.23/0.55    inference(avatar_sat_refutation,[],[f109,f114,f133,f344,f635,f919])).
% 0.23/0.55  fof(f919,plain,(
% 0.23/0.55    spl3_10),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f918])).
% 0.23/0.55  fof(f918,plain,(
% 0.23/0.55    $false | spl3_10),
% 0.23/0.55    inference(subsumption_resolution,[],[f634,f891])).
% 0.23/0.55  fof(f891,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f428,f228,f99])).
% 0.23/0.55  fof(f99,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | r1_tarski(X0,X1) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f48])).
% 0.23/0.55  fof(f48,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.23/0.55    inference(flattening,[],[f47])).
% 0.23/0.55  fof(f47,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.23/0.55    inference(ennf_transformation,[],[f13])).
% 0.23/0.55  fof(f13,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.23/0.55  fof(f228,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f91,f96])).
% 0.23/0.55  fof(f96,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f42])).
% 0.23/0.55  fof(f42,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.23/0.55    inference(ennf_transformation,[],[f5])).
% 0.23/0.55  fof(f5,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.23/0.55  fof(f91,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f9])).
% 0.23/0.55  fof(f9,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.23/0.55  fof(f428,plain,(
% 0.23/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.55    inference(superposition,[],[f159,f116])).
% 0.23/0.55  fof(f116,plain,(
% 0.23/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f71,f70])).
% 0.23/0.55  fof(f70,plain,(
% 0.23/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f34])).
% 0.23/0.55  fof(f34,plain,(
% 0.23/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.23/0.55    inference(ennf_transformation,[],[f12])).
% 0.23/0.55  fof(f12,axiom,(
% 0.23/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.23/0.55  fof(f71,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f10])).
% 0.23/0.55  fof(f10,axiom,(
% 0.23/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.23/0.55  fof(f159,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f101,f92])).
% 0.23/0.55  fof(f92,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f39])).
% 0.23/0.55  fof(f39,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.23/0.55    inference(ennf_transformation,[],[f14])).
% 0.23/0.55  fof(f14,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.23/0.55  fof(f101,plain,(
% 0.23/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.55    inference(equality_resolution,[],[f79])).
% 0.23/0.55  fof(f79,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.55    inference(cnf_transformation,[],[f54])).
% 0.23/0.55  fof(f54,plain,(
% 0.23/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.55    inference(flattening,[],[f53])).
% 0.23/0.55  fof(f53,plain,(
% 0.23/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.55    inference(nnf_transformation,[],[f1])).
% 0.23/0.55  fof(f1,axiom,(
% 0.23/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.55  fof(f634,plain,(
% 0.23/0.55    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | spl3_10),
% 0.23/0.55    inference(avatar_component_clause,[],[f632])).
% 0.23/0.55  fof(f632,plain,(
% 0.23/0.55    spl3_10 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK1)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.23/0.55  fof(f635,plain,(
% 0.23/0.55    ~spl3_10 | ~spl3_1 | ~spl3_2 | spl3_7),
% 0.23/0.55    inference(avatar_split_clause,[],[f371,f341,f111,f106,f632])).
% 0.23/0.55  fof(f106,plain,(
% 0.23/0.55    spl3_1 <=> v1_relat_1(sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.55  fof(f111,plain,(
% 0.23/0.55    spl3_2 <=> v1_relat_1(sK1)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.55  fof(f341,plain,(
% 0.23/0.55    spl3_7 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.23/0.55  fof(f371,plain,(
% 0.23/0.55    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | (~spl3_1 | ~spl3_2 | spl3_7)),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f113,f126,f343,f68])).
% 0.23/0.55  fof(f68,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f32])).
% 0.23/0.55  fof(f32,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(flattening,[],[f31])).
% 0.23/0.55  fof(f31,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f25])).
% 0.23/0.55  fof(f25,axiom,(
% 0.23/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 0.23/0.55  fof(f343,plain,(
% 0.23/0.55    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) | spl3_7),
% 0.23/0.55    inference(avatar_component_clause,[],[f341])).
% 0.23/0.55  fof(f126,plain,(
% 0.23/0.55    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) ) | ~spl3_1),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f108,f74])).
% 0.23/0.55  fof(f74,plain,(
% 0.23/0.55    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f36])).
% 0.23/0.55  fof(f36,plain,(
% 0.23/0.55    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f21])).
% 0.23/0.55  fof(f21,axiom,(
% 0.23/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.23/0.55  fof(f108,plain,(
% 0.23/0.55    v1_relat_1(sK0) | ~spl3_1),
% 0.23/0.55    inference(avatar_component_clause,[],[f106])).
% 0.23/0.55  fof(f113,plain,(
% 0.23/0.55    v1_relat_1(sK1) | ~spl3_2),
% 0.23/0.55    inference(avatar_component_clause,[],[f111])).
% 0.23/0.55  fof(f344,plain,(
% 0.23/0.55    ~spl3_7 | ~spl3_1 | spl3_3),
% 0.23/0.55    inference(avatar_split_clause,[],[f265,f130,f106,f341])).
% 0.23/0.55  fof(f130,plain,(
% 0.23/0.55    spl3_3 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.55  fof(f265,plain,(
% 0.23/0.55    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) | (~spl3_1 | spl3_3)),
% 0.23/0.55    inference(subsumption_resolution,[],[f252,f262])).
% 0.23/0.55  fof(f262,plain,(
% 0.23/0.55    ( ! [X0] : (r1_tarski(k3_relat_1(k3_xboole_0(sK0,X0)),k3_relat_1(sK0))) ) | ~spl3_1),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f108,f126,f72,f68])).
% 0.23/0.55  fof(f72,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f6])).
% 0.23/0.55  fof(f6,axiom,(
% 0.23/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.23/0.55  fof(f252,plain,(
% 0.23/0.55    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) | spl3_3),
% 0.23/0.55    inference(resolution,[],[f98,f132])).
% 0.23/0.55  fof(f132,plain,(
% 0.23/0.55    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) | spl3_3),
% 0.23/0.55    inference(avatar_component_clause,[],[f130])).
% 0.23/0.55  fof(f98,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f46])).
% 0.23/0.55  fof(f46,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.55    inference(flattening,[],[f45])).
% 0.23/0.55  fof(f45,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.55    inference(ennf_transformation,[],[f7])).
% 0.23/0.55  fof(f7,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.23/0.55  fof(f133,plain,(
% 0.23/0.55    ~spl3_3),
% 0.23/0.55    inference(avatar_split_clause,[],[f64,f130])).
% 0.23/0.55  fof(f64,plain,(
% 0.23/0.55    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.23/0.55    inference(cnf_transformation,[],[f51])).
% 0.23/0.55  fof(f51,plain,(
% 0.23/0.55    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f50,f49])).
% 0.23/0.55  fof(f49,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f50,plain,(
% 0.23/0.55    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f28,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f27])).
% 0.23/0.55  fof(f27,negated_conjecture,(
% 0.23/0.55    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.23/0.55    inference(negated_conjecture,[],[f26])).
% 0.23/0.55  fof(f26,conjecture,(
% 0.23/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).
% 0.23/0.55  fof(f114,plain,(
% 0.23/0.55    spl3_2),
% 0.23/0.55    inference(avatar_split_clause,[],[f63,f111])).
% 0.23/0.55  fof(f63,plain,(
% 0.23/0.55    v1_relat_1(sK1)),
% 0.23/0.55    inference(cnf_transformation,[],[f51])).
% 0.23/0.55  fof(f109,plain,(
% 0.23/0.55    spl3_1),
% 0.23/0.55    inference(avatar_split_clause,[],[f62,f106])).
% 0.23/0.55  fof(f62,plain,(
% 0.23/0.55    v1_relat_1(sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f51])).
% 0.23/0.55  % SZS output end Proof for theBenchmark
% 0.23/0.55  % (22580)------------------------------
% 0.23/0.55  % (22580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (22580)Termination reason: Refutation
% 0.23/0.55  
% 0.23/0.55  % (22580)Memory used [KB]: 11257
% 0.23/0.55  % (22580)Time elapsed: 0.074 s
% 0.23/0.55  % (22580)------------------------------
% 0.23/0.55  % (22580)------------------------------
% 0.23/0.56  % (22565)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.56  % (22556)Success in time 0.184 s
%------------------------------------------------------------------------------
