%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:54 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 115 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 ( 250 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f451,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f153,f156,f264,f267,f450])).

fof(f450,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f442,f32])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f442,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl2_3 ),
    inference(resolution,[],[f441,f32])).

fof(f441,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(X0,sK1) )
    | spl2_3 ),
    inference(superposition,[],[f437,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f437,plain,
    ( ! [X5] : ~ r1_tarski(k2_xboole_0(sK1,X5),sK1)
    | spl2_3 ),
    inference(resolution,[],[f179,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X1),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl2_3 ),
    inference(resolution,[],[f166,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK0,sK1),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl2_3 ),
    inference(superposition,[],[f164,f24])).

fof(f164,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X0),sK1)
    | spl2_3 ),
    inference(resolution,[],[f148,f29])).

fof(f148,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl2_3
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f267,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f263,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f263,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl2_5
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f264,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_2 ),
    inference(avatar_split_clause,[],[f222,f104,f150,f261])).

fof(f150,plain,
    ( spl2_4
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f104,plain,
    ( spl2_2
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f222,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl2_2 ),
    inference(resolution,[],[f175,f106])).

fof(f106,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f175,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(sK0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(superposition,[],[f157,f24])).

fof(f157,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(k2_xboole_0(X0,sK0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f74,f32])).

fof(f74,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k2_xboole_0(X1,sK0)),X2)
      | r1_tarski(k1_relat_1(X1),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f29,f37])).

fof(f37,plain,(
    ! [X1] :
      ( k1_relat_1(k2_xboole_0(X1,sK0)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK0))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f156,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f152,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0)) ),
    inference(resolution,[],[f20,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f152,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f150])).

fof(f153,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f120,f100,f150,f146])).

fof(f100,plain,
    ( spl2_1
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f120,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl2_1 ),
    inference(resolution,[],[f98,f102])).

fof(f102,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f98,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(sK1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(superposition,[],[f87,f24])).

fof(f87,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(k2_xboole_0(X0,sK1)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f66,f32])).

fof(f66,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k2_xboole_0(X1,sK1)),X2)
      | r1_tarski(k1_relat_1(X1),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f29,f34])).

fof(f34,plain,(
    ! [X1] :
      ( k1_relat_1(k2_xboole_0(X1,sK1)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f18,f21])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f107,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f54,f104,f100])).

fof(f54,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) ),
    inference(resolution,[],[f19,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f19,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:59:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (21675)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.49  % (21683)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (21679)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (21677)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (21695)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (21678)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (21694)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (21687)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (21690)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (21682)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (21680)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (21686)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (21698)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (21685)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (21689)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (21676)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (21693)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (21697)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.39/0.54  % (21699)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.39/0.54  % (21681)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.39/0.54  % (21696)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.39/0.54  % (21695)Refutation found. Thanks to Tanya!
% 1.39/0.54  % SZS status Theorem for theBenchmark
% 1.39/0.54  % (21684)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.39/0.55  % (21688)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.39/0.55  % (21700)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.39/0.55  % (21692)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.39/0.55  % (21691)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.54/0.56  % SZS output start Proof for theBenchmark
% 1.54/0.56  fof(f451,plain,(
% 1.54/0.56    $false),
% 1.54/0.56    inference(avatar_sat_refutation,[],[f107,f153,f156,f264,f267,f450])).
% 1.54/0.56  fof(f450,plain,(
% 1.54/0.56    spl2_3),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f446])).
% 1.54/0.56  fof(f446,plain,(
% 1.54/0.56    $false | spl2_3),
% 1.54/0.56    inference(resolution,[],[f442,f32])).
% 1.54/0.56  fof(f32,plain,(
% 1.54/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.54/0.56    inference(equality_resolution,[],[f25])).
% 1.54/0.56  fof(f25,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.54/0.56    inference(cnf_transformation,[],[f1])).
% 1.54/0.56  fof(f1,axiom,(
% 1.54/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.54/0.56  fof(f442,plain,(
% 1.54/0.56    ~r1_tarski(sK1,sK1) | spl2_3),
% 1.54/0.56    inference(resolution,[],[f441,f32])).
% 1.54/0.56  fof(f441,plain,(
% 1.54/0.56    ( ! [X0] : (~r1_tarski(sK1,X0) | ~r1_tarski(X0,sK1)) ) | spl2_3),
% 1.54/0.56    inference(superposition,[],[f437,f24])).
% 1.54/0.56  fof(f24,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.54/0.56    inference(cnf_transformation,[],[f14])).
% 1.54/0.56  fof(f14,plain,(
% 1.54/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f3])).
% 1.54/0.56  fof(f3,axiom,(
% 1.54/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.54/0.56  fof(f437,plain,(
% 1.54/0.56    ( ! [X5] : (~r1_tarski(k2_xboole_0(sK1,X5),sK1)) ) | spl2_3),
% 1.54/0.56    inference(resolution,[],[f179,f28])).
% 1.54/0.56  fof(f28,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f6])).
% 1.54/0.56  fof(f6,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 1.54/0.56  fof(f179,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X1),X0) | ~r1_tarski(X0,sK1)) ) | spl2_3),
% 1.54/0.56    inference(resolution,[],[f166,f29])).
% 1.54/0.56  fof(f29,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f15])).
% 1.54/0.56  fof(f15,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.54/0.56    inference(ennf_transformation,[],[f2])).
% 1.54/0.56  fof(f2,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.54/0.56  fof(f166,plain,(
% 1.54/0.56    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK1),X0) | ~r1_tarski(X0,sK1)) ) | spl2_3),
% 1.54/0.56    inference(superposition,[],[f164,f24])).
% 1.54/0.56  fof(f164,plain,(
% 1.54/0.56    ( ! [X0] : (~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X0),sK1)) ) | spl2_3),
% 1.54/0.56    inference(resolution,[],[f148,f29])).
% 1.54/0.56  fof(f148,plain,(
% 1.54/0.56    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | spl2_3),
% 1.54/0.56    inference(avatar_component_clause,[],[f146])).
% 1.54/0.56  fof(f146,plain,(
% 1.54/0.56    spl2_3 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK1)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.54/0.56  fof(f267,plain,(
% 1.54/0.56    spl2_5),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f265])).
% 1.54/0.56  fof(f265,plain,(
% 1.54/0.56    $false | spl2_5),
% 1.54/0.56    inference(resolution,[],[f263,f22])).
% 1.54/0.56  fof(f22,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f4])).
% 1.54/0.56  fof(f4,axiom,(
% 1.54/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.54/0.56  fof(f263,plain,(
% 1.54/0.56    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | spl2_5),
% 1.54/0.56    inference(avatar_component_clause,[],[f261])).
% 1.54/0.56  fof(f261,plain,(
% 1.54/0.56    spl2_5 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.54/0.56  fof(f264,plain,(
% 1.54/0.56    ~spl2_5 | ~spl2_4 | spl2_2),
% 1.54/0.56    inference(avatar_split_clause,[],[f222,f104,f150,f261])).
% 1.54/0.56  fof(f150,plain,(
% 1.54/0.56    spl2_4 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.54/0.56  fof(f104,plain,(
% 1.54/0.56    spl2_2 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.54/0.56  fof(f222,plain,(
% 1.54/0.56    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | spl2_2),
% 1.54/0.56    inference(resolution,[],[f175,f106])).
% 1.54/0.56  fof(f106,plain,(
% 1.54/0.56    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) | spl2_2),
% 1.54/0.56    inference(avatar_component_clause,[],[f104])).
% 1.54/0.56  fof(f175,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(sK0)) | ~v1_relat_1(X0) | ~r1_tarski(X0,sK0)) )),
% 1.54/0.56    inference(superposition,[],[f157,f24])).
% 1.54/0.56  fof(f157,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(k2_xboole_0(X0,sK0))) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(resolution,[],[f74,f32])).
% 1.54/0.56  fof(f74,plain,(
% 1.54/0.56    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k2_xboole_0(X1,sK0)),X2) | r1_tarski(k1_relat_1(X1),X2) | ~v1_relat_1(X1)) )),
% 1.54/0.56    inference(superposition,[],[f29,f37])).
% 1.54/0.56  fof(f37,plain,(
% 1.54/0.56    ( ! [X1] : (k1_relat_1(k2_xboole_0(X1,sK0)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK0)) | ~v1_relat_1(X1)) )),
% 1.54/0.56    inference(resolution,[],[f20,f21])).
% 1.54/0.56  fof(f21,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f12])).
% 1.54/0.56  fof(f12,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f8])).
% 1.54/0.56  fof(f8,axiom,(
% 1.54/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).
% 1.54/0.56  fof(f20,plain,(
% 1.54/0.56    v1_relat_1(sK0)),
% 1.54/0.56    inference(cnf_transformation,[],[f11])).
% 1.54/0.56  fof(f11,plain,(
% 1.54/0.56    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f10])).
% 1.54/0.56  fof(f10,negated_conjecture,(
% 1.54/0.56    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 1.54/0.56    inference(negated_conjecture,[],[f9])).
% 1.54/0.56  fof(f9,conjecture,(
% 1.54/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).
% 1.54/0.56  fof(f156,plain,(
% 1.54/0.56    spl2_4),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f154])).
% 1.54/0.56  fof(f154,plain,(
% 1.54/0.56    $false | spl2_4),
% 1.54/0.56    inference(resolution,[],[f152,f36])).
% 1.54/0.56  fof(f36,plain,(
% 1.54/0.56    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) )),
% 1.54/0.56    inference(resolution,[],[f20,f23])).
% 1.54/0.56  fof(f23,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f13])).
% 1.54/0.56  fof(f13,plain,(
% 1.54/0.56    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f7])).
% 1.54/0.56  fof(f7,axiom,(
% 1.54/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.54/0.56  fof(f152,plain,(
% 1.54/0.56    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_4),
% 1.54/0.56    inference(avatar_component_clause,[],[f150])).
% 1.54/0.56  fof(f153,plain,(
% 1.54/0.56    ~spl2_3 | ~spl2_4 | spl2_1),
% 1.54/0.56    inference(avatar_split_clause,[],[f120,f100,f150,f146])).
% 1.54/0.56  fof(f100,plain,(
% 1.54/0.56    spl2_1 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.54/0.56  fof(f120,plain,(
% 1.54/0.56    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | spl2_1),
% 1.54/0.56    inference(resolution,[],[f98,f102])).
% 1.54/0.56  fof(f102,plain,(
% 1.54/0.56    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) | spl2_1),
% 1.54/0.56    inference(avatar_component_clause,[],[f100])).
% 1.54/0.56  fof(f98,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(sK1)) | ~v1_relat_1(X0) | ~r1_tarski(X0,sK1)) )),
% 1.54/0.56    inference(superposition,[],[f87,f24])).
% 1.54/0.56  fof(f87,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(k2_xboole_0(X0,sK1))) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(resolution,[],[f66,f32])).
% 1.54/0.56  fof(f66,plain,(
% 1.54/0.56    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k2_xboole_0(X1,sK1)),X2) | r1_tarski(k1_relat_1(X1),X2) | ~v1_relat_1(X1)) )),
% 1.54/0.56    inference(superposition,[],[f29,f34])).
% 1.54/0.56  fof(f34,plain,(
% 1.54/0.56    ( ! [X1] : (k1_relat_1(k2_xboole_0(X1,sK1)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK1)) | ~v1_relat_1(X1)) )),
% 1.54/0.56    inference(resolution,[],[f18,f21])).
% 1.54/0.56  fof(f18,plain,(
% 1.54/0.56    v1_relat_1(sK1)),
% 1.54/0.56    inference(cnf_transformation,[],[f11])).
% 1.54/0.56  fof(f107,plain,(
% 1.54/0.56    ~spl2_1 | ~spl2_2),
% 1.54/0.56    inference(avatar_split_clause,[],[f54,f104,f100])).
% 1.54/0.56  fof(f54,plain,(
% 1.54/0.56    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))),
% 1.54/0.56    inference(resolution,[],[f19,f30])).
% 1.54/0.56  fof(f30,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f17])).
% 1.54/0.56  fof(f17,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.54/0.56    inference(flattening,[],[f16])).
% 1.54/0.56  fof(f16,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.54/0.56    inference(ennf_transformation,[],[f5])).
% 1.54/0.56  fof(f5,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.54/0.56  fof(f19,plain,(
% 1.54/0.56    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 1.54/0.56    inference(cnf_transformation,[],[f11])).
% 1.54/0.56  % SZS output end Proof for theBenchmark
% 1.54/0.56  % (21695)------------------------------
% 1.54/0.56  % (21695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (21695)Termination reason: Refutation
% 1.54/0.56  
% 1.54/0.56  % (21695)Memory used [KB]: 11001
% 1.54/0.56  % (21695)Time elapsed: 0.116 s
% 1.54/0.56  % (21695)------------------------------
% 1.54/0.56  % (21695)------------------------------
% 1.54/0.56  % (21674)Success in time 0.194 s
%------------------------------------------------------------------------------
