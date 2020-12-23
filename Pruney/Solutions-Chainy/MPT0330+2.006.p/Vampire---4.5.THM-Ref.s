%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:00 EST 2020

% Result     : Theorem 2.80s
% Output     : Refutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 152 expanded)
%              Number of leaves         :   14 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :  115 ( 254 expanded)
%              Number of equality atoms :   14 (  84 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1477,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f823,f826,f1473])).

fof(f1473,plain,
    ( ~ spl6_2
    | spl6_16 ),
    inference(avatar_contradiction_clause,[],[f1428])).

fof(f1428,plain,
    ( $false
    | ~ spl6_2
    | spl6_16 ),
    inference(unit_resulting_resolution,[],[f54,f822,f154,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f154,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) ),
    inference(superposition,[],[f91,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f33,f37,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f91,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f34,f36,f36])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f822,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f820])).

fof(f820,plain,
    ( spl6_16
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f54,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl6_2
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f826,plain,
    ( ~ spl6_1
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f824])).

fof(f824,plain,
    ( $false
    | ~ spl6_1
    | spl6_15 ),
    inference(unit_resulting_resolution,[],[f49,f137,f818,f28])).

fof(f818,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f816])).

fof(f816,plain,
    ( spl6_15
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f137,plain,(
    ! [X12,X10,X11] : r1_tarski(k2_zfmisc_1(X10,X11),k2_zfmisc_1(X10,k3_tarski(k1_enumset1(X11,X11,X12)))) ),
    inference(superposition,[],[f40,f41])).

fof(f49,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl6_1
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f823,plain,
    ( ~ spl6_15
    | ~ spl6_16
    | spl6_3 ),
    inference(avatar_split_clause,[],[f790,f57,f820,f816])).

fof(f57,plain,
    ( spl6_3
  <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f790,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | spl6_3 ),
    inference(resolution,[],[f166,f59])).

fof(f59,plain,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f166,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r1_tarski(k3_tarski(k1_enumset1(X8,X8,X9)),k2_zfmisc_1(k3_tarski(k1_enumset1(X5,X5,X7)),X6))
      | ~ r1_tarski(X9,k2_zfmisc_1(X7,X6))
      | ~ r1_tarski(X8,k2_zfmisc_1(X5,X6)) ) ),
    inference(superposition,[],[f39,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f32,f37,f37])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f37,f37])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f60,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f38,f57])).

fof(f38,plain,(
    ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f25,f37,f37,f37])).

fof(f25,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f55,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:49 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.46  % (25449)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.48  % (25465)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (25441)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (25442)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (25438)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (25439)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (25440)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (25459)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (25463)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (25437)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (25451)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (25445)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (25446)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (25464)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (25455)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (25444)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (25458)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (25447)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (25456)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (25443)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (25453)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (25462)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (25450)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (25460)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (25461)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (25457)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (25448)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (25454)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (25466)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.59/0.57  % (25452)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.22/0.67  % (25440)Refutation not found, incomplete strategy% (25440)------------------------------
% 2.22/0.67  % (25440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.67  % (25440)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.67  
% 2.22/0.67  % (25440)Memory used [KB]: 6140
% 2.22/0.67  % (25440)Time elapsed: 0.265 s
% 2.22/0.67  % (25440)------------------------------
% 2.22/0.67  % (25440)------------------------------
% 2.80/0.76  % (25460)Refutation found. Thanks to Tanya!
% 2.80/0.76  % SZS status Theorem for theBenchmark
% 2.80/0.76  % SZS output start Proof for theBenchmark
% 2.80/0.76  fof(f1477,plain,(
% 2.80/0.76    $false),
% 2.80/0.76    inference(avatar_sat_refutation,[],[f50,f55,f60,f823,f826,f1473])).
% 2.80/0.76  fof(f1473,plain,(
% 2.80/0.76    ~spl6_2 | spl6_16),
% 2.80/0.76    inference(avatar_contradiction_clause,[],[f1428])).
% 2.80/0.76  fof(f1428,plain,(
% 2.80/0.76    $false | (~spl6_2 | spl6_16)),
% 2.80/0.76    inference(unit_resulting_resolution,[],[f54,f822,f154,f28])).
% 2.80/0.76  fof(f28,plain,(
% 2.80/0.76    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.80/0.76    inference(cnf_transformation,[],[f18])).
% 2.80/0.76  fof(f18,plain,(
% 2.80/0.76    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.80/0.76    inference(flattening,[],[f17])).
% 2.80/0.76  fof(f17,plain,(
% 2.80/0.76    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.80/0.76    inference(ennf_transformation,[],[f3])).
% 2.80/0.76  fof(f3,axiom,(
% 2.80/0.76    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.80/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.80/0.76  fof(f154,plain,(
% 2.80/0.76    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))))) )),
% 2.80/0.76    inference(superposition,[],[f91,f41])).
% 2.80/0.76  fof(f41,plain,(
% 2.80/0.76    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 2.80/0.76    inference(definition_unfolding,[],[f33,f37,f37])).
% 2.80/0.76  fof(f37,plain,(
% 2.80/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.80/0.76    inference(definition_unfolding,[],[f35,f36])).
% 2.80/0.76  fof(f36,plain,(
% 2.80/0.76    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.80/0.76    inference(cnf_transformation,[],[f8])).
% 2.80/0.76  fof(f8,axiom,(
% 2.80/0.76    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.80/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.80/0.76  fof(f35,plain,(
% 2.80/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.80/0.76    inference(cnf_transformation,[],[f9])).
% 2.80/0.76  fof(f9,axiom,(
% 2.80/0.76    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.80/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.80/0.76  fof(f33,plain,(
% 2.80/0.76    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.80/0.76    inference(cnf_transformation,[],[f10])).
% 2.80/0.76  fof(f10,axiom,(
% 2.80/0.76    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.80/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 2.80/0.76  fof(f91,plain,(
% 2.80/0.76    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) )),
% 2.80/0.76    inference(superposition,[],[f40,f43])).
% 2.80/0.76  fof(f43,plain,(
% 2.80/0.76    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.80/0.76    inference(definition_unfolding,[],[f34,f36,f36])).
% 2.80/0.76  fof(f34,plain,(
% 2.80/0.76    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.80/0.76    inference(cnf_transformation,[],[f7])).
% 2.80/0.76  fof(f7,axiom,(
% 2.80/0.76    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.80/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.80/0.76  fof(f40,plain,(
% 2.80/0.76    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.80/0.76    inference(definition_unfolding,[],[f27,f37])).
% 2.80/0.76  fof(f27,plain,(
% 2.80/0.76    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.80/0.76    inference(cnf_transformation,[],[f6])).
% 2.80/0.76  fof(f6,axiom,(
% 2.80/0.76    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.80/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.80/0.76  fof(f822,plain,(
% 2.80/0.76    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | spl6_16),
% 2.80/0.76    inference(avatar_component_clause,[],[f820])).
% 2.80/0.76  fof(f820,plain,(
% 2.80/0.76    spl6_16 <=> r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 2.80/0.76    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.80/0.76  fof(f54,plain,(
% 2.80/0.76    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | ~spl6_2),
% 2.80/0.76    inference(avatar_component_clause,[],[f52])).
% 2.80/0.76  fof(f52,plain,(
% 2.80/0.76    spl6_2 <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 2.80/0.76    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.80/0.76  fof(f826,plain,(
% 2.80/0.76    ~spl6_1 | spl6_15),
% 2.80/0.76    inference(avatar_contradiction_clause,[],[f824])).
% 2.80/0.76  fof(f824,plain,(
% 2.80/0.76    $false | (~spl6_1 | spl6_15)),
% 2.80/0.76    inference(unit_resulting_resolution,[],[f49,f137,f818,f28])).
% 2.80/0.76  fof(f818,plain,(
% 2.80/0.76    ~r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | spl6_15),
% 2.80/0.76    inference(avatar_component_clause,[],[f816])).
% 2.80/0.76  fof(f816,plain,(
% 2.80/0.76    spl6_15 <=> r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 2.80/0.76    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.80/0.76  fof(f137,plain,(
% 2.80/0.76    ( ! [X12,X10,X11] : (r1_tarski(k2_zfmisc_1(X10,X11),k2_zfmisc_1(X10,k3_tarski(k1_enumset1(X11,X11,X12))))) )),
% 2.80/0.76    inference(superposition,[],[f40,f41])).
% 2.80/0.76  fof(f49,plain,(
% 2.80/0.76    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) | ~spl6_1),
% 2.80/0.76    inference(avatar_component_clause,[],[f47])).
% 2.80/0.76  fof(f47,plain,(
% 2.80/0.76    spl6_1 <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 2.80/0.76    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.80/0.76  fof(f823,plain,(
% 2.80/0.76    ~spl6_15 | ~spl6_16 | spl6_3),
% 2.80/0.76    inference(avatar_split_clause,[],[f790,f57,f820,f816])).
% 2.80/0.76  fof(f57,plain,(
% 2.80/0.76    spl6_3 <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 2.80/0.76    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.80/0.76  fof(f790,plain,(
% 2.80/0.76    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | ~r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | spl6_3),
% 2.80/0.76    inference(resolution,[],[f166,f59])).
% 2.80/0.76  fof(f59,plain,(
% 2.80/0.76    ~r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) | spl6_3),
% 2.80/0.76    inference(avatar_component_clause,[],[f57])).
% 2.80/0.76  fof(f166,plain,(
% 2.80/0.76    ( ! [X6,X8,X7,X5,X9] : (r1_tarski(k3_tarski(k1_enumset1(X8,X8,X9)),k2_zfmisc_1(k3_tarski(k1_enumset1(X5,X5,X7)),X6)) | ~r1_tarski(X9,k2_zfmisc_1(X7,X6)) | ~r1_tarski(X8,k2_zfmisc_1(X5,X6))) )),
% 2.80/0.76    inference(superposition,[],[f39,f42])).
% 2.80/0.76  fof(f42,plain,(
% 2.80/0.76    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 2.80/0.76    inference(definition_unfolding,[],[f32,f37,f37])).
% 2.80/0.76  fof(f32,plain,(
% 2.80/0.76    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.80/0.76    inference(cnf_transformation,[],[f10])).
% 2.80/0.76  fof(f39,plain,(
% 2.80/0.76    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.80/0.76    inference(definition_unfolding,[],[f26,f37,f37])).
% 2.80/0.76  fof(f26,plain,(
% 2.80/0.76    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.80/0.76    inference(cnf_transformation,[],[f16])).
% 2.80/0.76  fof(f16,plain,(
% 2.80/0.76    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 2.80/0.76    inference(flattening,[],[f15])).
% 2.80/0.76  fof(f15,plain,(
% 2.80/0.76    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 2.80/0.76    inference(ennf_transformation,[],[f2])).
% 2.80/0.76  fof(f2,axiom,(
% 2.80/0.76    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 2.80/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
% 2.80/0.76  fof(f60,plain,(
% 2.80/0.76    ~spl6_3),
% 2.80/0.76    inference(avatar_split_clause,[],[f38,f57])).
% 2.80/0.76  fof(f38,plain,(
% 2.80/0.76    ~r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 2.80/0.76    inference(definition_unfolding,[],[f25,f37,f37,f37])).
% 2.80/0.76  fof(f25,plain,(
% 2.80/0.76    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 2.80/0.76    inference(cnf_transformation,[],[f20])).
% 2.80/0.76  fof(f20,plain,(
% 2.80/0.76    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 2.80/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f19])).
% 2.80/0.76  fof(f19,plain,(
% 2.80/0.76    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 2.80/0.76    introduced(choice_axiom,[])).
% 2.80/0.76  fof(f14,plain,(
% 2.80/0.76    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 2.80/0.76    inference(flattening,[],[f13])).
% 2.80/0.76  fof(f13,plain,(
% 2.80/0.76    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 2.80/0.76    inference(ennf_transformation,[],[f12])).
% 2.80/0.76  fof(f12,negated_conjecture,(
% 2.80/0.76    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 2.80/0.76    inference(negated_conjecture,[],[f11])).
% 2.80/0.76  fof(f11,conjecture,(
% 2.80/0.76    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 2.80/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 2.80/0.76  fof(f55,plain,(
% 2.80/0.76    spl6_2),
% 2.80/0.76    inference(avatar_split_clause,[],[f24,f52])).
% 2.80/0.76  fof(f24,plain,(
% 2.80/0.76    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 2.80/0.76    inference(cnf_transformation,[],[f20])).
% 2.80/0.76  fof(f50,plain,(
% 2.80/0.76    spl6_1),
% 2.80/0.76    inference(avatar_split_clause,[],[f23,f47])).
% 2.80/0.76  fof(f23,plain,(
% 2.80/0.76    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 2.80/0.76    inference(cnf_transformation,[],[f20])).
% 2.80/0.76  % SZS output end Proof for theBenchmark
% 2.80/0.76  % (25460)------------------------------
% 2.80/0.76  % (25460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.80/0.76  % (25460)Termination reason: Refutation
% 2.80/0.76  
% 2.80/0.76  % (25460)Memory used [KB]: 12537
% 2.80/0.76  % (25460)Time elapsed: 0.335 s
% 2.80/0.76  % (25460)------------------------------
% 2.80/0.76  % (25460)------------------------------
% 2.80/0.76  % (25436)Success in time 0.407 s
%------------------------------------------------------------------------------
