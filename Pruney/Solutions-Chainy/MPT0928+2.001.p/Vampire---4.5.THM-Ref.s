%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 117 expanded)
%              Number of leaves         :   12 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 362 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f57,f67,f69,f79,f81,f83])).

fof(f83,plain,(
    spl8_6 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl8_6 ),
    inference(resolution,[],[f78,f14])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7))
    & r1_tarski(sK6,sK7)
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
        & r1_tarski(X6,X7)
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7))
      & r1_tarski(sK6,sK7)
      & r1_tarski(sK4,sK5)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
      & r1_tarski(X6,X7)
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
      & r1_tarski(X6,X7)
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( r1_tarski(X6,X7)
          & r1_tarski(X4,X5)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( r1_tarski(X6,X7)
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_mcart_1)).

fof(f78,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl8_6
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f81,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl8_5 ),
    inference(resolution,[],[f74,f15])).

fof(f15,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_5
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f79,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | spl8_4 ),
    inference(avatar_split_clause,[],[f70,f64,f76,f72])).

fof(f64,plain,
    ( spl8_4
  <=> r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f70,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(sK2,sK3)
    | spl8_4 ),
    inference(resolution,[],[f66,f33])).

fof(f33,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_tarski(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f30,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X2),X3)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X0,X2),X3) ) ),
    inference(resolution,[],[f20,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f69,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl8_3 ),
    inference(resolution,[],[f62,f16])).

fof(f16,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,
    ( ~ r1_tarski(sK4,sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl8_3
  <=> r1_tarski(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f67,plain,
    ( ~ spl8_3
    | ~ spl8_4
    | spl8_2 ),
    inference(avatar_split_clause,[],[f58,f52,f64,f60])).

fof(f52,plain,
    ( spl8_2
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f58,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | ~ r1_tarski(sK4,sK5)
    | spl8_2 ),
    inference(resolution,[],[f54,f33])).

fof(f54,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f57,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f50,f17])).

fof(f17,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,
    ( ~ r1_tarski(sK6,sK7)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl8_1
  <=> r1_tarski(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f55,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f42,f52,f48])).

fof(f42,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5))
    | ~ r1_tarski(sK6,sK7) ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),sK6),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5),sK7)) ),
    inference(definition_unfolding,[],[f18,f24,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f23,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f18,plain,(
    ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:54:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (21492)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (21488)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (21505)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (21502)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (21490)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (21493)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (21490)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f55,f57,f67,f69,f79,f81,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl8_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    $false | spl8_6),
% 0.21/0.48    inference(resolution,[],[f78,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ~r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7)) & r1_tarski(sK6,sK7) & r1_tarski(sK4,sK5) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (~r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) & r1_tarski(X6,X7) & r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7)) & r1_tarski(sK6,sK7) & r1_tarski(sK4,sK5) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (~r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) & r1_tarski(X6,X7) & r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (~r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) & (r1_tarski(X6,X7) & r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : ((r1_tarski(X6,X7) & r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((r1_tarski(X6,X7) & r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_mcart_1)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | spl8_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl8_6 <=> r1_tarski(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl8_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    $false | spl8_5),
% 0.21/0.48    inference(resolution,[],[f74,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    r1_tarski(sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ~r1_tarski(sK2,sK3) | spl8_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl8_5 <=> r1_tarski(sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ~spl8_5 | ~spl8_6 | spl8_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f70,f64,f76,f72])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl8_4 <=> r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | ~r1_tarski(sK2,sK3) | spl8_4),
% 0.21/0.48    inference(resolution,[],[f66,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X6,X4,X7,X5] : (r1_tarski(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)) | ~r1_tarski(X4,X5) | ~r1_tarski(X6,X7)) )),
% 0.21/0.48    inference(resolution,[],[f30,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X1,X2),X3) | ~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),X3)) )),
% 0.21/0.48    inference(resolution,[],[f20,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) | spl8_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl8_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    $false | spl8_3),
% 0.21/0.48    inference(resolution,[],[f62,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    r1_tarski(sK4,sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~r1_tarski(sK4,sK5) | spl8_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl8_3 <=> r1_tarski(sK4,sK5)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~spl8_3 | ~spl8_4 | spl8_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f58,f52,f64,f60])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl8_2 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) | ~r1_tarski(sK4,sK5) | spl8_2),
% 0.21/0.48    inference(resolution,[],[f54,f33])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5)) | spl8_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl8_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    $false | spl8_1),
% 0.21/0.48    inference(resolution,[],[f50,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    r1_tarski(sK6,sK7)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ~r1_tarski(sK6,sK7) | spl8_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl8_1 <=> r1_tarski(sK6,sK7)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ~spl8_1 | ~spl8_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f52,f48])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5)) | ~r1_tarski(sK6,sK7)),
% 0.21/0.48    inference(resolution,[],[f33,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),sK6),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5),sK7))),
% 0.21/0.48    inference(definition_unfolding,[],[f18,f24,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f23,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ~r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (21490)------------------------------
% 0.21/0.48  % (21490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21490)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (21490)Memory used [KB]: 6140
% 0.21/0.48  % (21490)Time elapsed: 0.064 s
% 0.21/0.48  % (21490)------------------------------
% 0.21/0.48  % (21490)------------------------------
% 0.21/0.48  % (21487)Success in time 0.12 s
%------------------------------------------------------------------------------
