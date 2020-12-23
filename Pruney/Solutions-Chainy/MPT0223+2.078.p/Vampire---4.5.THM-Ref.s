%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:01 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 160 expanded)
%              Number of equality atoms :   56 (  83 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f55,f81,f104])).

fof(f104,plain,
    ( ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f40,f88])).

fof(f88,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_tarski(sK0,sK0))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f87,f54])).

fof(f54,plain,
    ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_2
  <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f87,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))))
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f80,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f14])).

% (7112)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f80,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_5
  <=> r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f40,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f28,f22])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

% (7086)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f81,plain,
    ( spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f63,f43,f78])).

fof(f43,plain,
    ( spl4_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f63,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f45,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f26,f22,f22])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

% (7092)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f45,plain,
    ( sK0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f55,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f31,f52])).

fof(f31,plain,(
    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) ),
    inference(definition_unfolding,[],[f20,f22,f23,f22,f22])).

fof(f20,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f46,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.17/0.52  % (7083)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.17/0.52  % (7105)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.17/0.52  % (7085)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.53  % (7107)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.32/0.53  % (7087)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.32/0.53  % (7098)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.32/0.53  % (7105)Refutation found. Thanks to Tanya!
% 1.32/0.53  % SZS status Theorem for theBenchmark
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  fof(f105,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(avatar_sat_refutation,[],[f46,f55,f81,f104])).
% 1.32/0.53  fof(f104,plain,(
% 1.32/0.53    ~spl4_2 | ~spl4_5),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f100])).
% 1.32/0.53  fof(f100,plain,(
% 1.32/0.53    $false | (~spl4_2 | ~spl4_5)),
% 1.32/0.53    inference(unit_resulting_resolution,[],[f40,f88])).
% 1.32/0.53  fof(f88,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK0,sK0))) ) | (~spl4_2 | ~spl4_5)),
% 1.32/0.53    inference(forward_demodulation,[],[f87,f54])).
% 1.32/0.53  fof(f54,plain,(
% 1.32/0.53    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) | ~spl4_2),
% 1.32/0.53    inference(avatar_component_clause,[],[f52])).
% 1.32/0.53  fof(f52,plain,(
% 1.32/0.53    spl4_2 <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)))),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.32/0.53  fof(f87,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))))) ) | ~spl4_5),
% 1.32/0.53    inference(unit_resulting_resolution,[],[f80,f32])).
% 1.32/0.53  fof(f32,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f25,f23])).
% 1.32/0.53  fof(f23,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f2])).
% 1.32/0.53  fof(f2,axiom,(
% 1.32/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.32/0.53  fof(f25,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f15])).
% 1.32/0.53  fof(f15,plain,(
% 1.32/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f14])).
% 1.32/0.53  % (7112)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.53  fof(f14,plain,(
% 1.32/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f10,plain,(
% 1.32/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(ennf_transformation,[],[f8])).
% 1.32/0.53  fof(f8,plain,(
% 1.32/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(rectify,[],[f1])).
% 1.32/0.53  fof(f1,axiom,(
% 1.32/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.32/0.53  fof(f80,plain,(
% 1.32/0.53    r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) | ~spl4_5),
% 1.32/0.53    inference(avatar_component_clause,[],[f78])).
% 1.32/0.53  fof(f78,plain,(
% 1.32/0.53    spl4_5 <=> r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.32/0.53  fof(f40,plain,(
% 1.32/0.53    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 1.32/0.53    inference(equality_resolution,[],[f39])).
% 1.32/0.53  fof(f39,plain,(
% 1.32/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 1.32/0.53    inference(equality_resolution,[],[f37])).
% 1.32/0.53  fof(f37,plain,(
% 1.32/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 1.32/0.53    inference(definition_unfolding,[],[f28,f22])).
% 1.32/0.53  fof(f22,plain,(
% 1.32/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f4])).
% 1.32/0.53  fof(f4,axiom,(
% 1.32/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.53  fof(f28,plain,(
% 1.32/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.32/0.53    inference(cnf_transformation,[],[f19])).
% 1.32/0.53  % (7086)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.32/0.53  fof(f19,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 1.32/0.53  fof(f18,plain,(
% 1.32/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f17,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.53    inference(rectify,[],[f16])).
% 1.32/0.53  fof(f16,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.32/0.53    inference(nnf_transformation,[],[f3])).
% 1.32/0.53  fof(f3,axiom,(
% 1.32/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.32/0.53  fof(f81,plain,(
% 1.32/0.53    spl4_5 | spl4_1),
% 1.32/0.53    inference(avatar_split_clause,[],[f63,f43,f78])).
% 1.32/0.53  fof(f43,plain,(
% 1.32/0.53    spl4_1 <=> sK0 = sK1),
% 1.32/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.32/0.53  fof(f63,plain,(
% 1.32/0.53    r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) | spl4_1),
% 1.32/0.53    inference(unit_resulting_resolution,[],[f45,f34])).
% 1.32/0.53  fof(f34,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) | X0 = X1) )),
% 1.32/0.53    inference(definition_unfolding,[],[f26,f22,f22])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.32/0.53    inference(cnf_transformation,[],[f11])).
% 1.32/0.53  fof(f11,plain,(
% 1.32/0.53    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.32/0.53    inference(ennf_transformation,[],[f5])).
% 1.32/0.53  fof(f5,axiom,(
% 1.32/0.53    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 1.32/0.53  % (7092)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.32/0.53  fof(f45,plain,(
% 1.32/0.53    sK0 != sK1 | spl4_1),
% 1.32/0.53    inference(avatar_component_clause,[],[f43])).
% 1.32/0.53  fof(f55,plain,(
% 1.32/0.53    spl4_2),
% 1.32/0.53    inference(avatar_split_clause,[],[f31,f52])).
% 1.32/0.53  fof(f31,plain,(
% 1.32/0.53    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)))),
% 1.32/0.53    inference(definition_unfolding,[],[f20,f22,f23,f22,f22])).
% 1.32/0.53  fof(f20,plain,(
% 1.32/0.53    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.32/0.53    inference(cnf_transformation,[],[f13])).
% 1.32/0.53  fof(f13,plain,(
% 1.32/0.53    sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).
% 1.32/0.53  fof(f12,plain,(
% 1.32/0.53    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f9,plain,(
% 1.32/0.53    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.32/0.53    inference(ennf_transformation,[],[f7])).
% 1.32/0.53  fof(f7,negated_conjecture,(
% 1.32/0.53    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.32/0.53    inference(negated_conjecture,[],[f6])).
% 1.32/0.53  fof(f6,conjecture,(
% 1.32/0.53    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 1.32/0.53  fof(f46,plain,(
% 1.32/0.53    ~spl4_1),
% 1.32/0.53    inference(avatar_split_clause,[],[f21,f43])).
% 1.32/0.53  fof(f21,plain,(
% 1.32/0.53    sK0 != sK1),
% 1.32/0.53    inference(cnf_transformation,[],[f13])).
% 1.32/0.53  % SZS output end Proof for theBenchmark
% 1.32/0.53  % (7105)------------------------------
% 1.32/0.53  % (7105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (7105)Termination reason: Refutation
% 1.32/0.53  
% 1.32/0.53  % (7105)Memory used [KB]: 10746
% 1.32/0.53  % (7105)Time elapsed: 0.126 s
% 1.32/0.53  % (7105)------------------------------
% 1.32/0.53  % (7105)------------------------------
% 1.32/0.53  % (7089)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.53  % (7077)Success in time 0.174 s
%------------------------------------------------------------------------------
