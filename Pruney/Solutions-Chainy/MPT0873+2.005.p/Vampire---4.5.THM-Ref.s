%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  97 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :  107 ( 212 expanded)
%              Number of equality atoms :   67 ( 153 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f46,f48,f62,f64,f83,f84])).

fof(f84,plain,
    ( spl8_2
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f82,f59,f22])).

fof(f22,plain,
    ( spl8_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f59,plain,
    ( spl8_8
  <=> k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f82,plain,
    ( sK1 = sK5
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f78,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f78,plain,
    ( sK5 = k2_mcart_1(k4_tarski(sK0,sK1))
    | ~ spl8_8 ),
    inference(superposition,[],[f12,f61])).

fof(f61,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f83,plain,
    ( spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f79,f59,f18])).

fof(f18,plain,
    ( spl8_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f79,plain,
    ( sK0 = sK4
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f77,f11])).

fof(f11,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f77,plain,
    ( sK4 = k1_mcart_1(k4_tarski(sK0,sK1))
    | ~ spl8_8 ),
    inference(superposition,[],[f11,f61])).

fof(f64,plain,
    ( spl8_3
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f63,f43,f26])).

fof(f26,plain,
    ( spl8_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f43,plain,
    ( spl8_6
  <=> k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f63,plain,
    ( sK2 = sK6
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f56,f12])).

fof(f56,plain,
    ( sK6 = k2_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | ~ spl8_6 ),
    inference(superposition,[],[f12,f45])).

fof(f45,plain,
    ( k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK4,sK5),sK6)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f62,plain,
    ( spl8_8
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f57,f43,f59])).

fof(f57,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f55,f11])).

fof(f55,plain,
    ( k4_tarski(sK4,sK5) = k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | ~ spl8_6 ),
    inference(superposition,[],[f11,f45])).

fof(f48,plain,
    ( spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f47,f35,f30])).

fof(f30,plain,
    ( spl8_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f35,plain,
    ( spl8_5
  <=> k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f47,plain,
    ( sK3 = sK7
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f40,f12])).

fof(f40,plain,
    ( sK7 = k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))
    | ~ spl8_5 ),
    inference(superposition,[],[f12,f37])).

fof(f37,plain,
    ( k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f35])).

fof(f46,plain,
    ( spl8_6
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f41,f35,f43])).

fof(f41,plain,
    ( k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK4,sK5),sK6)
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f39,f11])).

fof(f39,plain,
    ( k4_tarski(k4_tarski(sK4,sK5),sK6) = k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3))
    | ~ spl8_5 ),
    inference(superposition,[],[f11,f37])).

fof(f38,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f9,f15,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f14,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f9,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f33,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f10,f30,f26,f22,f18])).

fof(f10,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n010.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:02:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (12242)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (12249)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (12242)Refutation not found, incomplete strategy% (12242)------------------------------
% 0.21/0.52  % (12242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12242)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12242)Memory used [KB]: 6140
% 0.21/0.52  % (12242)Time elapsed: 0.104 s
% 0.21/0.52  % (12242)------------------------------
% 0.21/0.52  % (12242)------------------------------
% 0.21/0.52  % (12247)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (12257)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (12249)Refutation not found, incomplete strategy% (12249)------------------------------
% 0.21/0.52  % (12249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12249)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12249)Memory used [KB]: 10618
% 0.21/0.52  % (12249)Time elapsed: 0.119 s
% 0.21/0.52  % (12249)------------------------------
% 0.21/0.52  % (12249)------------------------------
% 0.21/0.53  % (12239)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (12238)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (12263)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (12238)Refutation not found, incomplete strategy% (12238)------------------------------
% 0.21/0.53  % (12238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12238)Memory used [KB]: 1663
% 0.21/0.53  % (12238)Time elapsed: 0.111 s
% 0.21/0.53  % (12238)------------------------------
% 0.21/0.53  % (12238)------------------------------
% 0.21/0.53  % (12263)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f33,f38,f46,f48,f62,f64,f83,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    spl8_2 | ~spl8_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f82,f59,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    spl8_2 <=> sK1 = sK5),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    spl8_8 <=> k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    sK1 = sK5 | ~spl8_8),
% 0.21/0.53    inference(forward_demodulation,[],[f78,f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    sK5 = k2_mcart_1(k4_tarski(sK0,sK1)) | ~spl8_8),
% 0.21/0.53    inference(superposition,[],[f12,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5) | ~spl8_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f59])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl8_1 | ~spl8_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f79,f59,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    spl8_1 <=> sK0 = sK4),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    sK0 = sK4 | ~spl8_8),
% 0.21/0.53    inference(forward_demodulation,[],[f77,f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    sK4 = k1_mcart_1(k4_tarski(sK0,sK1)) | ~spl8_8),
% 0.21/0.53    inference(superposition,[],[f11,f61])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    spl8_3 | ~spl8_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f63,f43,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    spl8_3 <=> sK2 = sK6),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    spl8_6 <=> k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK4,sK5),sK6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    sK2 = sK6 | ~spl8_6),
% 0.21/0.53    inference(forward_demodulation,[],[f56,f12])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    sK6 = k2_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) | ~spl8_6),
% 0.21/0.53    inference(superposition,[],[f12,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK4,sK5),sK6) | ~spl8_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f43])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    spl8_8 | ~spl8_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f57,f43,f59])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    k4_tarski(sK0,sK1) = k4_tarski(sK4,sK5) | ~spl8_6),
% 0.21/0.53    inference(forward_demodulation,[],[f55,f11])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    k4_tarski(sK4,sK5) = k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) | ~spl8_6),
% 0.21/0.53    inference(superposition,[],[f11,f45])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    spl8_4 | ~spl8_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f47,f35,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    spl8_4 <=> sK3 = sK7),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    spl8_5 <=> k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    sK3 = sK7 | ~spl8_5),
% 0.21/0.53    inference(forward_demodulation,[],[f40,f12])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    sK7 = k2_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) | ~spl8_5),
% 0.21/0.53    inference(superposition,[],[f12,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7) | ~spl8_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f35])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    spl8_6 | ~spl8_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f35,f43])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK4,sK5),sK6) | ~spl8_5),
% 0.21/0.53    inference(forward_demodulation,[],[f39,f11])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    k4_tarski(k4_tarski(sK4,sK5),sK6) = k1_mcart_1(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)) | ~spl8_5),
% 0.21/0.53    inference(superposition,[],[f11,f37])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    spl8_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f16,f35])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) = k4_tarski(k4_tarski(k4_tarski(sK4,sK5),sK6),sK7)),
% 0.21/0.53    inference(definition_unfolding,[],[f9,f15,f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f14,f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f7])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f6,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.21/0.53    inference(negated_conjecture,[],[f4])).
% 0.21/0.53  fof(f4,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f10,f30,f26,f22,f18])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (12263)------------------------------
% 0.21/0.53  % (12263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12263)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (12263)Memory used [KB]: 6268
% 0.21/0.53  % (12263)Time elapsed: 0.117 s
% 0.21/0.53  % (12263)------------------------------
% 0.21/0.53  % (12263)------------------------------
% 0.21/0.53  % (12237)Success in time 0.167 s
%------------------------------------------------------------------------------
