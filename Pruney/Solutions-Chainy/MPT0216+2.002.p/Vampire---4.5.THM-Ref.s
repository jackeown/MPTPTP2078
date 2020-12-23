%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:13 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   35 (  58 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   73 ( 126 expanded)
%              Number of equality atoms :   41 (  79 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (5732)Refutation not found, incomplete strategy% (5732)------------------------------
% (5732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5731)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (5715)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (5721)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f61,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f22,f29,f43,f48,f60])).

fof(f60,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f42,f47,f24])).

fof(f24,plain,(
    ! [X2,X3,X1] :
      ( k2_tarski(X2,X1) != k1_tarski(X3)
      | X1 = X3 ) ),
    inference(superposition,[],[f12,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_tarski(X1,X2)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(f47,plain,
    ( k1_tarski(sK0) = k2_tarski(sK0,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_6
  <=> k1_tarski(sK0) = k2_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f42,plain,
    ( sK0 != sK2
    | spl3_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_5
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f48,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f32,f27,f19,f45])).

fof(f19,plain,
    ( spl3_2
  <=> k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f27,plain,
    ( spl3_3
  <=> ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f32,plain,
    ( k1_tarski(sK0) = k2_tarski(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f21,f30])).

fof(f30,plain,
    ( sK0 = sK1
    | ~ spl3_3 ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | sK1 = X0 )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f21,plain,
    ( k1_tarski(sK0) = k2_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f43,plain,
    ( ~ spl3_5
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f33,f27,f14,f40])).

fof(f14,plain,
    ( spl3_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f33,plain,
    ( sK0 != sK2
    | spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f16,f30])).

fof(f16,plain,
    ( sK1 != sK2
    | spl3_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f29,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f23,f19,f27])).

fof(f23,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | sK1 = X0 )
    | ~ spl3_2 ),
    inference(superposition,[],[f12,f21])).

fof(f22,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f9,f19])).

fof(f9,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( sK1 != sK2
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).

% (5736)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( X1 != X2
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK1 != sK2
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( X1 != X2
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f17,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f10,f14])).

fof(f10,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:53:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.48  % (5714)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.48  % (5719)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.48  % (5732)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.48  % (5714)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.49  % (5737)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  % (5732)Refutation not found, incomplete strategy% (5732)------------------------------
% 0.23/0.49  % (5732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (5731)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.50  % (5715)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.50  % (5721)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.50  fof(f61,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(avatar_sat_refutation,[],[f17,f22,f29,f43,f48,f60])).
% 0.23/0.50  fof(f60,plain,(
% 0.23/0.50    spl3_5 | ~spl3_6),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f56])).
% 0.23/0.50  fof(f56,plain,(
% 0.23/0.50    $false | (spl3_5 | ~spl3_6)),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f42,f47,f24])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    ( ! [X2,X3,X1] : (k2_tarski(X2,X1) != k1_tarski(X3) | X1 = X3) )),
% 0.23/0.50    inference(superposition,[],[f12,f11])).
% 0.23/0.50  fof(f11,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f1])).
% 0.23/0.50  fof(f1,axiom,(
% 0.23/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.23/0.50  fof(f12,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_tarski(X1,X2) | X0 = X1) )),
% 0.23/0.50    inference(cnf_transformation,[],[f6])).
% 0.23/0.50  fof(f6,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (X0 = X1 | k1_tarski(X0) != k2_tarski(X1,X2))),
% 0.23/0.50    inference(ennf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).
% 0.23/0.50  fof(f47,plain,(
% 0.23/0.50    k1_tarski(sK0) = k2_tarski(sK0,sK2) | ~spl3_6),
% 0.23/0.50    inference(avatar_component_clause,[],[f45])).
% 0.23/0.50  fof(f45,plain,(
% 0.23/0.50    spl3_6 <=> k1_tarski(sK0) = k2_tarski(sK0,sK2)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.23/0.50  fof(f42,plain,(
% 0.23/0.50    sK0 != sK2 | spl3_5),
% 0.23/0.50    inference(avatar_component_clause,[],[f40])).
% 0.23/0.50  fof(f40,plain,(
% 0.23/0.50    spl3_5 <=> sK0 = sK2),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.50  fof(f48,plain,(
% 0.23/0.50    spl3_6 | ~spl3_2 | ~spl3_3),
% 0.23/0.50    inference(avatar_split_clause,[],[f32,f27,f19,f45])).
% 0.23/0.50  fof(f19,plain,(
% 0.23/0.50    spl3_2 <=> k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.50  fof(f27,plain,(
% 0.23/0.50    spl3_3 <=> ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | sK1 = X0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    k1_tarski(sK0) = k2_tarski(sK0,sK2) | (~spl3_2 | ~spl3_3)),
% 0.23/0.50    inference(backward_demodulation,[],[f21,f30])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    sK0 = sK1 | ~spl3_3),
% 0.23/0.50    inference(equality_resolution,[],[f28])).
% 0.23/0.50  fof(f28,plain,(
% 0.23/0.50    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | sK1 = X0) ) | ~spl3_3),
% 0.23/0.50    inference(avatar_component_clause,[],[f27])).
% 0.23/0.50  fof(f21,plain,(
% 0.23/0.50    k1_tarski(sK0) = k2_tarski(sK1,sK2) | ~spl3_2),
% 0.23/0.50    inference(avatar_component_clause,[],[f19])).
% 0.23/0.50  fof(f43,plain,(
% 0.23/0.50    ~spl3_5 | spl3_1 | ~spl3_3),
% 0.23/0.50    inference(avatar_split_clause,[],[f33,f27,f14,f40])).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    spl3_1 <=> sK1 = sK2),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    sK0 != sK2 | (spl3_1 | ~spl3_3)),
% 0.23/0.50    inference(backward_demodulation,[],[f16,f30])).
% 0.23/0.50  fof(f16,plain,(
% 0.23/0.50    sK1 != sK2 | spl3_1),
% 0.23/0.50    inference(avatar_component_clause,[],[f14])).
% 0.23/0.50  fof(f29,plain,(
% 0.23/0.50    spl3_3 | ~spl3_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f23,f19,f27])).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | sK1 = X0) ) | ~spl3_2),
% 0.23/0.50    inference(superposition,[],[f12,f21])).
% 0.23/0.50  fof(f22,plain,(
% 0.23/0.50    spl3_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f9,f19])).
% 0.23/0.50  fof(f9,plain,(
% 0.23/0.50    k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.23/0.50    inference(cnf_transformation,[],[f8])).
% 0.23/0.50  fof(f8,plain,(
% 0.23/0.50    sK1 != sK2 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).
% 0.23/0.50  % (5736)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.50  fof(f7,plain,(
% 0.23/0.50    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK1 != sK2 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f5,plain,(
% 0.23/0.50    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 0.23/0.50    inference(ennf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,negated_conjecture,(
% 0.23/0.50    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.23/0.50    inference(negated_conjecture,[],[f3])).
% 0.23/0.50  fof(f3,conjecture,(
% 0.23/0.50    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).
% 0.23/0.50  fof(f17,plain,(
% 0.23/0.50    ~spl3_1),
% 0.23/0.50    inference(avatar_split_clause,[],[f10,f14])).
% 0.23/0.50  fof(f10,plain,(
% 0.23/0.50    sK1 != sK2),
% 0.23/0.50    inference(cnf_transformation,[],[f8])).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (5714)------------------------------
% 0.23/0.50  % (5714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (5714)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (5714)Memory used [KB]: 6140
% 0.23/0.50  % (5714)Time elapsed: 0.075 s
% 0.23/0.50  % (5714)------------------------------
% 0.23/0.50  % (5714)------------------------------
% 0.23/0.50  % (5726)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.50  % (5711)Success in time 0.127 s
%------------------------------------------------------------------------------
