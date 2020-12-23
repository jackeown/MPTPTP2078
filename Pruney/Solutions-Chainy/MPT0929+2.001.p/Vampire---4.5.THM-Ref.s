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
% DateTime   : Thu Dec  3 12:59:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  77 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  109 ( 153 expanded)
%              Number of equality atoms :   64 (  96 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f41,f46,f53,f58,f65,f70,f77,f82])).

fof(f82,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f17,f76])).

fof(f76,plain,
    ( sK4 != k2_mcart_1(k4_tarski(sK3,sK4))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_8
  <=> sK4 = k2_mcart_1(k4_tarski(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f17,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f77,plain,
    ( ~ spl6_8
    | spl6_4 ),
    inference(avatar_split_clause,[],[f71,f32,f74])).

fof(f32,plain,
    ( spl6_4
  <=> sK4 = k2_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f71,plain,
    ( sK4 != k2_mcart_1(k4_tarski(sK3,sK4))
    | spl6_4 ),
    inference(forward_demodulation,[],[f34,f17])).

fof(f34,plain,
    ( sK4 != k2_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f32])).

fof(f70,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f16,f64])).

fof(f64,plain,
    ( sK3 != k1_mcart_1(k4_tarski(sK3,sK4))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_7
  <=> sK3 = k1_mcart_1(k4_tarski(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f16,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f65,plain,
    ( ~ spl6_7
    | spl6_3 ),
    inference(avatar_split_clause,[],[f59,f28,f62])).

fof(f28,plain,
    ( spl6_3
  <=> sK3 = k1_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f59,plain,
    ( sK3 != k1_mcart_1(k4_tarski(sK3,sK4))
    | spl6_3 ),
    inference(forward_demodulation,[],[f30,f17])).

fof(f30,plain,
    ( sK3 != k1_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f58,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f17,f52])).

fof(f52,plain,
    ( sK1 != k2_mcart_1(k4_tarski(sK0,sK1))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl6_6
  <=> sK1 = k2_mcart_1(k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f53,plain,
    ( ~ spl6_6
    | spl6_2 ),
    inference(avatar_split_clause,[],[f47,f24,f50])).

fof(f24,plain,
    ( spl6_2
  <=> sK1 = k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f47,plain,
    ( sK1 != k2_mcart_1(k4_tarski(sK0,sK1))
    | spl6_2 ),
    inference(forward_demodulation,[],[f26,f16])).

fof(f26,plain,
    ( sK1 != k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f46,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f42])).

fof(f42,plain,
    ( $false
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f16,f40])).

fof(f40,plain,
    ( sK0 != k1_mcart_1(k4_tarski(sK0,sK1))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl6_5
  <=> sK0 = k1_mcart_1(k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f41,plain,
    ( ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f36,f20,f38])).

fof(f20,plain,
    ( spl6_1
  <=> sK0 = k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f36,plain,
    ( sK0 != k1_mcart_1(k4_tarski(sK0,sK1))
    | spl6_1 ),
    inference(forward_demodulation,[],[f22,f16])).

fof(f22,plain,
    ( sK0 != k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f35,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f18,f32,f28,f24,f20])).

fof(f18,plain,
    ( sK4 != k2_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))))
    | sK3 != k1_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))))
    | sK1 != k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))
    | sK0 != k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) ),
    inference(definition_unfolding,[],[f11,f15,f14,f13,f12])).

fof(f12,plain,(
    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_mcart_1)).

fof(f13,plain,(
    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_mcart_1)).

fof(f14,plain,(
    ! [X0] : k19_mcart_1(X0) = k1_mcart_1(k2_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k19_mcart_1(X0) = k1_mcart_1(k2_mcart_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_mcart_1)).

fof(f15,plain,(
    ! [X0] : k20_mcart_1(X0) = k2_mcart_1(k2_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k20_mcart_1(X0) = k2_mcart_1(k2_mcart_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_mcart_1)).

fof(f11,plain,
    ( sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK3 != k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK3 != k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4
        | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3
        | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1
        | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0 )
   => ( sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
      | sK3 != k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
      | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
      | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4
      | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3
      | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1
      | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4
        & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3
        & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1
        & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4
      & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3
      & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1
      & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:25:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (5649)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.42  % (5649)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f35,f41,f46,f53,f58,f65,f70,f77,f82])).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    spl6_8),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f78])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    $false | spl6_8),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f17,f76])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    sK4 != k2_mcart_1(k4_tarski(sK3,sK4)) | spl6_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f74])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    spl6_8 <=> sK4 = k2_mcart_1(k4_tarski(sK3,sK4))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    ~spl6_8 | spl6_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f71,f32,f74])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    spl6_4 <=> sK4 = k2_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    sK4 != k2_mcart_1(k4_tarski(sK3,sK4)) | spl6_4),
% 0.20/0.42    inference(forward_demodulation,[],[f34,f17])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    sK4 != k2_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))) | spl6_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f32])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    spl6_7),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f66])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    $false | spl6_7),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f16,f64])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    sK3 != k1_mcart_1(k4_tarski(sK3,sK4)) | spl6_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f62])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    spl6_7 <=> sK3 = k1_mcart_1(k4_tarski(sK3,sK4))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    ~spl6_7 | spl6_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f59,f28,f62])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    spl6_3 <=> sK3 = k1_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    sK3 != k1_mcart_1(k4_tarski(sK3,sK4)) | spl6_3),
% 0.20/0.42    inference(forward_demodulation,[],[f30,f17])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    sK3 != k1_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))) | spl6_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f28])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    spl6_6),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f54])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    $false | spl6_6),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f17,f52])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    sK1 != k2_mcart_1(k4_tarski(sK0,sK1)) | spl6_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f50])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    spl6_6 <=> sK1 = k2_mcart_1(k4_tarski(sK0,sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    ~spl6_6 | spl6_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f47,f24,f50])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    spl6_2 <=> sK1 = k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    sK1 != k2_mcart_1(k4_tarski(sK0,sK1)) | spl6_2),
% 0.20/0.42    inference(forward_demodulation,[],[f26,f16])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    sK1 != k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) | spl6_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f24])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    spl6_5),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    $false | spl6_5),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f16,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    sK0 != k1_mcart_1(k4_tarski(sK0,sK1)) | spl6_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f38])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl6_5 <=> sK0 = k1_mcart_1(k4_tarski(sK0,sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ~spl6_5 | spl6_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f36,f20,f38])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    spl6_1 <=> sK0 = k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    sK0 != k1_mcart_1(k4_tarski(sK0,sK1)) | spl6_1),
% 0.20/0.42    inference(forward_demodulation,[],[f22,f16])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    sK0 != k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) | spl6_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f20])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f18,f32,f28,f24,f20])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    sK4 != k2_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))) | sK3 != k1_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))) | sK1 != k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) | sK0 != k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))),
% 0.20/0.42    inference(definition_unfolding,[],[f11,f15,f14,f13,f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ( ! [X0] : (k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_mcart_1)).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ( ! [X0] : (k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_mcart_1)).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ( ! [X0] : (k19_mcart_1(X0) = k1_mcart_1(k2_mcart_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : k19_mcart_1(X0) = k1_mcart_1(k2_mcart_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_mcart_1)).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ( ! [X0] : (k20_mcart_1(X0) = k2_mcart_1(k2_mcart_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : k20_mcart_1(X0) = k2_mcart_1(k2_mcart_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_mcart_1)).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))) | sK3 != k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))) | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))) | sK3 != k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))) | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3,X4,X5] : (k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4 | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3 | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1 | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0) => (sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))) | sK3 != k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))) | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3,X4,X5] : (k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4 | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3 | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1 | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0)),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2,X3,X4,X5] : (k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4 & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3 & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1 & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0)),
% 0.20/0.42    inference(negated_conjecture,[],[f6])).
% 0.20/0.42  fof(f6,conjecture,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4,X5] : (k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4 & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3 & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1 & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_mcart_1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (5649)------------------------------
% 0.20/0.42  % (5649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (5649)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (5649)Memory used [KB]: 10618
% 0.20/0.42  % (5649)Time elapsed: 0.005 s
% 0.20/0.42  % (5649)------------------------------
% 0.20/0.42  % (5649)------------------------------
% 0.20/0.42  % (5631)Success in time 0.062 s
%------------------------------------------------------------------------------
