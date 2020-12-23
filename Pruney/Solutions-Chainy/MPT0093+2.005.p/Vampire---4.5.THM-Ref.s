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
% DateTime   : Thu Dec  3 12:31:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 (  87 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :  111 ( 188 expanded)
%              Number of equality atoms :   32 (  47 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f46,f64,f75,f90,f103])).

fof(f103,plain,
    ( spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(global_subsumption,[],[f74,f91])).

fof(f91,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f63,f89])).

fof(f89,plain,
    ( ! [X2] : k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k4_xboole_0(X2,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_8
  <=> ! [X2] : k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k4_xboole_0(X2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f63,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f74,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_7
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f90,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f85,f43,f88])).

fof(f43,plain,
    ( spl3_4
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f85,plain,
    ( ! [X2] : k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k4_xboole_0(X2,sK2))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f81,f84])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f80,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f24,f17])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f23,f18])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f81,plain,
    ( ! [X2] : k4_xboole_0(sK0,k4_xboole_0(X2,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X2),k4_xboole_0(sK0,sK0))
    | ~ spl3_4 ),
    inference(superposition,[],[f24,f45])).

fof(f45,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f75,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f65,f26,f72])).

fof(f26,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f65,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f28,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f28,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f64,plain,
    ( ~ spl3_6
    | spl3_3 ),
    inference(avatar_split_clause,[],[f52,f36,f61])).

fof(f36,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f52,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f38,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f46,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f40,f31,f43])).

fof(f31,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f40,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f33,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f33,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f39,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f34,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (20343)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.42  % (20343)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f104,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f29,f34,f39,f46,f64,f75,f90,f103])).
% 0.19/0.42  fof(f103,plain,(
% 0.19/0.42    spl3_6 | ~spl3_7 | ~spl3_8),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f102])).
% 0.19/0.42  fof(f102,plain,(
% 0.19/0.42    $false | (spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.19/0.42    inference(global_subsumption,[],[f74,f91])).
% 0.19/0.42  fof(f91,plain,(
% 0.19/0.42    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (spl3_6 | ~spl3_8)),
% 0.19/0.42    inference(superposition,[],[f63,f89])).
% 0.19/0.42  fof(f89,plain,(
% 0.19/0.42    ( ! [X2] : (k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k4_xboole_0(X2,sK2))) ) | ~spl3_8),
% 0.19/0.42    inference(avatar_component_clause,[],[f88])).
% 0.19/0.42  fof(f88,plain,(
% 0.19/0.42    spl3_8 <=> ! [X2] : k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k4_xboole_0(X2,sK2))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.42  fof(f63,plain,(
% 0.19/0.42    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_6),
% 0.19/0.42    inference(avatar_component_clause,[],[f61])).
% 0.19/0.42  fof(f61,plain,(
% 0.19/0.42    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.42  fof(f74,plain,(
% 0.19/0.42    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_7),
% 0.19/0.42    inference(avatar_component_clause,[],[f72])).
% 0.19/0.42  fof(f72,plain,(
% 0.19/0.42    spl3_7 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.42  fof(f90,plain,(
% 0.19/0.42    spl3_8 | ~spl3_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f85,f43,f88])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    spl3_4 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.42  fof(f85,plain,(
% 0.19/0.42    ( ! [X2] : (k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k4_xboole_0(X2,sK2))) ) | ~spl3_4),
% 0.19/0.42    inference(forward_demodulation,[],[f81,f84])).
% 0.19/0.42  fof(f84,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))) )),
% 0.19/0.42    inference(forward_demodulation,[],[f80,f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.42  fof(f80,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))) )),
% 0.19/0.42    inference(superposition,[],[f24,f17])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f23,f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.19/0.42  fof(f81,plain,(
% 0.19/0.42    ( ! [X2] : (k4_xboole_0(sK0,k4_xboole_0(X2,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X2),k4_xboole_0(sK0,sK0))) ) | ~spl3_4),
% 0.19/0.42    inference(superposition,[],[f24,f45])).
% 0.19/0.42  fof(f45,plain,(
% 0.19/0.42    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f43])).
% 0.19/0.42  fof(f75,plain,(
% 0.19/0.42    spl3_7 | ~spl3_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f65,f26,f72])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.42  fof(f65,plain,(
% 0.19/0.42    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_1),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f28,f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.19/0.42    inference(nnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f26])).
% 0.19/0.42  fof(f64,plain,(
% 0.19/0.42    ~spl3_6 | spl3_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f52,f36,f61])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    spl3_3 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.42  fof(f52,plain,(
% 0.19/0.42    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_3),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f38,f21])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | spl3_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f36])).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    spl3_4 | ~spl3_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f40,f31,f43])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.42  fof(f40,plain,(
% 0.19/0.42    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f33,f19])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f12])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(nnf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f31])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    ~spl3_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f16,f36])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => (~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1))),
% 0.19/0.42    inference(flattening,[],[f8])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.19/0.42    inference(ennf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.19/0.42    inference(negated_conjecture,[],[f6])).
% 0.19/0.42  fof(f6,conjecture,(
% 0.19/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    spl3_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f15,f31])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    r1_xboole_0(sK0,sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    spl3_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f14,f26])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    r1_tarski(sK0,sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (20343)------------------------------
% 0.19/0.42  % (20343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (20343)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (20343)Memory used [KB]: 10618
% 0.19/0.42  % (20343)Time elapsed: 0.006 s
% 0.19/0.42  % (20343)------------------------------
% 0.19/0.42  % (20343)------------------------------
% 0.19/0.42  % (20325)Success in time 0.072 s
%------------------------------------------------------------------------------
