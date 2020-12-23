%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 145 expanded)
%              Number of leaves         :   10 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  112 ( 244 expanded)
%              Number of equality atoms :   53 ( 162 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f53,f57,f62,f65,f83])).

fof(f83,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f39,f74])).

fof(f74,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f32,f42])).

fof(f42,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_2
  <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f32,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) != X0
      | r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f15,f21,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f12,f20])).

fof(f12,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f39,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl2_1
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f65,plain,
    ( spl2_4
    | spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f64,f59,f41,f50])).

fof(f50,plain,
    ( spl2_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f59,plain,
    ( spl2_5
  <=> r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f64,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | ~ spl2_5 ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | ~ spl2_5 ),
    inference(resolution,[],[f61,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f13,f21,f21,f20,f20])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,
    ( r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f62,plain,
    ( spl2_5
    | spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f22,f50,f41,f59])).

fof(f22,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f11,f21,f21])).

fof(f11,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f57,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f33,f48])).

fof(f48,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_3
  <=> r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f33,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f14,f20])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,
    ( ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f35,f50,f46])).

fof(f35,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(inner_rewriting,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f9,f21])).

fof(f9,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f34,f41,f37])).

fof(f34,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,sK0) ),
    inference(inner_rewriting,[],[f23])).

fof(f23,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f10,f21,f21])).

fof(f10,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:14:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (3878)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (3878)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f44,f53,f57,f62,f65,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl2_1 | ~spl2_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    $false | (spl2_1 | ~spl2_2)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f39,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    r1_tarski(sK0,sK0) | ~spl2_2),
% 0.21/0.48    inference(superposition,[],[f32,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl2_2 <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X1) != X0 | r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f15,f21,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f18,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f12,f20])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK0) | spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl2_1 <=> r1_tarski(sK0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl2_4 | spl2_2 | ~spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f64,f59,f41,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl2_4 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl2_5 <=> r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | ~spl2_5),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | ~spl2_5),
% 0.21/0.48    inference(resolution,[],[f61,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X1,X1,X1,X1) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X2) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f13,f21,f21,f20,f20])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl2_5 | spl2_2 | spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f50,f41,f59])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.48    inference(definition_unfolding,[],[f11,f21,f21])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl2_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    $false | spl2_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f33,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ~r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl2_3 <=> r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f14,f20])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ~spl2_3 | ~spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f50,f46])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | ~r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.48    inference(inner_rewriting,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.48    inference(definition_unfolding,[],[f9,f21])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ~spl2_1 | ~spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f41,f37])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,sK0)),
% 0.21/0.48    inference(inner_rewriting,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.48    inference(definition_unfolding,[],[f10,f21,f21])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (3878)------------------------------
% 0.21/0.48  % (3878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3878)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (3878)Memory used [KB]: 6140
% 0.21/0.48  % (3878)Time elapsed: 0.085 s
% 0.21/0.48  % (3878)------------------------------
% 0.21/0.48  % (3878)------------------------------
% 0.21/0.48  % (3873)Success in time 0.118 s
%------------------------------------------------------------------------------
