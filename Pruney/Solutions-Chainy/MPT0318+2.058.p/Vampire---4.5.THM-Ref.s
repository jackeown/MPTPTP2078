%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  72 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 163 expanded)
%              Number of equality atoms :   72 ( 126 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f49,f59,f62,f72])).

fof(f72,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl2_3 ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_3 ),
    inference(superposition,[],[f36,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_3
  <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 != k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[],[f24,f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f17,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f62,plain,
    ( spl2_4
    | spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f61,f28,f42,f46])).

fof(f46,plain,
    ( spl2_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f28,plain,
    ( spl2_1
  <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f61,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f60])).

fof(f60,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(superposition,[],[f19,f30])).

fof(f30,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f59,plain,(
    ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f57])).

fof(f57,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_4 ),
    inference(superposition,[],[f13,f48])).

fof(f48,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f49,plain,
    ( spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f40,f32,f46,f42])).

fof(f32,plain,
    ( spl2_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f40,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f37])).

fof(f37,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f19,f34])).

fof(f34,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f35,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f23,f32,f28])).

fof(f23,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(definition_unfolding,[],[f14,f22,f22])).

fof(f14,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:34:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (6853)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (6861)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (6857)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (6857)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f35,f49,f59,f62,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ~spl2_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    $false | ~spl2_3),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~spl2_3),
% 0.21/0.51    inference(superposition,[],[f36,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    spl2_3 <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.51    inference(superposition,[],[f24,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f17,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f16,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl2_4 | spl2_3 | ~spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f61,f28,f42,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    spl2_4 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    spl2_1 <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | ~spl2_1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | ~spl2_1),
% 0.21/0.51    inference(superposition,[],[f19,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f28])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ~spl2_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    $false | ~spl2_4),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~spl2_4),
% 0.21/0.51    inference(superposition,[],[f13,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f46])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    k1_xboole_0 != sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    (k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0)),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    spl2_3 | spl2_4 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f32,f46,f42])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    spl2_2 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_2),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_2),
% 0.21/0.51    inference(superposition,[],[f19,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f32])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    spl2_1 | spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f23,f32,f28])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.51    inference(definition_unfolding,[],[f14,f22,f22])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (6857)------------------------------
% 0.21/0.51  % (6857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6857)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (6857)Memory used [KB]: 6140
% 0.21/0.51  % (6857)Time elapsed: 0.108 s
% 0.21/0.51  % (6857)------------------------------
% 0.21/0.51  % (6857)------------------------------
% 0.21/0.52  % (6844)Success in time 0.164 s
%------------------------------------------------------------------------------
