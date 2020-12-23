%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 141 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 ( 347 expanded)
%              Number of equality atoms :   28 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f143,f175,f268,f292,f349])).

fof(f349,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl5_1
    | spl5_4 ),
    inference(resolution,[],[f295,f65])).

fof(f65,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f295,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl5_4 ),
    inference(resolution,[],[f146,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f146,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl5_4
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f292,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl5_9 ),
    inference(resolution,[],[f272,f32])).

fof(f32,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f272,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl5_9 ),
    inference(trivial_inequality_removal,[],[f269])).

fof(f269,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK2,sK1)
    | spl5_9 ),
    inference(superposition,[],[f267,f58])).

fof(f58,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k3_xboole_0(X3,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f43,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f267,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl5_9
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f268,plain,
    ( ~ spl5_4
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f260,f265,f145])).

fof(f260,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f107,f56])).

fof(f56,plain,(
    ~ r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))) ),
    inference(resolution,[],[f52,f42])).

fof(f52,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

% (10235)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f12,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f107,plain,(
    ! [X10,X11,X9] :
      ( r1_xboole_0(X9,k3_tarski(k2_enumset1(X10,X10,X10,X11)))
      | k1_xboole_0 != k3_xboole_0(X9,X11)
      | ~ r1_xboole_0(X9,X10) ) ),
    inference(superposition,[],[f44,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f50])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f175,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl5_3 ),
    inference(resolution,[],[f168,f32])).

fof(f168,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f153,f42])).

fof(f153,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f142,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f40,f31])).

fof(f31,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f142,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f143,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f133,f140,f64])).

fof(f133,plain,
    ( r2_hidden(sK3,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f131,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f131,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_xboole_0(sK0,sK1),X0)
      | r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f94,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X0)
      | r1_xboole_0(k3_xboole_0(sK0,sK1),X0) ) ),
    inference(resolution,[],[f48,f53])).

fof(f53,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f30,f51])).

fof(f30,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:39:36 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.44  % (10249)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.45  % (10241)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.46  % (10234)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (10239)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (10238)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (10237)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (10240)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (10238)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f350,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f143,f175,f268,f292,f349])).
% 0.22/0.48  fof(f349,plain,(
% 0.22/0.48    ~spl5_1 | spl5_4),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f345])).
% 0.22/0.48  fof(f345,plain,(
% 0.22/0.48    $false | (~spl5_1 | spl5_4)),
% 0.22/0.48    inference(resolution,[],[f295,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    r1_xboole_0(sK0,sK1) | ~spl5_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f64])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl5_1 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.48  fof(f295,plain,(
% 0.22/0.48    ~r1_xboole_0(sK0,sK1) | spl5_4),
% 0.22/0.48    inference(resolution,[],[f146,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,sK0) | spl5_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f145])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    spl5_4 <=> r1_xboole_0(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.48  fof(f292,plain,(
% 0.22/0.48    spl5_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f288])).
% 0.22/0.48  fof(f288,plain,(
% 0.22/0.48    $false | spl5_9),
% 0.22/0.48    inference(resolution,[],[f272,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    r1_xboole_0(sK2,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.22/0.48    inference(ennf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f13])).
% 0.22/0.48  fof(f13,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.22/0.48  fof(f272,plain,(
% 0.22/0.48    ~r1_xboole_0(sK2,sK1) | spl5_9),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f269])).
% 0.22/0.48  fof(f269,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK2,sK1) | spl5_9),
% 0.22/0.48    inference(superposition,[],[f267,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3)) )),
% 0.22/0.48    inference(superposition,[],[f43,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.48  fof(f267,plain,(
% 0.22/0.48    k1_xboole_0 != k3_xboole_0(sK1,sK2) | spl5_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f265])).
% 0.22/0.48  fof(f265,plain,(
% 0.22/0.48    spl5_9 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.48  fof(f268,plain,(
% 0.22/0.48    ~spl5_4 | ~spl5_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f260,f265,f145])).
% 0.22/0.48  fof(f260,plain,(
% 0.22/0.48    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 0.22/0.48    inference(resolution,[],[f107,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))),
% 0.22/0.48    inference(resolution,[],[f52,f42])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 0.22/0.48    inference(definition_unfolding,[],[f33,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f36,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f37,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  % (10235)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  fof(f12,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ( ! [X10,X11,X9] : (r1_xboole_0(X9,k3_tarski(k2_enumset1(X10,X10,X10,X11))) | k1_xboole_0 != k3_xboole_0(X9,X11) | ~r1_xboole_0(X9,X10)) )),
% 0.22/0.48    inference(superposition,[],[f44,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f47,f50])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    ~spl5_3),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.48  fof(f173,plain,(
% 0.22/0.48    $false | ~spl5_3),
% 0.22/0.48    inference(resolution,[],[f168,f32])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    ~r1_xboole_0(sK2,sK1) | ~spl5_3),
% 0.22/0.48    inference(resolution,[],[f153,f42])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,sK2) | ~spl5_3),
% 0.22/0.48    inference(resolution,[],[f142,f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 0.22/0.48    inference(resolution,[],[f40,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    r2_hidden(sK3,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    r2_hidden(sK3,sK1) | ~spl5_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f140])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    spl5_3 <=> r2_hidden(sK3,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    spl5_1 | spl5_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f133,f140,f64])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    r2_hidden(sK3,sK1) | r1_xboole_0(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f131,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X0) | r2_hidden(sK3,X0)) )),
% 0.22/0.48    inference(resolution,[],[f94,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f41,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f34,f49])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X0) | r1_xboole_0(k3_xboole_0(sK0,sK1),X0)) )),
% 0.22/0.48    inference(resolution,[],[f48,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.22/0.48    inference(definition_unfolding,[],[f30,f51])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (10238)------------------------------
% 0.22/0.48  % (10238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (10238)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (10238)Memory used [KB]: 6268
% 0.22/0.48  % (10238)Time elapsed: 0.058 s
% 0.22/0.48  % (10238)------------------------------
% 0.22/0.48  % (10238)------------------------------
% 0.22/0.49  % (10233)Success in time 0.126 s
%------------------------------------------------------------------------------
