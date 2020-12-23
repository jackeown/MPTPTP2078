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
% DateTime   : Thu Dec  3 12:41:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 153 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :  198 ( 312 expanded)
%              Number of equality atoms :   74 ( 145 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f64,f68,f74,f78,f82,f89,f94,f113,f121])).

fof(f121,plain,
    ( spl2_5
    | spl2_7
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl2_5
    | spl2_7
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f119,f63])).

fof(f63,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_5
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f119,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_7
    | ~ spl2_15 ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_7
    | ~ spl2_15 ),
    inference(superposition,[],[f73,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))
        | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))
        | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f73,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_7
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f113,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f95,f92,f44,f111])).

fof(f44,plain,
    ( spl2_1
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f92,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))
        | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))
        | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) )
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(superposition,[],[f93,f45])).

fof(f45,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))
        | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,
    ( spl2_11
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f90,f87,f76,f92])).

fof(f76,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f87,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))
        | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(resolution,[],[f88,f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( spl2_10
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f85,f80,f87])).

fof(f80,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X1)
        | r2_hidden(X2,X1)
        | k2_enumset1(X2,X2,X2,X0) = k5_xboole_0(k2_enumset1(X2,X2,X2,X0),k3_xboole_0(k2_enumset1(X2,X2,X2,X0),X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )
    | ~ spl2_9 ),
    inference(factoring,[],[f81])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,X1)
        | r2_hidden(X2,X1)
        | k2_enumset1(X2,X2,X2,X0) = k5_xboole_0(k2_enumset1(X2,X2,X2,X0),k3_xboole_0(k2_enumset1(X2,X2,X2,X0),X1)) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f69,f66,f48,f80])).

fof(f48,plain,
    ( spl2_2
  <=> ! [X1,X0] :
        ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( spl2_6
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
        | r2_hidden(X2,X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,X1)
        | r2_hidden(X2,X1)
        | k2_enumset1(X2,X2,X2,X0) = k5_xboole_0(k2_enumset1(X2,X2,X2,X0),k3_xboole_0(k2_enumset1(X2,X2,X2,X0),X1)) )
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f67,f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f67,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
        | r2_hidden(X2,X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f78,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f59,f56,f52,f76])).

fof(f52,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f56,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f57,f53])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f74,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f42,f71])).

fof(f42,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f35,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f35,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f23,f34,f27,f34])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

% (19143)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% (19145)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% (19146)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f21,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f68,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f40,f66])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f64,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f41,f61])).

fof(f41,plain,(
    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f36,f25])).

fof(f36,plain,(
    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f22,f27,f34])).

fof(f22,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f39,f56])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f54,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f38,f52])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f50,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f37,f48])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f46,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f25,f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:21:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (19150)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.45  % (19158)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (19150)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f64,f68,f74,f78,f82,f89,f94,f113,f121])).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    spl2_5 | spl2_7 | ~spl2_15),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f120])).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    $false | (spl2_5 | spl2_7 | ~spl2_15)),
% 0.20/0.46    inference(subsumption_resolution,[],[f119,f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl2_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f61])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    spl2_5 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.46  fof(f119,plain,(
% 0.20/0.46    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | (spl2_7 | ~spl2_15)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f116])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | (spl2_7 | ~spl2_15)),
% 0.20/0.46    inference(superposition,[],[f73,f112])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) ) | ~spl2_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f111])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    spl2_15 <=> ! [X1,X0] : (k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl2_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f71])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    spl2_7 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    spl2_15 | ~spl2_1 | ~spl2_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f95,f92,f44,f111])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    spl2_1 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    spl2_11 <=> ! [X1,X0] : (k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) ) | (~spl2_1 | ~spl2_11)),
% 0.20/0.46    inference(superposition,[],[f93,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f44])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) ) | ~spl2_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f92])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    spl2_11 | ~spl2_8 | ~spl2_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f90,f87,f76,f92])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    spl2_8 <=> ! [X1,X0] : (k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    spl2_10 <=> ! [X1,X0] : (r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) ) | (~spl2_8 | ~spl2_10)),
% 0.20/0.46    inference(resolution,[],[f88,f77])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) ) | ~spl2_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f76])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) ) | ~spl2_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f87])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    spl2_10 | ~spl2_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f85,f80,f87])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    spl2_9 <=> ! [X1,X0,X2] : (r2_hidden(X0,X1) | r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X0) = k5_xboole_0(k2_enumset1(X2,X2,X2,X0),k3_xboole_0(k2_enumset1(X2,X2,X2,X0),X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) ) | ~spl2_9),
% 0.20/0.46    inference(factoring,[],[f81])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X0) = k5_xboole_0(k2_enumset1(X2,X2,X2,X0),k3_xboole_0(k2_enumset1(X2,X2,X2,X0),X1))) ) | ~spl2_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f80])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    spl2_9 | ~spl2_2 | ~spl2_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f69,f66,f48,f80])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl2_2 <=> ! [X1,X0] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    spl2_6 <=> ! [X1,X0,X2] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X0) = k5_xboole_0(k2_enumset1(X2,X2,X2,X0),k3_xboole_0(k2_enumset1(X2,X2,X2,X0),X1))) ) | (~spl2_2 | ~spl2_6)),
% 0.20/0.46    inference(resolution,[],[f67,f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f48])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) ) | ~spl2_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f66])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    spl2_8 | ~spl2_3 | ~spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f59,f56,f52,f76])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    spl2_3 <=> ! [X1,X0] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    spl2_4 <=> ! [X1,X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) | ~r2_hidden(X0,X1)) ) | (~spl2_3 | ~spl2_4)),
% 0.20/0.46    inference(resolution,[],[f57,f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f52])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f56])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    ~spl2_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f42,f71])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.46    inference(backward_demodulation,[],[f35,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.20/0.46    inference(definition_unfolding,[],[f23,f34,f27,f34])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f24,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f26,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  % (19143)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (19145)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (19146)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.47    inference(negated_conjecture,[],[f10])).
% 0.20/0.47  fof(f10,conjecture,(
% 0.20/0.47    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl2_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f66])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f32,f33])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ~spl2_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f41,f61])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.47    inference(backward_demodulation,[],[f36,f25])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.20/0.47    inference(definition_unfolding,[],[f22,f27,f34])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl2_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f39,f56])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f30,f27])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.47    inference(unused_predicate_definition_removal,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl2_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f52])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f29,f34])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 0.20/0.47    inference(unused_predicate_definition_removal,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f48])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f28,f27])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 0.20/0.47    inference(unused_predicate_definition_removal,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    spl2_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f25,f44])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (19150)------------------------------
% 0.20/0.47  % (19150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (19150)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (19150)Memory used [KB]: 6140
% 0.20/0.47  % (19150)Time elapsed: 0.061 s
% 0.20/0.47  % (19150)------------------------------
% 0.20/0.47  % (19150)------------------------------
% 0.20/0.47  % (19142)Success in time 0.115 s
%------------------------------------------------------------------------------
