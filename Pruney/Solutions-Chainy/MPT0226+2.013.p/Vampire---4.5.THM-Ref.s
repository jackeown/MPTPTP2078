%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:15 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 126 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  166 ( 269 expanded)
%              Number of equality atoms :   73 ( 148 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f101,f107,f119,f122])).

fof(f122,plain,
    ( spl4_1
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f120])).

% (31697)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f120,plain,
    ( $false
    | spl4_1
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f76,f106,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f50])).

% (31699)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f10])).

% (31694)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f106,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_7
  <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f76,plain,
    ( sK0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f119,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f71,f112])).

fof(f112,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_6 ),
    inference(superposition,[],[f100,f111])).

fof(f111,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f110,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f110,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f57,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f47,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f100,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_6
  <=> ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f71,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,
    ( spl4_7
    | spl4_5 ),
    inference(avatar_split_clause,[],[f102,f95,f104])).

fof(f95,plain,
    ( spl4_5
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f102,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_5 ),
    inference(resolution,[],[f97,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f56])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f97,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f101,plain,
    ( ~ spl4_5
    | spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f83,f79,f99,f95])).

fof(f79,plain,
    ( spl4_2
  <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0))
        | ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) )
    | ~ spl4_2 ),
    inference(superposition,[],[f66,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f35])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f82,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f59,f79])).

fof(f59,plain,(
    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f33,f56,f56])).

fof(f33,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f77,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f34,f74])).

fof(f34,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (31698)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.47  % (31706)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.48  % (31706)Refutation not found, incomplete strategy% (31706)------------------------------
% 0.20/0.48  % (31706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31706)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (31706)Memory used [KB]: 10618
% 0.20/0.48  % (31706)Time elapsed: 0.093 s
% 0.20/0.48  % (31706)------------------------------
% 0.20/0.48  % (31706)------------------------------
% 0.20/0.50  % (31723)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (31701)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (31708)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (31724)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (31708)Refutation not found, incomplete strategy% (31708)------------------------------
% 0.20/0.51  % (31708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31708)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31708)Memory used [KB]: 1791
% 0.20/0.51  % (31708)Time elapsed: 0.083 s
% 0.20/0.51  % (31708)------------------------------
% 0.20/0.51  % (31708)------------------------------
% 0.20/0.51  % (31724)Refutation not found, incomplete strategy% (31724)------------------------------
% 0.20/0.51  % (31724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31724)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31724)Memory used [KB]: 1663
% 0.20/0.51  % (31724)Time elapsed: 0.001 s
% 0.20/0.51  % (31724)------------------------------
% 0.20/0.51  % (31724)------------------------------
% 1.24/0.51  % (31715)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.24/0.51  % (31696)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.24/0.51  % (31710)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.24/0.52  % (31716)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.24/0.52  % (31718)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.24/0.52  % (31718)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % (31717)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.24/0.52  % (31707)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.24/0.52  % (31695)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.52  % (31695)Refutation not found, incomplete strategy% (31695)------------------------------
% 1.24/0.52  % (31695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (31695)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (31695)Memory used [KB]: 1663
% 1.24/0.52  % (31695)Time elapsed: 0.125 s
% 1.24/0.52  % (31695)------------------------------
% 1.24/0.52  % (31695)------------------------------
% 1.24/0.52  % SZS output start Proof for theBenchmark
% 1.24/0.52  fof(f123,plain,(
% 1.24/0.52    $false),
% 1.24/0.52    inference(avatar_sat_refutation,[],[f77,f82,f101,f107,f119,f122])).
% 1.24/0.52  fof(f122,plain,(
% 1.24/0.52    spl4_1 | ~spl4_7),
% 1.24/0.52    inference(avatar_contradiction_clause,[],[f120])).
% 1.24/0.52  % (31697)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.24/0.52  fof(f120,plain,(
% 1.24/0.52    $false | (spl4_1 | ~spl4_7)),
% 1.24/0.52    inference(unit_resulting_resolution,[],[f76,f106,f72])).
% 1.24/0.52  fof(f72,plain,(
% 1.24/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.24/0.52    inference(equality_resolution,[],[f63])).
% 1.24/0.52  fof(f63,plain,(
% 1.24/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.24/0.52    inference(definition_unfolding,[],[f39,f56])).
% 1.24/0.52  fof(f56,plain,(
% 1.24/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.24/0.52    inference(definition_unfolding,[],[f44,f55])).
% 1.24/0.52  fof(f55,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.24/0.52    inference(definition_unfolding,[],[f51,f50])).
% 1.24/0.52  % (31699)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.24/0.52  fof(f50,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f14])).
% 1.24/0.52  fof(f14,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.24/0.52  fof(f51,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f13])).
% 1.24/0.52  fof(f13,axiom,(
% 1.24/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.24/0.52  fof(f44,plain,(
% 1.24/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f12])).
% 1.24/0.52  fof(f12,axiom,(
% 1.24/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.24/0.52  fof(f39,plain,(
% 1.24/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.24/0.52    inference(cnf_transformation,[],[f30])).
% 1.24/0.52  fof(f30,plain,(
% 1.24/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 1.24/0.52  fof(f29,plain,(
% 1.24/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f28,plain,(
% 1.24/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.24/0.52    inference(rectify,[],[f27])).
% 1.24/0.52  fof(f27,plain,(
% 1.24/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.24/0.52    inference(nnf_transformation,[],[f10])).
% 1.24/0.53  % (31694)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.53  fof(f10,axiom,(
% 1.24/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.24/0.53  fof(f106,plain,(
% 1.24/0.53    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl4_7),
% 1.24/0.53    inference(avatar_component_clause,[],[f104])).
% 1.24/0.53  fof(f104,plain,(
% 1.24/0.53    spl4_7 <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.24/0.53  fof(f76,plain,(
% 1.24/0.53    sK0 != sK1 | spl4_1),
% 1.24/0.53    inference(avatar_component_clause,[],[f74])).
% 1.24/0.53  fof(f74,plain,(
% 1.24/0.53    spl4_1 <=> sK0 = sK1),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.24/0.53  fof(f119,plain,(
% 1.24/0.53    ~spl4_6),
% 1.24/0.53    inference(avatar_contradiction_clause,[],[f116])).
% 1.24/0.53  fof(f116,plain,(
% 1.24/0.53    $false | ~spl4_6),
% 1.24/0.53    inference(unit_resulting_resolution,[],[f71,f112])).
% 1.24/0.53  fof(f112,plain,(
% 1.24/0.53    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) ) | ~spl4_6),
% 1.24/0.53    inference(superposition,[],[f100,f111])).
% 1.24/0.53  fof(f111,plain,(
% 1.24/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.24/0.53    inference(forward_demodulation,[],[f110,f45])).
% 1.24/0.53  fof(f45,plain,(
% 1.24/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f6])).
% 1.24/0.53  fof(f6,axiom,(
% 1.24/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.24/0.53  fof(f110,plain,(
% 1.24/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.24/0.53    inference(superposition,[],[f57,f65])).
% 1.24/0.53  fof(f65,plain,(
% 1.24/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.24/0.53    inference(definition_unfolding,[],[f47,f35])).
% 1.24/0.53  fof(f35,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f5])).
% 1.24/0.53  fof(f5,axiom,(
% 1.24/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.24/0.53  fof(f47,plain,(
% 1.24/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f4])).
% 1.24/0.53  fof(f4,axiom,(
% 1.24/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.24/0.53  fof(f57,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.24/0.53    inference(definition_unfolding,[],[f36,f35])).
% 1.24/0.53  fof(f36,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f3])).
% 1.24/0.53  fof(f3,axiom,(
% 1.24/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.24/0.53  fof(f100,plain,(
% 1.24/0.53    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0))) ) | ~spl4_6),
% 1.24/0.53    inference(avatar_component_clause,[],[f99])).
% 1.24/0.53  fof(f99,plain,(
% 1.24/0.53    spl4_6 <=> ! [X0] : ~r2_hidden(X0,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.24/0.53  fof(f71,plain,(
% 1.24/0.53    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.24/0.53    inference(equality_resolution,[],[f70])).
% 1.24/0.53  fof(f70,plain,(
% 1.24/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.24/0.53    inference(equality_resolution,[],[f62])).
% 1.24/0.53  fof(f62,plain,(
% 1.24/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.24/0.53    inference(definition_unfolding,[],[f40,f56])).
% 1.24/0.53  fof(f40,plain,(
% 1.24/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.24/0.53    inference(cnf_transformation,[],[f30])).
% 1.24/0.53  fof(f107,plain,(
% 1.24/0.53    spl4_7 | spl4_5),
% 1.24/0.53    inference(avatar_split_clause,[],[f102,f95,f104])).
% 1.24/0.53  fof(f95,plain,(
% 1.24/0.53    spl4_5 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.24/0.53  fof(f102,plain,(
% 1.24/0.53    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl4_5),
% 1.24/0.53    inference(resolution,[],[f97,f64])).
% 1.24/0.53  fof(f64,plain,(
% 1.24/0.53    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.24/0.53    inference(definition_unfolding,[],[f43,f56])).
% 1.24/0.53  fof(f43,plain,(
% 1.24/0.53    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f23])).
% 1.24/0.53  fof(f23,plain,(
% 1.24/0.53    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.24/0.53    inference(ennf_transformation,[],[f18])).
% 1.24/0.53  fof(f18,axiom,(
% 1.24/0.53    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.24/0.53  fof(f97,plain,(
% 1.24/0.53    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | spl4_5),
% 1.24/0.53    inference(avatar_component_clause,[],[f95])).
% 1.24/0.53  fof(f101,plain,(
% 1.24/0.53    ~spl4_5 | spl4_6 | ~spl4_2),
% 1.24/0.53    inference(avatar_split_clause,[],[f83,f79,f99,f95])).
% 1.24/0.53  fof(f79,plain,(
% 1.24/0.53    spl4_2 <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.24/0.53  fof(f83,plain,(
% 1.24/0.53    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)) | ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ) | ~spl4_2),
% 1.24/0.53    inference(superposition,[],[f66,f81])).
% 1.24/0.53  fof(f81,plain,(
% 1.24/0.53    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl4_2),
% 1.24/0.53    inference(avatar_component_clause,[],[f79])).
% 1.24/0.53  fof(f66,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.24/0.53    inference(definition_unfolding,[],[f49,f35])).
% 1.24/0.53  fof(f49,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f32])).
% 1.24/0.53  fof(f32,plain,(
% 1.24/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f31])).
% 1.24/0.53  fof(f31,plain,(
% 1.24/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f24,plain,(
% 1.24/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.24/0.53    inference(ennf_transformation,[],[f21])).
% 1.24/0.53  fof(f21,plain,(
% 1.24/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.24/0.53    inference(rectify,[],[f2])).
% 1.24/0.53  fof(f2,axiom,(
% 1.24/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.24/0.53  fof(f82,plain,(
% 1.24/0.53    spl4_2),
% 1.24/0.53    inference(avatar_split_clause,[],[f59,f79])).
% 1.24/0.53  fof(f59,plain,(
% 1.24/0.53    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.24/0.53    inference(definition_unfolding,[],[f33,f56,f56])).
% 1.24/0.53  fof(f33,plain,(
% 1.24/0.53    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.24/0.53    inference(cnf_transformation,[],[f26])).
% 1.24/0.53  fof(f26,plain,(
% 1.24/0.53    sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).
% 1.24/0.53  fof(f25,plain,(
% 1.24/0.53    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f22,plain,(
% 1.24/0.53    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.24/0.53    inference(ennf_transformation,[],[f20])).
% 1.24/0.53  fof(f20,negated_conjecture,(
% 1.24/0.53    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.24/0.53    inference(negated_conjecture,[],[f19])).
% 1.24/0.53  fof(f19,conjecture,(
% 1.24/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 1.24/0.53  fof(f77,plain,(
% 1.24/0.53    ~spl4_1),
% 1.24/0.53    inference(avatar_split_clause,[],[f34,f74])).
% 1.24/0.53  fof(f34,plain,(
% 1.24/0.53    sK0 != sK1),
% 1.24/0.53    inference(cnf_transformation,[],[f26])).
% 1.24/0.53  % SZS output end Proof for theBenchmark
% 1.24/0.53  % (31718)------------------------------
% 1.24/0.53  % (31718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (31718)Termination reason: Refutation
% 1.24/0.53  
% 1.24/0.53  % (31718)Memory used [KB]: 10746
% 1.24/0.53  % (31718)Time elapsed: 0.123 s
% 1.24/0.53  % (31718)------------------------------
% 1.24/0.53  % (31718)------------------------------
% 1.24/0.53  % (31722)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.24/0.53  % (31714)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.24/0.53  % (31704)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.38/0.53  % (31685)Success in time 0.179 s
%------------------------------------------------------------------------------
