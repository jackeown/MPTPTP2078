%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:39 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 109 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 ( 303 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f121,f161])).

fof(f161,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f159,f122])).

fof(f122,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f93,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f93,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f159,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f153,f51])).

fof(f51,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f38,f29])).

fof(f29,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f22])).

fof(f22,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f153,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f103,f30])).

fof(f30,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,(
    ! [X6,X8,X7] :
      ( r1_xboole_0(k2_xboole_0(X7,X8),X6)
      | ~ r1_xboole_0(X6,X8)
      | ~ r1_xboole_0(X6,X7) ) ),
    inference(resolution,[],[f42,f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f121,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f118,f97])).

fof(f97,plain,
    ( ~ r1_xboole_0(k1_enumset1(sK3,sK3,sK3),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_2
  <=> r1_xboole_0(k1_enumset1(sK3,sK3,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f118,plain,(
    r1_xboole_0(k1_enumset1(sK3,sK3,sK3),sK1) ),
    inference(superposition,[],[f52,f107])).

fof(f107,plain,(
    sK1 = k4_xboole_0(sK1,k1_enumset1(sK3,sK3,sK3)) ),
    inference(resolution,[],[f106,f29])).

fof(f106,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(sK2,X3)
      | k4_xboole_0(X3,k1_enumset1(sK3,sK3,sK3)) = X3 ) ),
    inference(resolution,[],[f48,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f38,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f98,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f86,f95,f91])).

fof(f86,plain,
    ( ~ r1_xboole_0(k1_enumset1(sK3,sK3,sK3),sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f69,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f69,plain,(
    ! [X0] :
      ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)
      | ~ r1_xboole_0(k1_enumset1(sK3,sK3,sK3),X0) ) ),
    inference(resolution,[],[f45,f47])).

fof(f47,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_enumset1(sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f27,f34,f46])).

fof(f27,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (2974)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.43  % (2974)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f162,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(avatar_sat_refutation,[],[f98,f121,f161])).
% 0.19/0.43  fof(f161,plain,(
% 0.19/0.43    ~spl5_1),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f160])).
% 0.19/0.43  fof(f160,plain,(
% 0.19/0.43    $false | ~spl5_1),
% 0.19/0.43    inference(subsumption_resolution,[],[f159,f122])).
% 0.19/0.43  fof(f122,plain,(
% 0.19/0.43    r1_xboole_0(sK1,sK0) | ~spl5_1),
% 0.19/0.43    inference(resolution,[],[f93,f38])).
% 0.19/0.43  fof(f38,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f17])).
% 0.19/0.43  fof(f17,plain,(
% 0.19/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f1])).
% 0.19/0.43  fof(f1,axiom,(
% 0.19/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.19/0.43  fof(f93,plain,(
% 0.19/0.43    r1_xboole_0(sK0,sK1) | ~spl5_1),
% 0.19/0.43    inference(avatar_component_clause,[],[f91])).
% 0.19/0.43  fof(f91,plain,(
% 0.19/0.43    spl5_1 <=> r1_xboole_0(sK0,sK1)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.43  fof(f159,plain,(
% 0.19/0.43    ~r1_xboole_0(sK1,sK0)),
% 0.19/0.43    inference(subsumption_resolution,[],[f153,f51])).
% 0.19/0.43  fof(f51,plain,(
% 0.19/0.43    r1_xboole_0(sK1,sK2)),
% 0.19/0.43    inference(resolution,[],[f38,f29])).
% 0.19/0.43  fof(f29,plain,(
% 0.19/0.43    r1_xboole_0(sK2,sK1)),
% 0.19/0.43    inference(cnf_transformation,[],[f23])).
% 0.19/0.43  fof(f23,plain,(
% 0.19/0.43    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f22])).
% 0.19/0.43  fof(f22,plain,(
% 0.19/0.43    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f15,plain,(
% 0.19/0.43    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.19/0.43    inference(flattening,[],[f14])).
% 0.19/0.43  fof(f14,plain,(
% 0.19/0.43    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.19/0.43    inference(ennf_transformation,[],[f12])).
% 0.19/0.43  fof(f12,negated_conjecture,(
% 0.19/0.43    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.19/0.43    inference(negated_conjecture,[],[f11])).
% 0.19/0.43  fof(f11,conjecture,(
% 0.19/0.43    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.19/0.43  fof(f153,plain,(
% 0.19/0.43    ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 0.19/0.43    inference(resolution,[],[f103,f30])).
% 0.19/0.43  fof(f30,plain,(
% 0.19/0.43    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.19/0.43    inference(cnf_transformation,[],[f23])).
% 0.19/0.43  fof(f103,plain,(
% 0.19/0.43    ( ! [X6,X8,X7] : (r1_xboole_0(k2_xboole_0(X7,X8),X6) | ~r1_xboole_0(X6,X8) | ~r1_xboole_0(X6,X7)) )),
% 0.19/0.43    inference(resolution,[],[f42,f38])).
% 0.19/0.43  fof(f42,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f19])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.19/0.43    inference(ennf_transformation,[],[f5])).
% 0.19/0.43  fof(f5,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.19/0.43  fof(f121,plain,(
% 0.19/0.43    spl5_2),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f120])).
% 0.19/0.43  fof(f120,plain,(
% 0.19/0.43    $false | spl5_2),
% 0.19/0.43    inference(subsumption_resolution,[],[f118,f97])).
% 0.19/0.43  fof(f97,plain,(
% 0.19/0.43    ~r1_xboole_0(k1_enumset1(sK3,sK3,sK3),sK1) | spl5_2),
% 0.19/0.43    inference(avatar_component_clause,[],[f95])).
% 0.19/0.43  fof(f95,plain,(
% 0.19/0.43    spl5_2 <=> r1_xboole_0(k1_enumset1(sK3,sK3,sK3),sK1)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.43  fof(f118,plain,(
% 0.19/0.43    r1_xboole_0(k1_enumset1(sK3,sK3,sK3),sK1)),
% 0.19/0.43    inference(superposition,[],[f52,f107])).
% 0.19/0.43  fof(f107,plain,(
% 0.19/0.43    sK1 = k4_xboole_0(sK1,k1_enumset1(sK3,sK3,sK3))),
% 0.19/0.43    inference(resolution,[],[f106,f29])).
% 0.19/0.43  fof(f106,plain,(
% 0.19/0.43    ( ! [X3] : (~r1_xboole_0(sK2,X3) | k4_xboole_0(X3,k1_enumset1(sK3,sK3,sK3)) = X3) )),
% 0.19/0.43    inference(resolution,[],[f48,f65])).
% 0.19/0.43  fof(f65,plain,(
% 0.19/0.43    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(sK2,X0)) )),
% 0.19/0.43    inference(resolution,[],[f37,f28])).
% 0.19/0.43  fof(f28,plain,(
% 0.19/0.43    r2_hidden(sK3,sK2)),
% 0.19/0.43    inference(cnf_transformation,[],[f23])).
% 0.19/0.43  fof(f37,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f25])).
% 0.19/0.43  fof(f25,plain,(
% 0.19/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f24])).
% 0.19/0.43  fof(f24,plain,(
% 0.19/0.43    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f16,plain,(
% 0.19/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.43    inference(ennf_transformation,[],[f13])).
% 0.19/0.43  fof(f13,plain,(
% 0.19/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.43    inference(rectify,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.19/0.43  fof(f48,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0) )),
% 0.19/0.43    inference(definition_unfolding,[],[f40,f46])).
% 0.19/0.43  fof(f46,plain,(
% 0.19/0.43    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f31,f33])).
% 0.19/0.43  fof(f33,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f9])).
% 0.19/0.43  fof(f9,axiom,(
% 0.19/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.43  fof(f31,plain,(
% 0.19/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f8])).
% 0.19/0.43  fof(f8,axiom,(
% 0.19/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.43  fof(f40,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f26])).
% 0.19/0.43  fof(f26,plain,(
% 0.19/0.43    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.19/0.43    inference(nnf_transformation,[],[f10])).
% 0.19/0.43  fof(f10,axiom,(
% 0.19/0.43    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.19/0.43  fof(f52,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.43    inference(resolution,[],[f38,f32])).
% 0.19/0.43  fof(f32,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f7])).
% 0.19/0.43  fof(f7,axiom,(
% 0.19/0.43    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.19/0.43  fof(f98,plain,(
% 0.19/0.43    spl5_1 | ~spl5_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f86,f95,f91])).
% 0.19/0.43  fof(f86,plain,(
% 0.19/0.43    ~r1_xboole_0(k1_enumset1(sK3,sK3,sK3),sK1) | r1_xboole_0(sK0,sK1)),
% 0.19/0.43    inference(resolution,[],[f69,f50])).
% 0.19/0.43  fof(f50,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f41,f34])).
% 0.19/0.43  fof(f34,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f3])).
% 0.19/0.43  fof(f3,axiom,(
% 0.19/0.43    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.43  fof(f41,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f18])).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f6])).
% 0.19/0.43  fof(f6,axiom,(
% 0.19/0.43    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.19/0.43  fof(f69,plain,(
% 0.19/0.43    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) | ~r1_xboole_0(k1_enumset1(sK3,sK3,sK3),X0)) )),
% 0.19/0.43    inference(resolution,[],[f45,f47])).
% 0.19/0.43  fof(f47,plain,(
% 0.19/0.43    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k1_enumset1(sK3,sK3,sK3))),
% 0.19/0.43    inference(definition_unfolding,[],[f27,f34,f46])).
% 0.19/0.43  fof(f27,plain,(
% 0.19/0.43    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.19/0.43    inference(cnf_transformation,[],[f23])).
% 0.19/0.43  fof(f45,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f21])).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.43    inference(flattening,[],[f20])).
% 0.19/0.43  fof(f20,plain,(
% 0.19/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.43    inference(ennf_transformation,[],[f4])).
% 0.19/0.43  fof(f4,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.19/0.43  % SZS output end Proof for theBenchmark
% 0.19/0.43  % (2974)------------------------------
% 0.19/0.43  % (2974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (2974)Termination reason: Refutation
% 0.19/0.43  
% 0.19/0.43  % (2974)Memory used [KB]: 6268
% 0.19/0.43  % (2974)Time elapsed: 0.010 s
% 0.19/0.43  % (2974)------------------------------
% 0.19/0.43  % (2974)------------------------------
% 0.19/0.43  % (2959)Success in time 0.077 s
%------------------------------------------------------------------------------
