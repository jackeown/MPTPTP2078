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
% DateTime   : Thu Dec  3 12:37:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 423 expanded)
%              Number of leaves         :   17 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          :  212 (1151 expanded)
%              Number of equality atoms :   73 ( 544 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f110,f195,f232,f323])).

fof(f323,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f321,f43])).

fof(f43,plain,(
    sK0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f25,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ! [X2] :
        ( sK1 = X2
        | ~ r2_hidden(X2,sK0) )
    & k1_xboole_0 != sK0
    & sK0 != k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK1 = X2
          | ~ r2_hidden(X2,sK0) )
      & k1_xboole_0 != sK0
      & sK0 != k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f321,plain,
    ( sK0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f311,f260])).

fof(f260,plain,
    ( sK0 = k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f109,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | sK0 = k3_xboole_0(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | sK0 = k3_xboole_0(sK0,X0)
      | sK0 = k3_xboole_0(sK0,X0) ) ),
    inference(superposition,[],[f54,f52])).

fof(f52,plain,(
    ! [X0] :
      ( sK1 = sK3(sK0,X0)
      | sK0 = k3_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f51,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | sK1 = sK3(sK0,X0) ) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f35,f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f109,plain,
    ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_3
  <=> r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f311,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f30,f92])).

fof(f92,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(resolution,[],[f85,f32])).

fof(f85,plain,(
    r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(resolution,[],[f44,f49])).

fof(f49,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f48,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f29,f47])).

fof(f47,plain,(
    sK1 = sK2(sK0) ),
    inference(subsumption_resolution,[],[f46,f26])).

fof(f46,plain,
    ( k1_xboole_0 = sK0
    | sK1 = sK2(sK0) ),
    inference(resolution,[],[f29,f27])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f232,plain,
    ( ~ spl4_1
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl4_1
    | spl4_9 ),
    inference(resolution,[],[f223,f169])).

fof(f169,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl4_9
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f223,plain,
    ( ! [X1] : r2_hidden(sK1,X1)
    | ~ spl4_1
    | spl4_9 ),
    inference(subsumption_resolution,[],[f222,f208])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r2_hidden(sK1,X0) )
    | ~ spl4_1 ),
    inference(superposition,[],[f45,f99])).

fof(f99,plain,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_1
  <=> k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f222,plain,
    ( ! [X1] :
        ( r1_tarski(k1_xboole_0,X1)
        | r2_hidden(sK1,X1) )
    | ~ spl4_1
    | spl4_9 ),
    inference(subsumption_resolution,[],[f218,f169])).

fof(f218,plain,
    ( ! [X1] :
        ( r2_hidden(sK1,k1_xboole_0)
        | r1_tarski(k1_xboole_0,X1)
        | r2_hidden(sK1,X1) )
    | ~ spl4_1 ),
    inference(superposition,[],[f34,f215])).

fof(f215,plain,
    ( ! [X0] :
        ( sK1 = sK3(k1_xboole_0,X0)
        | r2_hidden(sK1,X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f208,f123])).

fof(f123,plain,
    ( ! [X2] :
        ( r1_tarski(k1_xboole_0,X2)
        | sK1 = sK3(k1_xboole_0,X2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f112,f34])).

fof(f112,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k1_xboole_0)
        | sK1 = X9 )
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f91,f99])).

fof(f91,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
      | sK1 = X9 ) ),
    inference(resolution,[],[f85,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | sK1 = X0 ) ),
    inference(resolution,[],[f33,f27])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f195,plain,
    ( ~ spl4_1
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f193,f26])).

fof(f193,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f183,f119])).

fof(f119,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f113,f32])).

fof(f113,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f85,f99])).

fof(f183,plain,
    ( sK0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_9 ),
    inference(superposition,[],[f30,f175])).

fof(f175,plain,
    ( sK0 = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_9 ),
    inference(resolution,[],[f170,f76])).

fof(f170,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f168])).

fof(f110,plain,
    ( spl4_1
    | spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f105,f101,f107,f97])).

fof(f101,plain,
    ( spl4_2
  <=> sK1 = sK2(k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f105,plain,
    ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f29,f103])).

fof(f103,plain,
    ( sK1 = sK2(k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f104,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f94,f101,f97])).

fof(f94,plain,
    ( sK1 = sK2(k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f91,f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (4762)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.48  % (4759)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (4778)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.50  % (4770)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (4769)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (4768)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (4761)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (4760)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (4782)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (4789)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (4780)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (4764)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (4770)Refutation not found, incomplete strategy% (4770)------------------------------
% 0.21/0.51  % (4770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4770)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4770)Memory used [KB]: 10618
% 0.21/0.51  % (4770)Time elapsed: 0.112 s
% 0.21/0.51  % (4770)------------------------------
% 0.21/0.51  % (4770)------------------------------
% 0.21/0.52  % (4783)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (4774)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (4772)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (4763)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (4775)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (4765)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (4786)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (4777)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (4787)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (4773)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (4762)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f104,f110,f195,f232,f323])).
% 0.21/0.53  fof(f323,plain,(
% 0.21/0.53    ~spl4_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f322])).
% 0.21/0.53  fof(f322,plain,(
% 0.21/0.53    $false | ~spl4_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f321,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    sK0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.21/0.53    inference(definition_unfolding,[],[f25,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f28,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f31,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f38,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    sK0 != k1_tarski(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.21/0.53  fof(f321,plain,(
% 0.21/0.53    sK0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl4_3),
% 0.21/0.53    inference(forward_demodulation,[],[f311,f260])).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    sK0 = k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl4_3),
% 0.21/0.53    inference(resolution,[],[f109,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK1,X0) | sK0 = k3_xboole_0(sK0,X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK1,X0) | sK0 = k3_xboole_0(sK0,X0) | sK0 = k3_xboole_0(sK0,X0)) )),
% 0.21/0.53    inference(superposition,[],[f54,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0] : (sK1 = sK3(sK0,X0) | sK0 = k3_xboole_0(sK0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f51,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(sK0,X0) | sK1 = sK3(sK0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f34,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.53    inference(resolution,[],[f35,f32])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl4_3 <=> r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f311,plain,(
% 0.21/0.53    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.21/0.53    inference(superposition,[],[f30,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.53    inference(resolution,[],[f85,f32])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.53    inference(resolution,[],[f44,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f48,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(superposition,[],[f29,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    sK1 = sK2(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f46,f26])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | sK1 = sK2(sK0)),
% 0.21/0.53    inference(resolution,[],[f29,f27])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f37,f42])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    ~spl4_1 | spl4_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f229])).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    $false | (~spl4_1 | spl4_9)),
% 0.21/0.53    inference(resolution,[],[f223,f169])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k1_xboole_0) | spl4_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f168])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    spl4_9 <=> r2_hidden(sK1,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(sK1,X1)) ) | (~spl4_1 | spl4_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f222,f208])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r2_hidden(sK1,X0)) ) | ~spl4_1),
% 0.21/0.53    inference(superposition,[],[f45,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl4_1 <=> k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f36,f42])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(k1_xboole_0,X1) | r2_hidden(sK1,X1)) ) | (~spl4_1 | spl4_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f218,f169])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(sK1,k1_xboole_0) | r1_tarski(k1_xboole_0,X1) | r2_hidden(sK1,X1)) ) | ~spl4_1),
% 0.21/0.53    inference(superposition,[],[f34,f215])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    ( ! [X0] : (sK1 = sK3(k1_xboole_0,X0) | r2_hidden(sK1,X0)) ) | ~spl4_1),
% 0.21/0.53    inference(resolution,[],[f208,f123])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X2] : (r1_tarski(k1_xboole_0,X2) | sK1 = sK3(k1_xboole_0,X2)) ) | ~spl4_1),
% 0.21/0.53    inference(resolution,[],[f112,f34])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ( ! [X9] : (~r2_hidden(X9,k1_xboole_0) | sK1 = X9) ) | ~spl4_1),
% 0.21/0.53    inference(backward_demodulation,[],[f91,f99])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X9] : (~r2_hidden(X9,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | sK1 = X9) )),
% 0.21/0.53    inference(resolution,[],[f85,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | ~r2_hidden(X0,X1) | sK1 = X0) )),
% 0.21/0.53    inference(resolution,[],[f33,f27])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    ~spl4_1 | ~spl4_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f194])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    $false | (~spl4_1 | ~spl4_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f193,f26])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | (~spl4_1 | ~spl4_9)),
% 0.21/0.53    inference(forward_demodulation,[],[f183,f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) | ~spl4_1),
% 0.21/0.53    inference(resolution,[],[f113,f32])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    r1_tarski(k1_xboole_0,sK0) | ~spl4_1),
% 0.21/0.53    inference(backward_demodulation,[],[f85,f99])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    sK0 = k3_xboole_0(k1_xboole_0,sK0) | ~spl4_9),
% 0.21/0.53    inference(superposition,[],[f30,f175])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    sK0 = k3_xboole_0(sK0,k1_xboole_0) | ~spl4_9),
% 0.21/0.53    inference(resolution,[],[f170,f76])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    r2_hidden(sK1,k1_xboole_0) | ~spl4_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f168])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl4_1 | spl4_3 | ~spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f105,f101,f107,f97])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl4_2 <=> sK1 = sK2(k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl4_2),
% 0.21/0.53    inference(superposition,[],[f29,f103])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    sK1 = sK2(k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f101])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl4_1 | spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f94,f101,f97])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    sK1 = sK2(k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.21/0.53    inference(resolution,[],[f91,f29])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (4762)------------------------------
% 0.21/0.53  % (4762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4762)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (4762)Memory used [KB]: 10874
% 0.21/0.53  % (4762)Time elapsed: 0.112 s
% 0.21/0.53  % (4762)------------------------------
% 0.21/0.53  % (4762)------------------------------
% 0.21/0.53  % (4781)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (4758)Success in time 0.178 s
%------------------------------------------------------------------------------
