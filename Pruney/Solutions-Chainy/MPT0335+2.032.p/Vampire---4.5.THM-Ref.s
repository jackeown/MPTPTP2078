%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 174 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  190 ( 364 expanded)
%              Number of equality atoms :   77 ( 178 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f333,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f78,f86,f107,f154,f163,f275,f332])).

fof(f332,plain,
    ( ~ spl4_6
    | spl4_8
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl4_6
    | spl4_8
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f330,f106])).

fof(f106,plain,
    ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK1,sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_8
  <=> k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f330,plain,
    ( k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2)
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f311,f88])).

fof(f88,plain,
    ( ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)
    | ~ spl4_6 ),
    inference(superposition,[],[f39,f84])).

fof(f84,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_6
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f311,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl4_18 ),
    inference(superposition,[],[f30,f198])).

fof(f198,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl4_18
  <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f275,plain,
    ( spl4_18
    | ~ spl4_3
    | spl4_15 ),
    inference(avatar_split_clause,[],[f262,f159,f63,f196])).

fof(f63,plain,
    ( spl4_3
  <=> k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f159,plain,
    ( spl4_15
  <=> k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f262,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl4_3
    | spl4_15 ),
    inference(unit_resulting_resolution,[],[f161,f186])).

fof(f186,plain,
    ( ! [X0] :
        ( k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),X0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f99,f29])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f99,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k3_xboole_0(sK1,sK2))
        | k3_xboole_0(sK1,sK2) = X1
        | k1_xboole_0 = X1 )
    | ~ spl4_3 ),
    inference(superposition,[],[f48,f65])).

fof(f65,plain,
    ( k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f34,f43,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f161,plain,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f163,plain,
    ( ~ spl4_15
    | spl4_14 ),
    inference(avatar_split_clause,[],[f156,f151,f159])).

fof(f151,plain,
    ( spl4_14
  <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f156,plain,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | spl4_14 ),
    inference(resolution,[],[f153,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f153,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f154,plain,
    ( ~ spl4_14
    | ~ spl4_3
    | spl4_5 ),
    inference(avatar_split_clause,[],[f149,f75,f63,f151])).

fof(f75,plain,
    ( spl4_5
  <=> r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f149,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl4_3
    | spl4_5 ),
    inference(forward_demodulation,[],[f77,f65])).

fof(f77,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f107,plain,
    ( ~ spl4_8
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f97,f63,f53,f104])).

fof(f53,plain,
    ( spl4_1
  <=> k3_xboole_0(sK0,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f97,plain,
    ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK1,sK2)
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f55,f65])).

fof(f55,plain,
    ( k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f86,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f80,f68,f82])).

fof(f68,plain,
    ( spl4_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f80,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f70,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f70,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f78,plain,
    ( ~ spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f72,f58,f75])).

fof(f58,plain,
    ( spl4_2
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f72,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f60,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f60,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f71,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f24,f68])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f66,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f45,f63])).

fof(f45,plain,(
    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f25,f43])).

fof(f25,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f44,f53])).

fof(f44,plain,(
    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f27,f43])).

fof(f27,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (8303)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (8312)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (8295)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (8296)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (8304)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (8293)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (8292)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (8308)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (8290)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (8317)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (8299)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (8291)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (8318)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (8298)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (8301)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (8309)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (8294)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (8300)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (8310)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (8297)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (8315)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (8313)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (8315)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f333,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f78,f86,f107,f154,f163,f275,f332])).
% 0.20/0.55  fof(f332,plain,(
% 0.20/0.55    ~spl4_6 | spl4_8 | ~spl4_18),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f331])).
% 0.20/0.55  fof(f331,plain,(
% 0.20/0.55    $false | (~spl4_6 | spl4_8 | ~spl4_18)),
% 0.20/0.55    inference(subsumption_resolution,[],[f330,f106])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK1,sK2) | spl4_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f104])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    spl4_8 <=> k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.55  fof(f330,plain,(
% 0.20/0.55    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2) | (~spl4_6 | ~spl4_18)),
% 0.20/0.55    inference(forward_demodulation,[],[f311,f88])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) ) | ~spl4_6),
% 0.20/0.55    inference(superposition,[],[f39,f84])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    spl4_6 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.55  fof(f311,plain,(
% 0.20/0.55    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl4_18),
% 0.20/0.55    inference(superposition,[],[f30,f198])).
% 0.20/0.55  fof(f198,plain,(
% 0.20/0.55    k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) | ~spl4_18),
% 0.20/0.55    inference(avatar_component_clause,[],[f196])).
% 0.20/0.55  fof(f196,plain,(
% 0.20/0.55    spl4_18 <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.55  fof(f275,plain,(
% 0.20/0.55    spl4_18 | ~spl4_3 | spl4_15),
% 0.20/0.55    inference(avatar_split_clause,[],[f262,f159,f63,f196])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    spl4_3 <=> k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.55  fof(f159,plain,(
% 0.20/0.55    spl4_15 <=> k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.55  fof(f262,plain,(
% 0.20/0.55    k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) | (~spl4_3 | spl4_15)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f161,f186])).
% 0.20/0.55  fof(f186,plain,(
% 0.20/0.55    ( ! [X0] : (k3_xboole_0(sK1,sK2) = k3_xboole_0(k3_xboole_0(sK1,sK2),X0) | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) ) | ~spl4_3),
% 0.20/0.55    inference(resolution,[],[f99,f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    ( ! [X1] : (~r1_tarski(X1,k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = X1 | k1_xboole_0 = X1) ) | ~spl4_3),
% 0.20/0.55    inference(superposition,[],[f48,f65])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | ~spl4_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f63])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f34,f43,f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f28,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f31,f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f38,f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.55  fof(f161,plain,(
% 0.20/0.55    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) | spl4_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f159])).
% 0.20/0.55  fof(f163,plain,(
% 0.20/0.55    ~spl4_15 | spl4_14),
% 0.20/0.55    inference(avatar_split_clause,[],[f156,f151,f159])).
% 0.20/0.55  fof(f151,plain,(
% 0.20/0.55    spl4_14 <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.55  fof(f156,plain,(
% 0.20/0.55    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) | spl4_14),
% 0.20/0.55    inference(resolution,[],[f153,f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 0.20/0.55    inference(unused_predicate_definition_removal,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.55  fof(f153,plain,(
% 0.20/0.55    ~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) | spl4_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f151])).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    ~spl4_14 | ~spl4_3 | spl4_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f149,f75,f63,f151])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    spl4_5 <=> r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.55  fof(f149,plain,(
% 0.20/0.55    ~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) | (~spl4_3 | spl4_5)),
% 0.20/0.55    inference(forward_demodulation,[],[f77,f65])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ~r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) | spl4_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f75])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ~spl4_8 | spl4_1 | ~spl4_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f97,f63,f53,f104])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    spl4_1 <=> k3_xboole_0(sK0,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    k3_xboole_0(sK0,sK2) != k3_xboole_0(sK1,sK2) | (spl4_1 | ~spl4_3)),
% 0.20/0.55    inference(superposition,[],[f55,f65])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) | spl4_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f53])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    spl4_6 | ~spl4_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f80,f68,f82])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    spl4_4 <=> r1_tarski(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_4),
% 0.20/0.55    inference(resolution,[],[f70,f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    r1_tarski(sK0,sK1) | ~spl4_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f68])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ~spl4_5 | ~spl4_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f72,f58,f75])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    spl4_2 <=> r2_hidden(sK3,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ~r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) | ~spl4_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f60,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f37,f43])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    r2_hidden(sK3,sK0) | ~spl4_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f58])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    spl4_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f24,f68])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    r1_tarski(sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 0.20/0.55    inference(flattening,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 0.20/0.55    inference(negated_conjecture,[],[f12])).
% 0.20/0.55  fof(f12,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    spl4_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f45,f63])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 0.20/0.55    inference(definition_unfolding,[],[f25,f43])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    spl4_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f26,f58])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    r2_hidden(sK3,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ~spl4_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f44,f53])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 0.20/0.55    inference(definition_unfolding,[],[f27,f43])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (8315)------------------------------
% 0.20/0.55  % (8315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8315)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (8315)Memory used [KB]: 6396
% 0.20/0.55  % (8315)Time elapsed: 0.142 s
% 0.20/0.55  % (8315)------------------------------
% 0.20/0.55  % (8315)------------------------------
% 0.20/0.56  % (8307)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (8305)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (8305)Refutation not found, incomplete strategy% (8305)------------------------------
% 0.20/0.56  % (8305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (8305)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (8305)Memory used [KB]: 6140
% 0.20/0.56  % (8305)Time elapsed: 0.151 s
% 0.20/0.56  % (8305)------------------------------
% 0.20/0.56  % (8305)------------------------------
% 0.20/0.56  % (8307)Refutation not found, incomplete strategy% (8307)------------------------------
% 0.20/0.56  % (8307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (8307)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (8307)Memory used [KB]: 10618
% 0.20/0.56  % (8307)Time elapsed: 0.150 s
% 0.20/0.56  % (8307)------------------------------
% 0.20/0.56  % (8307)------------------------------
% 0.20/0.56  % (8311)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (8316)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.57  % (8319)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.57  % (8306)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.57  % (8314)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.58  % (8289)Success in time 0.215 s
%------------------------------------------------------------------------------
