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
% DateTime   : Thu Dec  3 12:41:13 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 136 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 ( 214 expanded)
%              Number of equality atoms :   61 ( 131 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f80,f86,f93,f278])).

fof(f278,plain,
    ( spl4_2
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f272,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f272,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)
    | spl4_2
    | spl4_4 ),
    inference(backward_demodulation,[],[f92,f256])).

fof(f256,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f79,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)))
      | k1_xboole_0 = k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(superposition,[],[f119,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f119,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 = k5_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),k3_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),X7))
      | k1_xboole_0 = k3_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),X7) ) ),
    inference(resolution,[],[f63,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) ) ),
    inference(resolution,[],[f51,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f42,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(resolution,[],[f50,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f37,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f79,plain,
    ( k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_2
  <=> k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f92,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_4
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f93,plain,
    ( ~ spl4_4
    | spl4_3 ),
    inference(avatar_split_clause,[],[f87,f83,f90])).

fof(f83,plain,
    ( spl4_3
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f87,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl4_3 ),
    inference(forward_demodulation,[],[f85,f33])).

fof(f85,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f86,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f48,f83])).

fof(f48,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f29,f47,f35,f47])).

fof(f29,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f80,plain,
    ( ~ spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f75,f71,f77])).

fof(f71,plain,
    ( spl4_1
  <=> k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f75,plain,
    ( k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl4_1 ),
    inference(forward_demodulation,[],[f73,f33])).

fof(f73,plain,
    ( k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f74,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f49,f71])).

fof(f49,plain,(
    k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f28,f35,f47])).

fof(f28,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n017.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 15:30:31 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.23/0.45  % (17306)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.46  % (17306)Refutation found. Thanks to Tanya!
% 0.23/0.46  % SZS status Theorem for theBenchmark
% 0.23/0.46  % SZS output start Proof for theBenchmark
% 0.23/0.46  fof(f279,plain,(
% 0.23/0.46    $false),
% 0.23/0.46    inference(avatar_sat_refutation,[],[f74,f80,f86,f93,f278])).
% 0.23/0.46  fof(f278,plain,(
% 0.23/0.46    spl4_2 | spl4_4),
% 0.23/0.46    inference(avatar_contradiction_clause,[],[f277])).
% 0.23/0.46  fof(f277,plain,(
% 0.23/0.46    $false | (spl4_2 | spl4_4)),
% 0.23/0.46    inference(subsumption_resolution,[],[f272,f30])).
% 0.23/0.46  fof(f30,plain,(
% 0.23/0.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.46    inference(cnf_transformation,[],[f6])).
% 0.23/0.46  fof(f6,axiom,(
% 0.23/0.46    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.23/0.46  fof(f272,plain,(
% 0.23/0.46    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) | (spl4_2 | spl4_4)),
% 0.23/0.46    inference(backward_demodulation,[],[f92,f256])).
% 0.23/0.46  fof(f256,plain,(
% 0.23/0.46    k1_xboole_0 = k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl4_2),
% 0.23/0.46    inference(unit_resulting_resolution,[],[f79,f166])).
% 0.23/0.46  fof(f166,plain,(
% 0.23/0.46    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0))) | k1_xboole_0 = k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 0.23/0.46    inference(superposition,[],[f119,f33])).
% 0.23/0.46  fof(f33,plain,(
% 0.23/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f1])).
% 0.23/0.46  fof(f1,axiom,(
% 0.23/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.46  fof(f119,plain,(
% 0.23/0.46    ( ! [X6,X7] : (k1_xboole_0 = k5_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),k3_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),X7)) | k1_xboole_0 = k3_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),X7)) )),
% 0.23/0.46    inference(resolution,[],[f63,f64])).
% 0.23/0.46  fof(f64,plain,(
% 0.23/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1))) )),
% 0.23/0.46    inference(resolution,[],[f51,f53])).
% 0.23/0.46  fof(f53,plain,(
% 0.23/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.46    inference(definition_unfolding,[],[f42,f35])).
% 0.23/0.46  fof(f35,plain,(
% 0.23/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.46    inference(cnf_transformation,[],[f5])).
% 0.23/0.46  fof(f5,axiom,(
% 0.23/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.46  fof(f42,plain,(
% 0.23/0.46    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f27])).
% 0.23/0.46  fof(f27,plain,(
% 0.23/0.46    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.23/0.46    inference(nnf_transformation,[],[f4])).
% 0.23/0.46  fof(f4,axiom,(
% 0.23/0.46    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.23/0.46  fof(f51,plain,(
% 0.23/0.46    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.46    inference(definition_unfolding,[],[f40,f47])).
% 0.23/0.46  fof(f47,plain,(
% 0.23/0.46    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.23/0.46    inference(definition_unfolding,[],[f31,f46])).
% 0.23/0.46  fof(f46,plain,(
% 0.23/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.23/0.46    inference(definition_unfolding,[],[f34,f45])).
% 0.23/0.46  fof(f45,plain,(
% 0.23/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.23/0.46    inference(definition_unfolding,[],[f43,f44])).
% 0.23/0.46  fof(f44,plain,(
% 0.23/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f10])).
% 0.23/0.46  fof(f10,axiom,(
% 0.23/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.46  fof(f43,plain,(
% 0.23/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f9])).
% 0.23/0.46  fof(f9,axiom,(
% 0.23/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.46  fof(f34,plain,(
% 0.23/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f8])).
% 0.23/0.46  fof(f8,axiom,(
% 0.23/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.46  fof(f31,plain,(
% 0.23/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f7])).
% 0.23/0.46  fof(f7,axiom,(
% 0.23/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.46  fof(f40,plain,(
% 0.23/0.46    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f26])).
% 0.23/0.46  fof(f26,plain,(
% 0.23/0.46    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.23/0.46    inference(nnf_transformation,[],[f11])).
% 0.23/0.46  fof(f11,axiom,(
% 0.23/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.23/0.46  fof(f63,plain,(
% 0.23/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.23/0.46    inference(resolution,[],[f50,f55])).
% 0.23/0.46  fof(f55,plain,(
% 0.23/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.23/0.46    inference(resolution,[],[f37,f32])).
% 0.23/0.46  fof(f32,plain,(
% 0.23/0.46    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.23/0.46    inference(cnf_transformation,[],[f23])).
% 0.23/0.46  fof(f23,plain,(
% 0.23/0.46    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.23/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f22])).
% 0.23/0.46  fof(f22,plain,(
% 0.23/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.23/0.46    introduced(choice_axiom,[])).
% 0.23/0.46  fof(f17,plain,(
% 0.23/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.23/0.46    inference(ennf_transformation,[],[f3])).
% 0.23/0.46  fof(f3,axiom,(
% 0.23/0.46    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.23/0.46  fof(f37,plain,(
% 0.23/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f25])).
% 0.23/0.46  fof(f25,plain,(
% 0.23/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.23/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f24])).
% 0.23/0.46  fof(f24,plain,(
% 0.23/0.46    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.23/0.46    introduced(choice_axiom,[])).
% 0.23/0.46  fof(f18,plain,(
% 0.23/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.23/0.46    inference(ennf_transformation,[],[f15])).
% 0.23/0.46  fof(f15,plain,(
% 0.23/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.46    inference(rectify,[],[f2])).
% 0.23/0.46  fof(f2,axiom,(
% 0.23/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.23/0.46  fof(f50,plain,(
% 0.23/0.46    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.23/0.46    inference(definition_unfolding,[],[f38,f47])).
% 0.23/0.46  fof(f38,plain,(
% 0.23/0.46    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f19])).
% 0.23/0.46  fof(f19,plain,(
% 0.23/0.46    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.23/0.46    inference(ennf_transformation,[],[f12])).
% 0.23/0.46  fof(f12,axiom,(
% 0.23/0.46    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.23/0.46  fof(f79,plain,(
% 0.23/0.46    k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl4_2),
% 0.23/0.46    inference(avatar_component_clause,[],[f77])).
% 0.23/0.46  fof(f77,plain,(
% 0.23/0.46    spl4_2 <=> k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.23/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.46  fof(f92,plain,(
% 0.23/0.46    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl4_4),
% 0.23/0.46    inference(avatar_component_clause,[],[f90])).
% 0.23/0.46  fof(f90,plain,(
% 0.23/0.46    spl4_4 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.23/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.46  fof(f93,plain,(
% 0.23/0.46    ~spl4_4 | spl4_3),
% 0.23/0.46    inference(avatar_split_clause,[],[f87,f83,f90])).
% 0.23/0.46  fof(f83,plain,(
% 0.23/0.46    spl4_3 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.23/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.46  fof(f87,plain,(
% 0.23/0.46    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl4_3),
% 0.23/0.46    inference(forward_demodulation,[],[f85,f33])).
% 0.23/0.46  fof(f85,plain,(
% 0.23/0.46    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | spl4_3),
% 0.23/0.46    inference(avatar_component_clause,[],[f83])).
% 0.23/0.46  fof(f86,plain,(
% 0.23/0.46    ~spl4_3),
% 0.23/0.46    inference(avatar_split_clause,[],[f48,f83])).
% 0.23/0.46  fof(f48,plain,(
% 0.23/0.46    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.23/0.46    inference(definition_unfolding,[],[f29,f47,f35,f47])).
% 0.23/0.46  fof(f29,plain,(
% 0.23/0.46    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.23/0.46    inference(cnf_transformation,[],[f21])).
% 0.23/0.46  fof(f21,plain,(
% 0.23/0.46    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.23/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f20])).
% 0.23/0.46  fof(f20,plain,(
% 0.23/0.46    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 0.23/0.46    introduced(choice_axiom,[])).
% 0.23/0.46  fof(f16,plain,(
% 0.23/0.46    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.46    inference(ennf_transformation,[],[f14])).
% 0.23/0.46  fof(f14,negated_conjecture,(
% 0.23/0.46    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.46    inference(negated_conjecture,[],[f13])).
% 0.23/0.46  fof(f13,conjecture,(
% 0.23/0.46    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 0.23/0.46  fof(f80,plain,(
% 0.23/0.46    ~spl4_2 | spl4_1),
% 0.23/0.46    inference(avatar_split_clause,[],[f75,f71,f77])).
% 0.23/0.46  fof(f71,plain,(
% 0.23/0.46    spl4_1 <=> k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.23/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.46  fof(f75,plain,(
% 0.23/0.46    k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl4_1),
% 0.23/0.46    inference(forward_demodulation,[],[f73,f33])).
% 0.23/0.46  fof(f73,plain,(
% 0.23/0.46    k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) | spl4_1),
% 0.23/0.46    inference(avatar_component_clause,[],[f71])).
% 0.23/0.46  fof(f74,plain,(
% 0.23/0.46    ~spl4_1),
% 0.23/0.46    inference(avatar_split_clause,[],[f49,f71])).
% 0.23/0.46  fof(f49,plain,(
% 0.23/0.46    k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.23/0.46    inference(definition_unfolding,[],[f28,f35,f47])).
% 0.23/0.46  fof(f28,plain,(
% 0.23/0.46    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.23/0.46    inference(cnf_transformation,[],[f21])).
% 0.23/0.46  % SZS output end Proof for theBenchmark
% 0.23/0.46  % (17306)------------------------------
% 0.23/0.46  % (17306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.46  % (17306)Termination reason: Refutation
% 0.23/0.46  
% 0.23/0.46  % (17306)Memory used [KB]: 10874
% 0.23/0.46  % (17306)Time elapsed: 0.039 s
% 0.23/0.46  % (17306)------------------------------
% 0.23/0.46  % (17306)------------------------------
% 0.23/0.46  % (17290)Success in time 0.084 s
%------------------------------------------------------------------------------
