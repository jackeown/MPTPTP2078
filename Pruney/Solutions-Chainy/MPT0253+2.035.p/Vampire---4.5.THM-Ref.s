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
% DateTime   : Thu Dec  3 12:39:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 682 expanded)
%              Number of leaves         :   19 ( 181 expanded)
%              Depth                    :   17
%              Number of atoms          :  165 (1365 expanded)
%              Number of equality atoms :   66 ( 719 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f825,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f76,f657,f740,f824])).

fof(f824,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f822])).

fof(f822,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f64,f69,f739,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f739,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f737])).

fof(f737,plain,
    ( spl3_9
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f69,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f64,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f740,plain,
    ( ~ spl3_9
    | spl3_7 ),
    inference(avatar_split_clause,[],[f735,f653,f737])).

fof(f653,plain,
    ( spl3_7
  <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f735,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | spl3_7 ),
    inference(trivial_inequality_removal,[],[f734])).

fof(f734,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | spl3_7 ),
    inference(forward_demodulation,[],[f733,f370])).

fof(f370,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X2)) = X3 ),
    inference(superposition,[],[f284,f155])).

fof(f155,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f144,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f144,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f88,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(global_subsumption,[],[f59,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f57,f40])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f88,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k5_xboole_0(X5,X6)) = k5_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f41,f81])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f284,plain,(
    ! [X4,X5] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X5,k5_xboole_0(X4,X5))) = X4 ),
    inference(forward_demodulation,[],[f256,f42])).

fof(f256,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X5,k5_xboole_0(X4,X5))) ),
    inference(superposition,[],[f88,f92])).

fof(f92,plain,(
    ! [X8,X9] : k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(X8,X9))) ),
    inference(superposition,[],[f41,f81])).

fof(f733,plain,
    ( sK1 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | spl3_7 ),
    inference(forward_demodulation,[],[f728,f490])).

fof(f490,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(forward_demodulation,[],[f469,f155])).

fof(f469,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X9),X8) ),
    inference(superposition,[],[f418,f88])).

fof(f418,plain,(
    ! [X12,X13] : k5_xboole_0(k5_xboole_0(X13,X12),X13) = X12 ),
    inference(superposition,[],[f370,f370])).

fof(f728,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | spl3_7 ),
    inference(superposition,[],[f655,f314])).

fof(f314,plain,(
    ! [X6,X7] :
      ( k3_xboole_0(X7,X6) = X6
      | ~ r1_tarski(X6,X7) ) ),
    inference(forward_demodulation,[],[f313,f42])).

fof(f313,plain,(
    ! [X6,X7] :
      ( k5_xboole_0(X6,k1_xboole_0) = k3_xboole_0(X7,X6)
      | ~ r1_tarski(X6,X7) ) ),
    inference(forward_demodulation,[],[f303,f155])).

fof(f303,plain,(
    ! [X6,X7] :
      ( k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X7,X6))
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f88,f79])).

fof(f79,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X2,X1))
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f57,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f655,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f653])).

fof(f657,plain,
    ( ~ spl3_7
    | spl3_3 ),
    inference(avatar_split_clause,[],[f582,f73,f653])).

fof(f73,plain,
    ( spl3_3
  <=> sK1 = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f582,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))
    | spl3_3 ),
    inference(superposition,[],[f75,f490])).

fof(f75,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f76,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f71,f73])).

fof(f71,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) ),
    inference(forward_demodulation,[],[f52,f39])).

fof(f52,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f31,f32,f51])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f31,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f70,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:00:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (21924)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (21930)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (21946)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.51  % (21926)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (21923)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (21925)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (21948)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (21932)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (21948)Refutation not found, incomplete strategy% (21948)------------------------------
% 0.22/0.52  % (21948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21938)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (21932)Refutation not found, incomplete strategy% (21932)------------------------------
% 0.22/0.52  % (21932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21948)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21948)Memory used [KB]: 6268
% 0.22/0.52  % (21948)Time elapsed: 0.109 s
% 0.22/0.52  % (21948)------------------------------
% 0.22/0.52  % (21948)------------------------------
% 0.22/0.52  % (21935)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (21950)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (21932)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21932)Memory used [KB]: 10746
% 0.22/0.52  % (21932)Time elapsed: 0.109 s
% 0.22/0.52  % (21932)------------------------------
% 0.22/0.52  % (21932)------------------------------
% 0.22/0.53  % (21928)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (21942)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (21946)Refutation not found, incomplete strategy% (21946)------------------------------
% 0.22/0.53  % (21946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21936)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (21938)Refutation not found, incomplete strategy% (21938)------------------------------
% 0.22/0.53  % (21938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21946)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21946)Memory used [KB]: 10618
% 0.22/0.53  % (21946)Time elapsed: 0.114 s
% 0.22/0.53  % (21946)------------------------------
% 0.22/0.53  % (21946)------------------------------
% 0.22/0.53  % (21936)Refutation not found, incomplete strategy% (21936)------------------------------
% 0.22/0.53  % (21936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21936)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21936)Memory used [KB]: 1663
% 0.22/0.53  % (21936)Time elapsed: 0.086 s
% 0.22/0.53  % (21936)------------------------------
% 0.22/0.53  % (21936)------------------------------
% 0.22/0.53  % (21937)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (21938)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21938)Memory used [KB]: 10618
% 0.22/0.53  % (21938)Time elapsed: 0.115 s
% 0.22/0.53  % (21938)------------------------------
% 0.22/0.53  % (21938)------------------------------
% 0.22/0.54  % (21944)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (21934)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (21943)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (21923)Refutation not found, incomplete strategy% (21923)------------------------------
% 0.22/0.54  % (21923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21923)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21923)Memory used [KB]: 1663
% 0.22/0.54  % (21923)Time elapsed: 0.106 s
% 0.22/0.54  % (21923)------------------------------
% 0.22/0.54  % (21923)------------------------------
% 0.22/0.54  % (21927)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (21945)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (21947)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (21922)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (21941)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (21947)Refutation not found, incomplete strategy% (21947)------------------------------
% 0.22/0.54  % (21947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21947)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21947)Memory used [KB]: 6268
% 0.22/0.54  % (21947)Time elapsed: 0.129 s
% 0.22/0.54  % (21947)------------------------------
% 0.22/0.54  % (21947)------------------------------
% 0.22/0.54  % (21950)Refutation not found, incomplete strategy% (21950)------------------------------
% 0.22/0.54  % (21950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21950)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21950)Memory used [KB]: 10746
% 0.22/0.54  % (21950)Time elapsed: 0.144 s
% 0.22/0.54  % (21950)------------------------------
% 0.22/0.54  % (21950)------------------------------
% 0.22/0.55  % (21939)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (21949)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (21940)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (21949)Refutation not found, incomplete strategy% (21949)------------------------------
% 0.22/0.55  % (21949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21949)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21949)Memory used [KB]: 6140
% 0.22/0.55  % (21949)Time elapsed: 0.138 s
% 0.22/0.55  % (21949)------------------------------
% 0.22/0.55  % (21949)------------------------------
% 0.22/0.55  % (21940)Refutation not found, incomplete strategy% (21940)------------------------------
% 0.22/0.55  % (21940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21940)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21940)Memory used [KB]: 1663
% 0.22/0.55  % (21940)Time elapsed: 0.138 s
% 0.22/0.55  % (21940)------------------------------
% 0.22/0.55  % (21940)------------------------------
% 0.22/0.55  % (21933)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (21929)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (21931)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (21934)Refutation not found, incomplete strategy% (21934)------------------------------
% 0.22/0.55  % (21934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21934)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21934)Memory used [KB]: 10746
% 0.22/0.55  % (21934)Time elapsed: 0.135 s
% 0.22/0.55  % (21934)------------------------------
% 0.22/0.55  % (21934)------------------------------
% 0.22/0.55  % (21951)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (21951)Refutation not found, incomplete strategy% (21951)------------------------------
% 0.22/0.55  % (21951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21951)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21951)Memory used [KB]: 1663
% 0.22/0.55  % (21951)Time elapsed: 0.141 s
% 0.22/0.55  % (21951)------------------------------
% 0.22/0.55  % (21951)------------------------------
% 0.22/0.59  % (21945)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f825,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(avatar_sat_refutation,[],[f65,f70,f76,f657,f740,f824])).
% 0.22/0.59  fof(f824,plain,(
% 0.22/0.59    ~spl3_1 | ~spl3_2 | spl3_9),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f822])).
% 0.22/0.59  fof(f822,plain,(
% 0.22/0.59    $false | (~spl3_1 | ~spl3_2 | spl3_9)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f64,f69,f739,f54])).
% 0.22/0.59  fof(f54,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f36,f51])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f37,f50])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f48,f49])).
% 0.22/0.59  fof(f49,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f9])).
% 0.22/0.59  fof(f9,axiom,(
% 0.22/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.59    inference(flattening,[],[f24])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.59    inference(nnf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.59  fof(f739,plain,(
% 0.22/0.59    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | spl3_9),
% 0.22/0.59    inference(avatar_component_clause,[],[f737])).
% 0.22/0.59  fof(f737,plain,(
% 0.22/0.59    spl3_9 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.59  fof(f69,plain,(
% 0.22/0.59    r2_hidden(sK2,sK1) | ~spl3_2),
% 0.22/0.59    inference(avatar_component_clause,[],[f67])).
% 0.22/0.59  fof(f67,plain,(
% 0.22/0.59    spl3_2 <=> r2_hidden(sK2,sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.59  fof(f64,plain,(
% 0.22/0.59    r2_hidden(sK0,sK1) | ~spl3_1),
% 0.22/0.59    inference(avatar_component_clause,[],[f62])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    spl3_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.59  fof(f740,plain,(
% 0.22/0.59    ~spl3_9 | spl3_7),
% 0.22/0.59    inference(avatar_split_clause,[],[f735,f653,f737])).
% 0.22/0.59  fof(f653,plain,(
% 0.22/0.59    spl3_7 <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.59  fof(f735,plain,(
% 0.22/0.59    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | spl3_7),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f734])).
% 0.22/0.59  fof(f734,plain,(
% 0.22/0.59    sK1 != sK1 | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | spl3_7),
% 0.22/0.59    inference(forward_demodulation,[],[f733,f370])).
% 0.22/0.59  fof(f370,plain,(
% 0.22/0.59    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X2)) = X3) )),
% 0.22/0.59    inference(superposition,[],[f284,f155])).
% 0.22/0.59  fof(f155,plain,(
% 0.22/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.59    inference(forward_demodulation,[],[f144,f42])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.59  fof(f144,plain,(
% 0.22/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.59    inference(superposition,[],[f88,f81])).
% 0.22/0.59  fof(f81,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.59    inference(global_subsumption,[],[f59,f78])).
% 0.22/0.59  fof(f78,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 0.22/0.59    inference(superposition,[],[f57,f40])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f19])).
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.59    inference(rectify,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f44,f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.59    inference(nnf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.59    inference(equality_resolution,[],[f46])).
% 0.22/0.59  fof(f46,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.59    inference(cnf_transformation,[],[f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.59    inference(flattening,[],[f27])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.59    inference(nnf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.59  fof(f88,plain,(
% 0.22/0.59    ( ! [X6,X5] : (k5_xboole_0(X5,k5_xboole_0(X5,X6)) = k5_xboole_0(k1_xboole_0,X6)) )),
% 0.22/0.59    inference(superposition,[],[f41,f81])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.59  fof(f284,plain,(
% 0.22/0.59    ( ! [X4,X5] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X5,k5_xboole_0(X4,X5))) = X4) )),
% 0.22/0.59    inference(forward_demodulation,[],[f256,f42])).
% 0.22/0.59  fof(f256,plain,(
% 0.22/0.59    ( ! [X4,X5] : (k5_xboole_0(X4,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X5,k5_xboole_0(X4,X5)))) )),
% 0.22/0.59    inference(superposition,[],[f88,f92])).
% 0.22/0.59  fof(f92,plain,(
% 0.22/0.59    ( ! [X8,X9] : (k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(X8,X9)))) )),
% 0.22/0.59    inference(superposition,[],[f41,f81])).
% 0.22/0.59  fof(f733,plain,(
% 0.22/0.59    sK1 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | spl3_7),
% 0.22/0.59    inference(forward_demodulation,[],[f728,f490])).
% 0.22/0.59  fof(f490,plain,(
% 0.22/0.59    ( ! [X8,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f469,f155])).
% 0.22/0.59  fof(f469,plain,(
% 0.22/0.59    ( ! [X8,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X9),X8)) )),
% 0.22/0.59    inference(superposition,[],[f418,f88])).
% 0.22/0.59  fof(f418,plain,(
% 0.22/0.59    ( ! [X12,X13] : (k5_xboole_0(k5_xboole_0(X13,X12),X13) = X12) )),
% 0.22/0.59    inference(superposition,[],[f370,f370])).
% 0.22/0.59  fof(f728,plain,(
% 0.22/0.59    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | spl3_7),
% 0.22/0.59    inference(superposition,[],[f655,f314])).
% 0.22/0.59  fof(f314,plain,(
% 0.22/0.59    ( ! [X6,X7] : (k3_xboole_0(X7,X6) = X6 | ~r1_tarski(X6,X7)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f313,f42])).
% 0.22/0.59  fof(f313,plain,(
% 0.22/0.59    ( ! [X6,X7] : (k5_xboole_0(X6,k1_xboole_0) = k3_xboole_0(X7,X6) | ~r1_tarski(X6,X7)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f303,f155])).
% 0.22/0.59  fof(f303,plain,(
% 0.22/0.59    ( ! [X6,X7] : (k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X7,X6)) | ~r1_tarski(X6,X7)) )),
% 0.22/0.59    inference(superposition,[],[f88,f79])).
% 0.22/0.59  fof(f79,plain,(
% 0.22/0.59    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X2,X1)) | ~r1_tarski(X1,X2)) )),
% 0.22/0.59    inference(superposition,[],[f57,f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.59  fof(f655,plain,(
% 0.22/0.59    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) | spl3_7),
% 0.22/0.59    inference(avatar_component_clause,[],[f653])).
% 0.22/0.59  fof(f657,plain,(
% 0.22/0.59    ~spl3_7 | spl3_3),
% 0.22/0.59    inference(avatar_split_clause,[],[f582,f73,f653])).
% 0.22/0.59  fof(f73,plain,(
% 0.22/0.59    spl3_3 <=> sK1 = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.59  fof(f582,plain,(
% 0.22/0.59    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) | spl3_3),
% 0.22/0.59    inference(superposition,[],[f75,f490])).
% 0.22/0.59  fof(f75,plain,(
% 0.22/0.59    sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) | spl3_3),
% 0.22/0.59    inference(avatar_component_clause,[],[f73])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    ~spl3_3),
% 0.22/0.59    inference(avatar_split_clause,[],[f71,f73])).
% 0.22/0.59  fof(f71,plain,(
% 0.22/0.59    sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),
% 0.22/0.59    inference(forward_demodulation,[],[f52,f39])).
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1))),
% 0.22/0.59    inference(definition_unfolding,[],[f31,f32,f51])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f23])).
% 0.22/0.59  fof(f23,plain,(
% 0.22/0.59    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 0.22/0.59    inference(flattening,[],[f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 0.22/0.59    inference(ennf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.22/0.59    inference(negated_conjecture,[],[f17])).
% 0.22/0.59  fof(f17,conjecture,(
% 0.22/0.59    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 0.22/0.59  fof(f70,plain,(
% 0.22/0.59    spl3_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f30,f67])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    r2_hidden(sK2,sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f23])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    spl3_1),
% 0.22/0.59    inference(avatar_split_clause,[],[f29,f62])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    r2_hidden(sK0,sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f23])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (21945)------------------------------
% 0.22/0.59  % (21945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (21945)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (21945)Memory used [KB]: 11257
% 0.22/0.59  % (21945)Time elapsed: 0.164 s
% 0.22/0.59  % (21945)------------------------------
% 0.22/0.59  % (21945)------------------------------
% 0.22/0.59  % (21921)Success in time 0.224 s
%------------------------------------------------------------------------------
