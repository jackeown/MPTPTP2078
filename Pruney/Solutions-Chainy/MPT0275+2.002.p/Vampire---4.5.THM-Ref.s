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
% DateTime   : Thu Dec  3 12:41:25 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 394 expanded)
%              Number of leaves         :   22 ( 138 expanded)
%              Depth                    :   15
%              Number of atoms          :  254 ( 646 expanded)
%              Number of equality atoms :   81 ( 355 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f857,f895,f910,f918,f924,f930,f1325,f1328,f1329])).

fof(f1329,plain,
    ( spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f903,f854,f915])).

fof(f915,plain,
    ( spl3_5
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f854,plain,
    ( spl3_2
  <=> k1_xboole_0 = k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f903,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f902,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f42,f55,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f902,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f901,f93])).

fof(f93,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f80,f70])).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f39,f43])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f80,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f38,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f901,plain,
    ( k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))))
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f61,f38])).

fof(f61,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f32,f58,f55])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f50,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f32,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f1328,plain,
    ( ~ spl3_1
    | spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f1326])).

fof(f1326,plain,
    ( $false
    | ~ spl3_1
    | spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f917,f852,f908,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f37,f55])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f908,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f907])).

fof(f907,plain,
    ( spl3_4
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f852,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f850])).

fof(f850,plain,
    ( spl3_1
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f917,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f915])).

fof(f1325,plain,
    ( ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f1319,f892,f907])).

fof(f892,plain,
    ( spl3_3
  <=> sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1319,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | spl3_3 ),
    inference(trivial_inequality_removal,[],[f1318])).

fof(f1318,plain,
    ( sK2 != sK2
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | spl3_3 ),
    inference(superposition,[],[f893,f172])).

fof(f172,plain,(
    ! [X6,X7] :
      ( k3_tarski(k3_enumset1(X7,X7,X7,X7,X6)) = X7
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f67,f65])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f893,plain,
    ( sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f892])).

fof(f930,plain,
    ( ~ spl3_5
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f928,f892,f850,f915])).

fof(f928,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f927])).

fof(f927,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f926,f44])).

fof(f926,plain,
    ( k1_xboole_0 != k5_xboole_0(sK2,sK2)
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f921,f894])).

fof(f894,plain,
    ( sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f892])).

fof(f921,plain,
    ( k1_xboole_0 != k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f920,f65])).

fof(f920,plain,
    ( k1_xboole_0 != k5_xboole_0(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f919,f93])).

fof(f919,plain,
    ( k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))))
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f59,f38])).

fof(f59,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f34,f58,f55])).

fof(f34,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f924,plain,
    ( spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f912,f907,f850])).

fof(f912,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f909,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f36,f55])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f909,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f907])).

fof(f918,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f911,f907,f915])).

fof(f911,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f909,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f35,f55])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f910,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f904,f892,f907])).

fof(f904,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f900,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f900,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | r1_tarski(X0,sK2) )
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f898,f98])).

fof(f98,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f93,f39])).

fof(f898,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))
        | r1_tarski(X0,sK2) )
    | ~ spl3_3 ),
    inference(superposition,[],[f556,f894])).

fof(f556,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))))
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f66,f38])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) ) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f895,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f878,f854,f892])).

fof(f878,plain,
    ( sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f863,f43])).

fof(f863,plain,
    ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f93,f856])).

fof(f856,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f854])).

fof(f857,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f848,f854,f850])).

fof(f848,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))
    | r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f847,f65])).

fof(f847,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))
    | r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f846,f93])).

fof(f846,plain,
    ( k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))))
    | r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f60,f38])).

fof(f60,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f33,f58,f55])).

fof(f33,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:14:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (14599)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (14612)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (14603)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (14601)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (14604)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (14602)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (14610)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (14610)Refutation not found, incomplete strategy% (14610)------------------------------
% 0.21/0.52  % (14610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14610)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14610)Memory used [KB]: 6140
% 0.21/0.52  % (14610)Time elapsed: 0.113 s
% 0.21/0.52  % (14610)------------------------------
% 0.21/0.52  % (14610)------------------------------
% 1.26/0.53  % (14613)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.26/0.53  % (14606)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.26/0.53  % (14619)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.26/0.53  % (14625)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.26/0.53  % (14627)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.26/0.53  % (14625)Refutation not found, incomplete strategy% (14625)------------------------------
% 1.26/0.53  % (14625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (14625)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (14625)Memory used [KB]: 6268
% 1.26/0.53  % (14625)Time elapsed: 0.123 s
% 1.26/0.53  % (14625)------------------------------
% 1.26/0.53  % (14625)------------------------------
% 1.26/0.53  % (14628)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.26/0.54  % (14617)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.26/0.54  % (14617)Refutation not found, incomplete strategy% (14617)------------------------------
% 1.26/0.54  % (14617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (14617)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (14617)Memory used [KB]: 1663
% 1.26/0.54  % (14617)Time elapsed: 0.134 s
% 1.26/0.54  % (14617)------------------------------
% 1.26/0.54  % (14617)------------------------------
% 1.26/0.54  % (14600)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.26/0.54  % (14628)Refutation not found, incomplete strategy% (14628)------------------------------
% 1.26/0.54  % (14628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (14628)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (14628)Memory used [KB]: 1663
% 1.26/0.54  % (14628)Time elapsed: 0.089 s
% 1.26/0.54  % (14628)------------------------------
% 1.26/0.54  % (14628)------------------------------
% 1.26/0.54  % (14621)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.42/0.55  % (14607)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.55  % (14608)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.55  % (14609)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.55  % (14626)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.55  % (14620)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.55  % (14611)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.42/0.55  % (14624)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.42/0.55  % (14615)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.55  % (14622)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.42/0.55  % (14615)Refutation not found, incomplete strategy% (14615)------------------------------
% 1.42/0.55  % (14615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (14615)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (14615)Memory used [KB]: 10618
% 1.42/0.55  % (14615)Time elapsed: 0.140 s
% 1.42/0.55  % (14615)------------------------------
% 1.42/0.55  % (14615)------------------------------
% 1.42/0.55  % (14605)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (14618)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.56  % (14623)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.56  % (14616)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.56  % (14614)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.42/0.56  % (14613)Refutation not found, incomplete strategy% (14613)------------------------------
% 1.42/0.56  % (14613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (14613)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (14613)Memory used [KB]: 1918
% 1.42/0.56  % (14613)Time elapsed: 0.126 s
% 1.42/0.56  % (14613)------------------------------
% 1.42/0.56  % (14613)------------------------------
% 1.97/0.64  % (14622)Refutation found. Thanks to Tanya!
% 1.97/0.64  % SZS status Theorem for theBenchmark
% 1.97/0.65  % (14632)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.97/0.65  % SZS output start Proof for theBenchmark
% 1.97/0.65  fof(f1330,plain,(
% 1.97/0.65    $false),
% 1.97/0.65    inference(avatar_sat_refutation,[],[f857,f895,f910,f918,f924,f930,f1325,f1328,f1329])).
% 1.97/0.65  fof(f1329,plain,(
% 1.97/0.65    spl3_5 | spl3_2),
% 1.97/0.65    inference(avatar_split_clause,[],[f903,f854,f915])).
% 1.97/0.65  fof(f915,plain,(
% 1.97/0.65    spl3_5 <=> r2_hidden(sK0,sK2)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.97/0.65  fof(f854,plain,(
% 1.97/0.65    spl3_2 <=> k1_xboole_0 = k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.97/0.65  fof(f903,plain,(
% 1.97/0.65    k1_xboole_0 = k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) | r2_hidden(sK0,sK2)),
% 1.97/0.65    inference(forward_demodulation,[],[f902,f65])).
% 1.97/0.65  fof(f65,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.97/0.65    inference(definition_unfolding,[],[f42,f55,f55])).
% 1.97/0.65  fof(f55,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.97/0.65    inference(definition_unfolding,[],[f41,f54])).
% 1.97/0.65  fof(f54,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.97/0.65    inference(definition_unfolding,[],[f51,f53])).
% 1.97/0.65  fof(f53,plain,(
% 1.97/0.65    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f13])).
% 1.97/0.65  fof(f13,axiom,(
% 1.97/0.65    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.97/0.65  fof(f51,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f12])).
% 1.97/0.65  fof(f12,axiom,(
% 1.97/0.65    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.97/0.65  fof(f41,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f11])).
% 1.97/0.65  fof(f11,axiom,(
% 1.97/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.97/0.65  fof(f42,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f10])).
% 1.97/0.65  fof(f10,axiom,(
% 1.97/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.97/0.65  fof(f902,plain,(
% 1.97/0.65    k1_xboole_0 = k5_xboole_0(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))) | r2_hidden(sK0,sK2)),
% 1.97/0.65    inference(forward_demodulation,[],[f901,f93])).
% 1.97/0.65  fof(f93,plain,(
% 1.97/0.65    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 1.97/0.65    inference(forward_demodulation,[],[f80,f70])).
% 1.97/0.65  fof(f70,plain,(
% 1.97/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.97/0.65    inference(superposition,[],[f39,f43])).
% 1.97/0.65  fof(f43,plain,(
% 1.97/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.97/0.65    inference(cnf_transformation,[],[f6])).
% 1.97/0.65  fof(f6,axiom,(
% 1.97/0.65    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.97/0.65  fof(f39,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f1])).
% 1.97/0.65  fof(f1,axiom,(
% 1.97/0.65    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.97/0.65  fof(f80,plain,(
% 1.97/0.65    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 1.97/0.65    inference(superposition,[],[f38,f44])).
% 1.97/0.65  fof(f44,plain,(
% 1.97/0.65    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f8])).
% 1.97/0.65  fof(f8,axiom,(
% 1.97/0.65    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.97/0.65  fof(f38,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.97/0.65    inference(cnf_transformation,[],[f7])).
% 1.97/0.65  fof(f7,axiom,(
% 1.97/0.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.97/0.65  fof(f901,plain,(
% 1.97/0.65    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))))) | r2_hidden(sK0,sK2)),
% 1.97/0.65    inference(forward_demodulation,[],[f61,f38])).
% 1.97/0.65  fof(f61,plain,(
% 1.97/0.65    r2_hidden(sK0,sK2) | k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))))),
% 1.97/0.65    inference(definition_unfolding,[],[f32,f58,f55])).
% 1.97/0.65  fof(f58,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) )),
% 1.97/0.65    inference(definition_unfolding,[],[f40,f57])).
% 1.97/0.65  fof(f57,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.97/0.65    inference(definition_unfolding,[],[f50,f56])).
% 1.97/0.65  fof(f56,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.97/0.65    inference(definition_unfolding,[],[f52,f55])).
% 1.97/0.65  fof(f52,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.97/0.65    inference(cnf_transformation,[],[f17])).
% 1.97/0.65  fof(f17,axiom,(
% 1.97/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.97/0.65  fof(f50,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.97/0.65    inference(cnf_transformation,[],[f9])).
% 1.97/0.65  fof(f9,axiom,(
% 1.97/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.97/0.65  fof(f40,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.97/0.65    inference(cnf_transformation,[],[f3])).
% 1.97/0.65  fof(f3,axiom,(
% 1.97/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.97/0.65  fof(f32,plain,(
% 1.97/0.65    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.97/0.65    inference(cnf_transformation,[],[f27])).
% 1.97/0.66  fof(f27,plain,(
% 1.97/0.66    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 1.97/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).
% 1.97/0.66  fof(f26,plain,(
% 1.97/0.66    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 1.97/0.66    introduced(choice_axiom,[])).
% 1.97/0.66  fof(f25,plain,(
% 1.97/0.66    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.97/0.66    inference(flattening,[],[f24])).
% 1.97/0.66  fof(f24,plain,(
% 1.97/0.66    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.97/0.66    inference(nnf_transformation,[],[f21])).
% 1.97/0.66  fof(f21,plain,(
% 1.97/0.66    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.97/0.66    inference(ennf_transformation,[],[f20])).
% 1.97/0.66  fof(f20,negated_conjecture,(
% 1.97/0.66    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.97/0.66    inference(negated_conjecture,[],[f19])).
% 1.97/0.66  fof(f19,conjecture,(
% 1.97/0.66    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 1.97/0.66  fof(f1328,plain,(
% 1.97/0.66    ~spl3_1 | spl3_4 | ~spl3_5),
% 1.97/0.66    inference(avatar_contradiction_clause,[],[f1326])).
% 1.97/0.66  fof(f1326,plain,(
% 1.97/0.66    $false | (~spl3_1 | spl3_4 | ~spl3_5)),
% 1.97/0.66    inference(unit_resulting_resolution,[],[f917,f852,f908,f62])).
% 1.97/0.66  fof(f62,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.97/0.66    inference(definition_unfolding,[],[f37,f55])).
% 1.97/0.66  fof(f37,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f29])).
% 1.97/0.66  fof(f29,plain,(
% 1.97/0.66    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.97/0.66    inference(flattening,[],[f28])).
% 1.97/0.66  fof(f28,plain,(
% 1.97/0.66    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.97/0.66    inference(nnf_transformation,[],[f18])).
% 1.97/0.66  fof(f18,axiom,(
% 1.97/0.66    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.97/0.66  fof(f908,plain,(
% 1.97/0.66    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | spl3_4),
% 1.97/0.66    inference(avatar_component_clause,[],[f907])).
% 1.97/0.66  fof(f907,plain,(
% 1.97/0.66    spl3_4 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),
% 1.97/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.97/0.66  fof(f852,plain,(
% 1.97/0.66    r2_hidden(sK1,sK2) | ~spl3_1),
% 1.97/0.66    inference(avatar_component_clause,[],[f850])).
% 1.97/0.66  fof(f850,plain,(
% 1.97/0.66    spl3_1 <=> r2_hidden(sK1,sK2)),
% 1.97/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.97/0.66  fof(f917,plain,(
% 1.97/0.66    r2_hidden(sK0,sK2) | ~spl3_5),
% 1.97/0.66    inference(avatar_component_clause,[],[f915])).
% 1.97/0.66  fof(f1325,plain,(
% 1.97/0.66    ~spl3_4 | spl3_3),
% 1.97/0.66    inference(avatar_split_clause,[],[f1319,f892,f907])).
% 1.97/0.66  fof(f892,plain,(
% 1.97/0.66    spl3_3 <=> sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 1.97/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.97/0.66  fof(f1319,plain,(
% 1.97/0.66    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | spl3_3),
% 1.97/0.66    inference(trivial_inequality_removal,[],[f1318])).
% 1.97/0.66  fof(f1318,plain,(
% 1.97/0.66    sK2 != sK2 | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | spl3_3),
% 1.97/0.66    inference(superposition,[],[f893,f172])).
% 1.97/0.66  fof(f172,plain,(
% 1.97/0.66    ( ! [X6,X7] : (k3_tarski(k3_enumset1(X7,X7,X7,X7,X6)) = X7 | ~r1_tarski(X6,X7)) )),
% 1.97/0.66    inference(superposition,[],[f67,f65])).
% 1.97/0.66  fof(f67,plain,(
% 1.97/0.66    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.97/0.66    inference(definition_unfolding,[],[f49,f56])).
% 1.97/0.66  fof(f49,plain,(
% 1.97/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f23])).
% 1.97/0.66  fof(f23,plain,(
% 1.97/0.66    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.97/0.66    inference(ennf_transformation,[],[f4])).
% 1.97/0.66  fof(f4,axiom,(
% 1.97/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.97/0.66  fof(f893,plain,(
% 1.97/0.66    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl3_3),
% 1.97/0.66    inference(avatar_component_clause,[],[f892])).
% 1.97/0.66  fof(f930,plain,(
% 1.97/0.66    ~spl3_5 | ~spl3_1 | ~spl3_3),
% 1.97/0.66    inference(avatar_split_clause,[],[f928,f892,f850,f915])).
% 1.97/0.66  fof(f928,plain,(
% 1.97/0.66    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~spl3_3),
% 1.97/0.66    inference(trivial_inequality_removal,[],[f927])).
% 1.97/0.66  fof(f927,plain,(
% 1.97/0.66    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~spl3_3),
% 1.97/0.66    inference(forward_demodulation,[],[f926,f44])).
% 1.97/0.66  fof(f926,plain,(
% 1.97/0.66    k1_xboole_0 != k5_xboole_0(sK2,sK2) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~spl3_3),
% 1.97/0.66    inference(forward_demodulation,[],[f921,f894])).
% 1.97/0.66  fof(f894,plain,(
% 1.97/0.66    sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl3_3),
% 1.97/0.66    inference(avatar_component_clause,[],[f892])).
% 1.97/0.66  fof(f921,plain,(
% 1.97/0.66    k1_xboole_0 != k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2)),
% 1.97/0.66    inference(forward_demodulation,[],[f920,f65])).
% 1.97/0.66  fof(f920,plain,(
% 1.97/0.66    k1_xboole_0 != k5_xboole_0(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2)),
% 1.97/0.66    inference(forward_demodulation,[],[f919,f93])).
% 1.97/0.66  fof(f919,plain,(
% 1.97/0.66    k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))))) | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2)),
% 1.97/0.66    inference(forward_demodulation,[],[f59,f38])).
% 1.97/0.66  fof(f59,plain,(
% 1.97/0.66    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))))),
% 1.97/0.66    inference(definition_unfolding,[],[f34,f58,f55])).
% 1.97/0.66  fof(f34,plain,(
% 1.97/0.66    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.97/0.66    inference(cnf_transformation,[],[f27])).
% 1.97/0.66  fof(f924,plain,(
% 1.97/0.66    spl3_1 | ~spl3_4),
% 1.97/0.66    inference(avatar_split_clause,[],[f912,f907,f850])).
% 1.97/0.66  fof(f912,plain,(
% 1.97/0.66    r2_hidden(sK1,sK2) | ~spl3_4),
% 1.97/0.66    inference(resolution,[],[f909,f63])).
% 1.97/0.66  fof(f63,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.97/0.66    inference(definition_unfolding,[],[f36,f55])).
% 1.97/0.66  fof(f36,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f29])).
% 1.97/0.66  fof(f909,plain,(
% 1.97/0.66    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_4),
% 1.97/0.66    inference(avatar_component_clause,[],[f907])).
% 1.97/0.66  fof(f918,plain,(
% 1.97/0.66    spl3_5 | ~spl3_4),
% 1.97/0.66    inference(avatar_split_clause,[],[f911,f907,f915])).
% 1.97/0.66  fof(f911,plain,(
% 1.97/0.66    r2_hidden(sK0,sK2) | ~spl3_4),
% 1.97/0.66    inference(resolution,[],[f909,f64])).
% 1.97/0.66  fof(f64,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.97/0.66    inference(definition_unfolding,[],[f35,f55])).
% 1.97/0.66  fof(f35,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.97/0.66    inference(cnf_transformation,[],[f29])).
% 1.97/0.66  fof(f910,plain,(
% 1.97/0.66    spl3_4 | ~spl3_3),
% 1.97/0.66    inference(avatar_split_clause,[],[f904,f892,f907])).
% 1.97/0.66  fof(f904,plain,(
% 1.97/0.66    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_3),
% 1.97/0.66    inference(resolution,[],[f900,f68])).
% 1.97/0.66  fof(f68,plain,(
% 1.97/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.97/0.66    inference(equality_resolution,[],[f47])).
% 1.97/0.66  fof(f47,plain,(
% 1.97/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.97/0.66    inference(cnf_transformation,[],[f31])).
% 1.97/0.66  fof(f31,plain,(
% 1.97/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.97/0.66    inference(flattening,[],[f30])).
% 1.97/0.66  fof(f30,plain,(
% 1.97/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.97/0.66    inference(nnf_transformation,[],[f2])).
% 1.97/0.66  fof(f2,axiom,(
% 1.97/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.97/0.66  fof(f900,plain,(
% 1.97/0.66    ( ! [X0] : (~r1_tarski(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | r1_tarski(X0,sK2)) ) | ~spl3_3),
% 1.97/0.66    inference(forward_demodulation,[],[f898,f98])).
% 1.97/0.66  fof(f98,plain,(
% 1.97/0.66    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.97/0.66    inference(superposition,[],[f93,f39])).
% 1.97/0.66  fof(f898,plain,(
% 1.97/0.66    ( ! [X0] : (~r1_tarski(X0,k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))) | r1_tarski(X0,sK2)) ) | ~spl3_3),
% 1.97/0.66    inference(superposition,[],[f556,f894])).
% 1.97/0.66  fof(f556,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))))) | r1_tarski(X0,X1)) )),
% 1.97/0.66    inference(forward_demodulation,[],[f66,f38])).
% 1.97/0.66  fof(f66,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))))) )),
% 1.97/0.66    inference(definition_unfolding,[],[f45,f57])).
% 1.97/0.66  fof(f45,plain,(
% 1.97/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.97/0.66    inference(cnf_transformation,[],[f22])).
% 1.97/0.66  fof(f22,plain,(
% 1.97/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.97/0.66    inference(ennf_transformation,[],[f5])).
% 1.97/0.66  fof(f5,axiom,(
% 1.97/0.66    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.97/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 1.97/0.66  fof(f895,plain,(
% 1.97/0.66    spl3_3 | ~spl3_2),
% 1.97/0.66    inference(avatar_split_clause,[],[f878,f854,f892])).
% 1.97/0.66  fof(f878,plain,(
% 1.97/0.66    sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl3_2),
% 1.97/0.66    inference(forward_demodulation,[],[f863,f43])).
% 1.97/0.66  fof(f863,plain,(
% 1.97/0.66    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(sK2,k1_xboole_0) | ~spl3_2),
% 1.97/0.66    inference(superposition,[],[f93,f856])).
% 1.97/0.66  fof(f856,plain,(
% 1.97/0.66    k1_xboole_0 = k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) | ~spl3_2),
% 1.97/0.66    inference(avatar_component_clause,[],[f854])).
% 1.97/0.66  fof(f857,plain,(
% 1.97/0.66    spl3_1 | spl3_2),
% 1.97/0.66    inference(avatar_split_clause,[],[f848,f854,f850])).
% 1.97/0.66  fof(f848,plain,(
% 1.97/0.66    k1_xboole_0 = k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) | r2_hidden(sK1,sK2)),
% 1.97/0.66    inference(forward_demodulation,[],[f847,f65])).
% 1.97/0.66  fof(f847,plain,(
% 1.97/0.66    k1_xboole_0 = k5_xboole_0(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))) | r2_hidden(sK1,sK2)),
% 1.97/0.66    inference(forward_demodulation,[],[f846,f93])).
% 1.97/0.66  fof(f846,plain,(
% 1.97/0.66    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))))) | r2_hidden(sK1,sK2)),
% 1.97/0.66    inference(forward_demodulation,[],[f60,f38])).
% 1.97/0.66  fof(f60,plain,(
% 1.97/0.66    r2_hidden(sK1,sK2) | k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))))),
% 1.97/0.66    inference(definition_unfolding,[],[f33,f58,f55])).
% 1.97/0.66  fof(f33,plain,(
% 1.97/0.66    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.97/0.66    inference(cnf_transformation,[],[f27])).
% 1.97/0.66  % SZS output end Proof for theBenchmark
% 1.97/0.66  % (14622)------------------------------
% 1.97/0.66  % (14622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.66  % (14622)Termination reason: Refutation
% 1.97/0.66  
% 1.97/0.66  % (14622)Memory used [KB]: 12025
% 1.97/0.66  % (14622)Time elapsed: 0.238 s
% 1.97/0.66  % (14622)------------------------------
% 1.97/0.66  % (14622)------------------------------
% 1.97/0.66  % (14598)Success in time 0.291 s
%------------------------------------------------------------------------------
