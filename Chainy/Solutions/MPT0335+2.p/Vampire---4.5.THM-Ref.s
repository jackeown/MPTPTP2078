%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0335+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:24 EST 2020

% Result     : Theorem 8.28s
% Output     : Refutation 8.28s
% Verified   : 
% Statistics : Number of formulae       :   47 (  87 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 236 expanded)
%              Number of equality atoms :   41 ( 110 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2081,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1231,f1236,f1367,f1372,f1788,f1988])).

fof(f1988,plain,
    ( ~ spl20_2
    | spl20_3
    | ~ spl20_4
    | ~ spl20_8 ),
    inference(avatar_contradiction_clause,[],[f1987])).

fof(f1987,plain,
    ( $false
    | ~ spl20_2
    | spl20_3
    | ~ spl20_4
    | ~ spl20_8 ),
    inference(subsumption_resolution,[],[f1985,f1378])).

fof(f1378,plain,
    ( k3_xboole_0(sK0,sK2) != k3_xboole_0(sK1,sK2)
    | spl20_3
    | ~ spl20_4 ),
    inference(superposition,[],[f1366,f1371])).

fof(f1371,plain,
    ( k3_xboole_0(sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3)
    | ~ spl20_4 ),
    inference(avatar_component_clause,[],[f1369])).

fof(f1369,plain,
    ( spl20_4
  <=> k3_xboole_0(sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_4])])).

fof(f1366,plain,
    ( k3_xboole_0(sK0,sK2) != k2_enumset1(sK3,sK3,sK3,sK3)
    | spl20_3 ),
    inference(avatar_component_clause,[],[f1364])).

fof(f1364,plain,
    ( spl20_3
  <=> k3_xboole_0(sK0,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_3])])).

fof(f1985,plain,
    ( k3_xboole_0(sK0,sK2) = k3_xboole_0(sK1,sK2)
    | ~ spl20_2
    | ~ spl20_8 ),
    inference(backward_demodulation,[],[f1352,f1917])).

fof(f1917,plain,
    ( ! [X14] : k3_xboole_0(sK0,X14) = k3_xboole_0(sK0,k3_xboole_0(sK1,X14))
    | ~ spl20_8 ),
    inference(superposition,[],[f910,f1787])).

fof(f1787,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl20_8 ),
    inference(avatar_component_clause,[],[f1785])).

fof(f1785,plain,
    ( spl20_8
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_8])])).

fof(f910,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f1352,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl20_2 ),
    inference(forward_demodulation,[],[f1295,f983])).

fof(f983,plain,(
    k3_xboole_0(sK1,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f675,f874])).

fof(f874,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f267])).

fof(f267,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f675,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f584])).

fof(f584,plain,
    ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f450,f583])).

fof(f583,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f450,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f449])).

fof(f449,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f364])).

fof(f364,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f363])).

fof(f363,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f1295,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k3_xboole_0(sK0,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl20_2 ),
    inference(resolution,[],[f1235,f1063])).

fof(f1063,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(definition_unfolding,[],[f785,f874,f874])).

fof(f785,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f485])).

fof(f485,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f307])).

fof(f307,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f1235,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl20_2 ),
    inference(avatar_component_clause,[],[f1233])).

fof(f1233,plain,
    ( spl20_2
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_2])])).

fof(f1788,plain,
    ( spl20_8
    | ~ spl20_1 ),
    inference(avatar_split_clause,[],[f1246,f1228,f1785])).

fof(f1228,plain,
    ( spl20_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_1])])).

fof(f1246,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl20_1 ),
    inference(resolution,[],[f1230,f916])).

fof(f916,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f540])).

fof(f540,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1230,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl20_1 ),
    inference(avatar_component_clause,[],[f1228])).

fof(f1372,plain,(
    spl20_4 ),
    inference(avatar_split_clause,[],[f983,f1369])).

fof(f1367,plain,(
    ~ spl20_3 ),
    inference(avatar_split_clause,[],[f982,f1364])).

fof(f982,plain,(
    k3_xboole_0(sK0,sK2) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f677,f874])).

fof(f677,plain,(
    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f584])).

fof(f1236,plain,(
    spl20_2 ),
    inference(avatar_split_clause,[],[f676,f1233])).

fof(f676,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f584])).

fof(f1231,plain,(
    spl20_1 ),
    inference(avatar_split_clause,[],[f674,f1228])).

fof(f674,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f584])).
%------------------------------------------------------------------------------
