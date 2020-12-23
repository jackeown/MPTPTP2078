%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:27 EST 2020

% Result     : Theorem 21.12s
% Output     : Refutation 21.12s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 432 expanded)
%              Number of leaves         :   26 ( 141 expanded)
%              Depth                    :   14
%              Number of atoms          :  455 (1369 expanded)
%              Number of equality atoms :  196 ( 652 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15765,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f112,f113,f13047,f13317,f13318,f13401,f13432,f13433,f14193,f15764])).

fof(f15764,plain,
    ( spl5_1
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f15763])).

fof(f15763,plain,
    ( $false
    | spl5_1
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f15759,f102])).

fof(f102,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_1
  <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f15759,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ spl5_13 ),
    inference(resolution,[],[f13009,f1664])).

fof(f1664,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X0),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(subsumption_resolution,[],[f1645,f962])).

fof(f962,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(duplicate_literal_removal,[],[f953])).

fof(f953,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | r2_hidden(sK3(X0,X1,X0),X0)
      | r2_hidden(sK3(X0,X1,X0),X0) ) ),
    inference(superposition,[],[f200,f261])).

fof(f261,plain,(
    ! [X4,X2,X3] :
      ( k4_xboole_0(X2,X3) = k5_xboole_0(X2,X4)
      | r2_hidden(sK3(X2,X3,X4),X2)
      | r2_hidden(sK3(X2,X3,X4),X4) ) ),
    inference(superposition,[],[f66,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f54,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f200,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f190,f167])).

fof(f167,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f163,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f163,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f66,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f190,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f66,f169])).

fof(f169,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f120,f167])).

fof(f120,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f118,f40])).

fof(f118,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)) ),
    inference(superposition,[],[f71,f70])).

fof(f71,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f1645,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r2_hidden(sK3(X0,X1,X0),X1)
      | ~ r2_hidden(sK3(X0,X1,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f1577])).

fof(f1577,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r2_hidden(sK3(X0,X1,X0),X1)
      | ~ r2_hidden(sK3(X0,X1,X0),X0)
      | ~ r2_hidden(sK3(X0,X1,X0),X0) ) ),
    inference(superposition,[],[f311,f200])).

fof(f311,plain,(
    ! [X4,X2,X3] :
      ( k4_xboole_0(X2,X3) = k5_xboole_0(X2,X4)
      | ~ r2_hidden(sK3(X2,X3,X4),X3)
      | ~ r2_hidden(sK3(X2,X3,X4),X2)
      | ~ r2_hidden(sK3(X2,X3,X4),X4) ) ),
    inference(superposition,[],[f66,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f56,f44])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13009,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f13008])).

fof(f13008,plain,
    ( spl5_13
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f14193,plain,
    ( sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f13433,plain,
    ( sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f13432,plain,(
    ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f13429])).

fof(f13429,plain,
    ( $false
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f87,f12916])).

fof(f12916,plain,
    ( ! [X441] : ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),X441)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f12915])).

fof(f12915,plain,
    ( spl5_11
  <=> ! [X441] : ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),X441) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f13401,plain,
    ( spl5_11
    | spl5_9
    | spl5_1 ),
    inference(avatar_split_clause,[],[f13400,f100,f12906,f12915])).

fof(f12906,plain,
    ( spl5_9
  <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f13400,plain,
    ( ! [X4] :
        ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
        | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),X4) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f13393,f486])).

fof(f486,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f164,f200])).

fof(f164,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f66,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f13393,plain,
    ( ! [X4] :
        ( k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X4)
        | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
        | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),X4) )
    | spl5_1 ),
    inference(superposition,[],[f102,f5285])).

fof(f5285,plain,(
    ! [X14,X15,X16] :
      ( k4_xboole_0(X14,X15) = k4_xboole_0(X14,X16)
      | r2_hidden(sK3(X14,X16,X14),X14)
      | ~ r1_tarski(X14,X15) ) ),
    inference(superposition,[],[f975,f72])).

fof(f975,plain,(
    ! [X12,X10,X11] :
      ( r2_hidden(sK3(X10,X12,k4_xboole_0(X10,k4_xboole_0(X10,X11))),X10)
      | k4_xboole_0(X10,X11) = k4_xboole_0(X10,X12) ) ),
    inference(subsumption_resolution,[],[f916,f91])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f44])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f916,plain,(
    ! [X12,X10,X11] :
      ( k4_xboole_0(X10,X11) = k4_xboole_0(X10,X12)
      | r2_hidden(sK3(X10,X12,k4_xboole_0(X10,k4_xboole_0(X10,X11))),X10)
      | r2_hidden(sK3(X10,X12,k4_xboole_0(X10,k4_xboole_0(X10,X11))),k4_xboole_0(X10,k4_xboole_0(X10,X11))) ) ),
    inference(superposition,[],[f261,f66])).

fof(f13318,plain,
    ( spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f13213,f100,f108])).

fof(f108,plain,
    ( spl5_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f13213,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f13123,f93])).

fof(f93,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f13123,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK1))
        | r2_hidden(X4,sK2) )
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f13059,f167])).

fof(f13059,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0))
        | r2_hidden(X4,sK2) )
    | ~ spl5_1 ),
    inference(superposition,[],[f90,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f52,f44])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13317,plain,
    ( spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f13214,f100,f104])).

fof(f104,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f13214,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f13123,f95])).

fof(f95,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f50])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13047,plain,
    ( spl5_18
    | spl5_19
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f13002,f12906,f13044,f13040])).

fof(f13040,plain,
    ( spl5_18
  <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f13044,plain,
    ( spl5_19
  <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f13002,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f13001])).

fof(f13001,plain,
    ( sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_9 ),
    inference(resolution,[],[f12908,f98])).

fof(f98,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f50])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12908,plain,
    ( r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f12906])).

fof(f113,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f69,f104,f100])).

fof(f69,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f35,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).

fof(f21,plain,
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

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f112,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f68,f108,f100])).

fof(f68,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f36,f65])).

fof(f36,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f111,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f67,f108,f104,f100])).

fof(f67,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f37,f65])).

fof(f37,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:38:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (31327)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (31326)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.50  % (31334)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (31331)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (31335)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (31348)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (31330)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (31340)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (31328)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (31354)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (31333)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (31354)Refutation not found, incomplete strategy% (31354)------------------------------
% 0.21/0.51  % (31354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31354)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31354)Memory used [KB]: 1663
% 0.21/0.51  % (31354)Time elapsed: 0.114 s
% 0.21/0.51  % (31354)------------------------------
% 0.21/0.51  % (31354)------------------------------
% 0.21/0.51  % (31329)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (31345)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (31342)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (31346)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (31350)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (31335)Refutation not found, incomplete strategy% (31335)------------------------------
% 0.21/0.52  % (31335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31335)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31335)Memory used [KB]: 10746
% 0.21/0.52  % (31344)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (31335)Time elapsed: 0.069 s
% 0.21/0.52  % (31335)------------------------------
% 0.21/0.52  % (31335)------------------------------
% 0.21/0.52  % (31351)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (31338)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (31339)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (31339)Refutation not found, incomplete strategy% (31339)------------------------------
% 0.21/0.53  % (31339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31339)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31339)Memory used [KB]: 1663
% 0.21/0.53  % (31339)Time elapsed: 0.134 s
% 0.21/0.53  % (31339)------------------------------
% 0.21/0.53  % (31339)------------------------------
% 0.21/0.53  % (31332)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (31336)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (31353)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (31336)Refutation not found, incomplete strategy% (31336)------------------------------
% 0.21/0.53  % (31336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31336)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31336)Memory used [KB]: 6140
% 0.21/0.53  % (31336)Time elapsed: 0.130 s
% 0.21/0.53  % (31336)------------------------------
% 0.21/0.53  % (31336)------------------------------
% 0.21/0.53  % (31337)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (31325)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (31352)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (31352)Refutation not found, incomplete strategy% (31352)------------------------------
% 0.21/0.53  % (31352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31352)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31352)Memory used [KB]: 6140
% 0.21/0.53  % (31352)Time elapsed: 0.128 s
% 0.21/0.53  % (31352)------------------------------
% 0.21/0.53  % (31352)------------------------------
% 0.21/0.53  % (31343)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.54  % (31343)Refutation not found, incomplete strategy% (31343)------------------------------
% 1.42/0.54  % (31343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (31343)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (31343)Memory used [KB]: 1791
% 1.42/0.54  % (31343)Time elapsed: 0.131 s
% 1.42/0.54  % (31343)------------------------------
% 1.42/0.54  % (31343)------------------------------
% 1.42/0.54  % (31342)Refutation not found, incomplete strategy% (31342)------------------------------
% 1.42/0.54  % (31342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (31342)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (31342)Memory used [KB]: 1663
% 1.42/0.54  % (31342)Time elapsed: 0.141 s
% 1.42/0.54  % (31342)------------------------------
% 1.42/0.54  % (31342)------------------------------
% 1.42/0.54  % (31349)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.55  % (31347)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.42/0.55  % (31341)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.55  % (31341)Refutation not found, incomplete strategy% (31341)------------------------------
% 1.42/0.55  % (31341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (31341)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (31341)Memory used [KB]: 10618
% 1.42/0.55  % (31341)Time elapsed: 0.152 s
% 1.42/0.55  % (31341)------------------------------
% 1.42/0.55  % (31341)------------------------------
% 1.56/0.55  % (31353)Refutation not found, incomplete strategy% (31353)------------------------------
% 1.56/0.55  % (31353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.55  % (31353)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.55  
% 1.56/0.55  % (31353)Memory used [KB]: 10746
% 1.56/0.55  % (31353)Time elapsed: 0.133 s
% 1.56/0.55  % (31353)------------------------------
% 1.56/0.55  % (31353)------------------------------
% 1.99/0.65  % (31362)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.99/0.66  % (31360)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.99/0.66  % (31363)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.24/0.67  % (31364)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.24/0.67  % (31365)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.24/0.67  % (31328)Refutation not found, incomplete strategy% (31328)------------------------------
% 2.24/0.67  % (31328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.24/0.67  % (31328)Termination reason: Refutation not found, incomplete strategy
% 2.24/0.67  
% 2.24/0.67  % (31328)Memory used [KB]: 6140
% 2.24/0.67  % (31328)Time elapsed: 0.269 s
% 2.24/0.67  % (31328)------------------------------
% 2.24/0.67  % (31328)------------------------------
% 2.24/0.67  % (31364)Refutation not found, incomplete strategy% (31364)------------------------------
% 2.24/0.67  % (31364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.24/0.67  % (31364)Termination reason: Refutation not found, incomplete strategy
% 2.24/0.67  
% 2.24/0.67  % (31364)Memory used [KB]: 10618
% 2.24/0.67  % (31364)Time elapsed: 0.109 s
% 2.24/0.67  % (31364)------------------------------
% 2.24/0.67  % (31364)------------------------------
% 2.24/0.68  % (31361)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.24/0.69  % (31366)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.24/0.69  % (31367)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.24/0.70  % (31369)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.80/0.79  % (31400)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.80/0.80  % (31349)Time limit reached!
% 2.80/0.80  % (31349)------------------------------
% 2.80/0.80  % (31349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.80/0.80  % (31349)Termination reason: Time limit
% 2.80/0.80  
% 2.80/0.80  % (31349)Memory used [KB]: 12537
% 2.80/0.80  % (31349)Time elapsed: 0.400 s
% 2.80/0.80  % (31349)------------------------------
% 2.80/0.80  % (31349)------------------------------
% 2.80/0.80  % (31400)Refutation not found, incomplete strategy% (31400)------------------------------
% 2.80/0.80  % (31400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.80/0.80  % (31400)Termination reason: Refutation not found, incomplete strategy
% 2.80/0.80  
% 2.80/0.80  % (31400)Memory used [KB]: 10746
% 2.80/0.80  % (31400)Time elapsed: 0.065 s
% 2.80/0.80  % (31400)------------------------------
% 2.80/0.80  % (31400)------------------------------
% 3.16/0.84  % (31412)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.16/0.84  % (31327)Time limit reached!
% 3.16/0.84  % (31327)------------------------------
% 3.16/0.84  % (31327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.84  % (31327)Termination reason: Time limit
% 3.16/0.84  % (31327)Termination phase: Saturation
% 3.16/0.84  
% 3.16/0.84  % (31327)Memory used [KB]: 6652
% 3.16/0.84  % (31327)Time elapsed: 0.400 s
% 3.16/0.84  % (31327)------------------------------
% 3.16/0.84  % (31327)------------------------------
% 3.29/0.91  % (31331)Time limit reached!
% 3.29/0.91  % (31331)------------------------------
% 3.29/0.91  % (31331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.91  % (31331)Termination reason: Time limit
% 3.29/0.91  
% 3.29/0.91  % (31331)Memory used [KB]: 14967
% 3.29/0.91  % (31331)Time elapsed: 0.511 s
% 3.29/0.91  % (31331)------------------------------
% 3.29/0.91  % (31331)------------------------------
% 3.29/0.91  % (31461)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 3.64/0.94  % (31457)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 3.84/0.99  % (31495)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 3.84/1.00  % (31332)Time limit reached!
% 3.84/1.00  % (31332)------------------------------
% 3.84/1.00  % (31332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.84/1.02  % (31332)Termination reason: Time limit
% 3.84/1.02  % (31332)Termination phase: Saturation
% 3.84/1.02  
% 3.84/1.02  % (31332)Memory used [KB]: 5756
% 3.84/1.02  % (31332)Time elapsed: 0.600 s
% 3.84/1.02  % (31332)------------------------------
% 3.84/1.02  % (31332)------------------------------
% 4.17/1.04  % (31523)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 5.69/1.12  % (31549)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 6.12/1.16  % (31366)Time limit reached!
% 6.12/1.16  % (31366)------------------------------
% 6.12/1.16  % (31366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.12/1.16  % (31366)Termination reason: Time limit
% 6.12/1.16  % (31366)Termination phase: Saturation
% 6.12/1.16  
% 6.12/1.16  % (31366)Memory used [KB]: 18677
% 6.12/1.16  % (31366)Time elapsed: 0.600 s
% 6.12/1.16  % (31366)------------------------------
% 6.12/1.16  % (31366)------------------------------
% 6.35/1.18  % (31523)Refutation not found, incomplete strategy% (31523)------------------------------
% 6.35/1.18  % (31523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.35/1.20  % (31523)Termination reason: Refutation not found, incomplete strategy
% 6.35/1.20  
% 6.35/1.20  % (31523)Memory used [KB]: 6268
% 6.35/1.20  % (31523)Time elapsed: 0.238 s
% 6.35/1.20  % (31523)------------------------------
% 6.35/1.20  % (31523)------------------------------
% 6.35/1.22  % (31326)Time limit reached!
% 6.35/1.22  % (31326)------------------------------
% 6.35/1.22  % (31326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.84/1.23  % (31326)Termination reason: Time limit
% 6.84/1.23  
% 6.84/1.23  % (31326)Memory used [KB]: 3070
% 6.84/1.23  % (31326)Time elapsed: 0.819 s
% 6.84/1.23  % (31326)------------------------------
% 6.84/1.23  % (31326)------------------------------
% 7.09/1.27  % (31495)Time limit reached!
% 7.09/1.27  % (31495)------------------------------
% 7.09/1.27  % (31495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.09/1.27  % (31495)Termination reason: Time limit
% 7.09/1.27  % (31495)Termination phase: Saturation
% 7.09/1.27  
% 7.09/1.27  % (31495)Memory used [KB]: 13560
% 7.09/1.27  % (31495)Time elapsed: 0.400 s
% 7.09/1.27  % (31495)------------------------------
% 7.09/1.27  % (31495)------------------------------
% 7.09/1.31  % (31571)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 7.09/1.32  % (31581)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 7.09/1.33  % (31600)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 7.86/1.38  % (31611)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 7.86/1.40  % (31362)Time limit reached!
% 7.86/1.40  % (31362)------------------------------
% 7.86/1.40  % (31362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.86/1.40  % (31362)Termination reason: Time limit
% 7.86/1.40  
% 7.86/1.40  % (31362)Memory used [KB]: 12025
% 7.86/1.40  % (31362)Time elapsed: 0.834 s
% 7.86/1.40  % (31362)------------------------------
% 7.86/1.40  % (31362)------------------------------
% 7.86/1.40  % (31337)Time limit reached!
% 7.86/1.40  % (31337)------------------------------
% 7.86/1.40  % (31337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.86/1.40  % (31337)Termination reason: Time limit
% 7.86/1.40  
% 7.86/1.40  % (31337)Memory used [KB]: 15095
% 7.86/1.40  % (31337)Time elapsed: 1.003 s
% 7.86/1.40  % (31337)------------------------------
% 7.86/1.40  % (31337)------------------------------
% 8.52/1.48  % (31549)Time limit reached!
% 8.52/1.48  % (31549)------------------------------
% 8.52/1.48  % (31549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.52/1.48  % (31549)Termination reason: Time limit
% 8.52/1.48  % (31549)Termination phase: Saturation
% 8.52/1.48  
% 8.52/1.48  % (31549)Memory used [KB]: 9978
% 8.52/1.48  % (31549)Time elapsed: 0.400 s
% 8.52/1.48  % (31549)------------------------------
% 8.52/1.48  % (31549)------------------------------
% 8.91/1.53  % (31614)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 9.11/1.61  % (31325)Time limit reached!
% 9.11/1.61  % (31325)------------------------------
% 9.11/1.61  % (31325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.11/1.63  % (31325)Termination reason: Time limit
% 9.11/1.63  
% 9.11/1.63  % (31325)Memory used [KB]: 10234
% 9.11/1.63  % (31325)Time elapsed: 1.210 s
% 9.11/1.63  % (31325)------------------------------
% 9.11/1.63  % (31325)------------------------------
% 9.11/1.63  % (31581)Time limit reached!
% 9.11/1.63  % (31581)------------------------------
% 9.11/1.63  % (31581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.11/1.63  % (31581)Termination reason: Time limit
% 9.11/1.63  
% 9.11/1.63  % (31581)Memory used [KB]: 8443
% 9.11/1.63  % (31581)Time elapsed: 0.409 s
% 9.11/1.63  % (31581)------------------------------
% 9.11/1.63  % (31581)------------------------------
% 10.47/1.72  % (31571)Time limit reached!
% 10.47/1.72  % (31571)------------------------------
% 10.47/1.72  % (31571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.47/1.72  % (31571)Termination reason: Time limit
% 10.47/1.72  % (31571)Termination phase: Saturation
% 10.47/1.72  
% 10.47/1.72  % (31571)Memory used [KB]: 14456
% 10.47/1.72  % (31571)Time elapsed: 0.500 s
% 10.47/1.72  % (31571)------------------------------
% 10.47/1.72  % (31571)------------------------------
% 10.47/1.72  % (31330)Time limit reached!
% 10.47/1.72  % (31330)------------------------------
% 10.47/1.72  % (31330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.47/1.72  % (31330)Termination reason: Time limit
% 10.47/1.72  
% 10.47/1.72  % (31330)Memory used [KB]: 9978
% 10.47/1.72  % (31330)Time elapsed: 1.319 s
% 10.47/1.72  % (31330)------------------------------
% 10.47/1.72  % (31330)------------------------------
% 10.47/1.73  % (31611)Time limit reached!
% 10.47/1.73  % (31611)------------------------------
% 10.47/1.73  % (31611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.47/1.74  % (31611)Termination reason: Time limit
% 10.47/1.74  % (31611)Termination phase: Saturation
% 10.47/1.74  
% 10.47/1.74  % (31611)Memory used [KB]: 2942
% 10.47/1.74  % (31611)Time elapsed: 0.400 s
% 10.47/1.74  % (31611)------------------------------
% 10.47/1.74  % (31611)------------------------------
% 11.86/1.87  % (31614)Time limit reached!
% 11.86/1.87  % (31614)------------------------------
% 11.86/1.87  % (31614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.86/1.87  % (31614)Termination reason: Time limit
% 11.86/1.87  
% 11.86/1.87  % (31614)Memory used [KB]: 8571
% 11.86/1.87  % (31614)Time elapsed: 0.418 s
% 11.86/1.87  % (31614)------------------------------
% 11.86/1.87  % (31614)------------------------------
% 12.89/2.00  % (31351)Time limit reached!
% 12.89/2.00  % (31351)------------------------------
% 12.89/2.00  % (31351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.89/2.00  % (31351)Termination reason: Time limit
% 12.89/2.00  % (31351)Termination phase: Saturation
% 12.89/2.00  
% 12.89/2.00  % (31351)Memory used [KB]: 16119
% 12.89/2.00  % (31351)Time elapsed: 1.600 s
% 12.89/2.00  % (31351)------------------------------
% 12.89/2.00  % (31351)------------------------------
% 14.34/2.19  % (31345)Time limit reached!
% 14.34/2.19  % (31345)------------------------------
% 14.34/2.19  % (31345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.34/2.21  % (31345)Termination reason: Time limit
% 14.34/2.21  % (31345)Termination phase: Saturation
% 14.34/2.21  
% 14.34/2.21  % (31345)Memory used [KB]: 30575
% 14.34/2.21  % (31345)Time elapsed: 1.800 s
% 14.34/2.21  % (31345)------------------------------
% 14.34/2.21  % (31345)------------------------------
% 19.86/2.86  % (31340)Time limit reached!
% 19.86/2.86  % (31340)------------------------------
% 19.86/2.86  % (31340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.86/2.87  % (31340)Termination reason: Time limit
% 19.86/2.87  % (31340)Termination phase: Saturation
% 19.86/2.87  
% 19.86/2.87  % (31340)Memory used [KB]: 19317
% 19.86/2.87  % (31340)Time elapsed: 2.400 s
% 19.86/2.87  % (31340)------------------------------
% 19.86/2.87  % (31340)------------------------------
% 21.12/3.02  % (31361)Refutation found. Thanks to Tanya!
% 21.12/3.02  % SZS status Theorem for theBenchmark
% 21.12/3.02  % SZS output start Proof for theBenchmark
% 21.12/3.02  fof(f15765,plain,(
% 21.12/3.02    $false),
% 21.12/3.02    inference(avatar_sat_refutation,[],[f111,f112,f113,f13047,f13317,f13318,f13401,f13432,f13433,f14193,f15764])).
% 21.12/3.02  fof(f15764,plain,(
% 21.12/3.02    spl5_1 | ~spl5_13),
% 21.12/3.02    inference(avatar_contradiction_clause,[],[f15763])).
% 21.12/3.02  fof(f15763,plain,(
% 21.12/3.02    $false | (spl5_1 | ~spl5_13)),
% 21.12/3.02    inference(subsumption_resolution,[],[f15759,f102])).
% 21.12/3.02  fof(f102,plain,(
% 21.12/3.02    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | spl5_1),
% 21.12/3.02    inference(avatar_component_clause,[],[f100])).
% 21.12/3.02  fof(f100,plain,(
% 21.12/3.02    spl5_1 <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 21.12/3.02    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 21.12/3.02  fof(f15759,plain,(
% 21.12/3.02    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~spl5_13),
% 21.12/3.02    inference(resolution,[],[f13009,f1664])).
% 21.12/3.02  fof(f1664,plain,(
% 21.12/3.02    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,X0),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 21.12/3.02    inference(subsumption_resolution,[],[f1645,f962])).
% 21.12/3.02  fof(f962,plain,(
% 21.12/3.02    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 21.12/3.02    inference(duplicate_literal_removal,[],[f953])).
% 21.12/3.02  fof(f953,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | r2_hidden(sK3(X0,X1,X0),X0) | r2_hidden(sK3(X0,X1,X0),X0)) )),
% 21.12/3.02    inference(superposition,[],[f200,f261])).
% 21.12/3.02  fof(f261,plain,(
% 21.12/3.02    ( ! [X4,X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,X4) | r2_hidden(sK3(X2,X3,X4),X2) | r2_hidden(sK3(X2,X3,X4),X4)) )),
% 21.12/3.02    inference(superposition,[],[f66,f75])).
% 21.12/3.02  fof(f75,plain,(
% 21.12/3.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 21.12/3.02    inference(definition_unfolding,[],[f54,f44])).
% 21.12/3.02  fof(f44,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 21.12/3.02    inference(cnf_transformation,[],[f8])).
% 21.12/3.02  fof(f8,axiom,(
% 21.12/3.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 21.12/3.02  fof(f54,plain,(
% 21.12/3.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 21.12/3.02    inference(cnf_transformation,[],[f29])).
% 21.12/3.02  fof(f29,plain,(
% 21.12/3.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 21.12/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 21.12/3.02  fof(f28,plain,(
% 21.12/3.02    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 21.12/3.02    introduced(choice_axiom,[])).
% 21.12/3.02  fof(f27,plain,(
% 21.12/3.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 21.12/3.02    inference(rectify,[],[f26])).
% 21.12/3.02  fof(f26,plain,(
% 21.12/3.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 21.12/3.02    inference(flattening,[],[f25])).
% 21.12/3.02  fof(f25,plain,(
% 21.12/3.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 21.12/3.02    inference(nnf_transformation,[],[f1])).
% 21.12/3.02  fof(f1,axiom,(
% 21.12/3.02    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 21.12/3.02  fof(f66,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 21.12/3.02    inference(definition_unfolding,[],[f45,f44])).
% 21.12/3.02  fof(f45,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 21.12/3.02    inference(cnf_transformation,[],[f3])).
% 21.12/3.02  fof(f3,axiom,(
% 21.12/3.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 21.12/3.02  fof(f200,plain,(
% 21.12/3.02    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 21.12/3.02    inference(forward_demodulation,[],[f190,f167])).
% 21.12/3.02  fof(f167,plain,(
% 21.12/3.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 21.12/3.02    inference(forward_demodulation,[],[f163,f40])).
% 21.12/3.02  fof(f40,plain,(
% 21.12/3.02    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 21.12/3.02    inference(cnf_transformation,[],[f9])).
% 21.12/3.02  fof(f9,axiom,(
% 21.12/3.02    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 21.12/3.02  fof(f163,plain,(
% 21.12/3.02    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 21.12/3.02    inference(superposition,[],[f66,f70])).
% 21.12/3.02  fof(f70,plain,(
% 21.12/3.02    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 21.12/3.02    inference(definition_unfolding,[],[f39,f44])).
% 21.12/3.02  fof(f39,plain,(
% 21.12/3.02    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 21.12/3.02    inference(cnf_transformation,[],[f5])).
% 21.12/3.02  fof(f5,axiom,(
% 21.12/3.02    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 21.12/3.02  fof(f190,plain,(
% 21.12/3.02    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) )),
% 21.12/3.02    inference(superposition,[],[f66,f169])).
% 21.12/3.02  fof(f169,plain,(
% 21.12/3.02    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 21.12/3.02    inference(superposition,[],[f120,f167])).
% 21.12/3.02  fof(f120,plain,(
% 21.12/3.02    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) )),
% 21.12/3.02    inference(forward_demodulation,[],[f118,f40])).
% 21.12/3.02  fof(f118,plain,(
% 21.12/3.02    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0))) )),
% 21.12/3.02    inference(superposition,[],[f71,f70])).
% 21.12/3.02  fof(f71,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 21.12/3.02    inference(definition_unfolding,[],[f41,f43])).
% 21.12/3.02  fof(f43,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 21.12/3.02    inference(cnf_transformation,[],[f10])).
% 21.12/3.02  fof(f10,axiom,(
% 21.12/3.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 21.12/3.02  fof(f41,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 21.12/3.02    inference(cnf_transformation,[],[f7])).
% 21.12/3.02  fof(f7,axiom,(
% 21.12/3.02    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 21.12/3.02  fof(f1645,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r2_hidden(sK3(X0,X1,X0),X1) | ~r2_hidden(sK3(X0,X1,X0),X0)) )),
% 21.12/3.02    inference(duplicate_literal_removal,[],[f1577])).
% 21.12/3.02  fof(f1577,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r2_hidden(sK3(X0,X1,X0),X1) | ~r2_hidden(sK3(X0,X1,X0),X0) | ~r2_hidden(sK3(X0,X1,X0),X0)) )),
% 21.12/3.02    inference(superposition,[],[f311,f200])).
% 21.12/3.02  fof(f311,plain,(
% 21.12/3.02    ( ! [X4,X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,X4) | ~r2_hidden(sK3(X2,X3,X4),X3) | ~r2_hidden(sK3(X2,X3,X4),X2) | ~r2_hidden(sK3(X2,X3,X4),X4)) )),
% 21.12/3.02    inference(superposition,[],[f66,f73])).
% 21.12/3.02  fof(f73,plain,(
% 21.12/3.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 21.12/3.02    inference(definition_unfolding,[],[f56,f44])).
% 21.12/3.02  fof(f56,plain,(
% 21.12/3.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 21.12/3.02    inference(cnf_transformation,[],[f29])).
% 21.12/3.02  fof(f13009,plain,(
% 21.12/3.02    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2) | ~spl5_13),
% 21.12/3.02    inference(avatar_component_clause,[],[f13008])).
% 21.12/3.02  fof(f13008,plain,(
% 21.12/3.02    spl5_13 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)),
% 21.12/3.02    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 21.12/3.02  fof(f14193,plain,(
% 21.12/3.02    sK0 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)),
% 21.12/3.02    introduced(theory_tautology_sat_conflict,[])).
% 21.12/3.02  fof(f13433,plain,(
% 21.12/3.02    sK1 != sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),sK2)),
% 21.12/3.02    introduced(theory_tautology_sat_conflict,[])).
% 21.12/3.02  fof(f13432,plain,(
% 21.12/3.02    ~spl5_11),
% 21.12/3.02    inference(avatar_contradiction_clause,[],[f13429])).
% 21.12/3.02  fof(f13429,plain,(
% 21.12/3.02    $false | ~spl5_11),
% 21.12/3.02    inference(unit_resulting_resolution,[],[f87,f12916])).
% 21.12/3.02  fof(f12916,plain,(
% 21.12/3.02    ( ! [X441] : (~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),X441)) ) | ~spl5_11),
% 21.12/3.02    inference(avatar_component_clause,[],[f12915])).
% 21.12/3.02  fof(f12915,plain,(
% 21.12/3.02    spl5_11 <=> ! [X441] : ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),X441)),
% 21.12/3.02    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 21.12/3.02  fof(f87,plain,(
% 21.12/3.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 21.12/3.02    inference(equality_resolution,[],[f48])).
% 21.12/3.02  fof(f48,plain,(
% 21.12/3.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 21.12/3.02    inference(cnf_transformation,[],[f24])).
% 21.12/3.02  fof(f24,plain,(
% 21.12/3.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 21.12/3.02    inference(flattening,[],[f23])).
% 21.12/3.02  fof(f23,plain,(
% 21.12/3.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 21.12/3.02    inference(nnf_transformation,[],[f2])).
% 21.12/3.02  fof(f2,axiom,(
% 21.12/3.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 21.12/3.02  fof(f13401,plain,(
% 21.12/3.02    spl5_11 | spl5_9 | spl5_1),
% 21.12/3.02    inference(avatar_split_clause,[],[f13400,f100,f12906,f12915])).
% 21.12/3.02  fof(f12906,plain,(
% 21.12/3.02    spl5_9 <=> r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 21.12/3.02    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 21.12/3.02  fof(f13400,plain,(
% 21.12/3.02    ( ! [X4] : (r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),X4)) ) | spl5_1),
% 21.12/3.02    inference(subsumption_resolution,[],[f13393,f486])).
% 21.12/3.02  fof(f486,plain,(
% 21.12/3.02    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 21.12/3.02    inference(forward_demodulation,[],[f164,f200])).
% 21.12/3.02  fof(f164,plain,(
% 21.12/3.02    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1) | ~r1_tarski(X1,X2)) )),
% 21.12/3.02    inference(superposition,[],[f66,f72])).
% 21.12/3.02  fof(f72,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 21.12/3.02    inference(definition_unfolding,[],[f46,f44])).
% 21.12/3.02  fof(f46,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 21.12/3.02    inference(cnf_transformation,[],[f17])).
% 21.12/3.02  fof(f17,plain,(
% 21.12/3.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 21.12/3.02    inference(ennf_transformation,[],[f4])).
% 21.12/3.02  fof(f4,axiom,(
% 21.12/3.02    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 21.12/3.02  fof(f13393,plain,(
% 21.12/3.02    ( ! [X4] : (k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),X4) | r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),X4)) ) | spl5_1),
% 21.12/3.02    inference(superposition,[],[f102,f5285])).
% 21.12/3.02  fof(f5285,plain,(
% 21.12/3.02    ( ! [X14,X15,X16] : (k4_xboole_0(X14,X15) = k4_xboole_0(X14,X16) | r2_hidden(sK3(X14,X16,X14),X14) | ~r1_tarski(X14,X15)) )),
% 21.12/3.02    inference(superposition,[],[f975,f72])).
% 21.12/3.02  fof(f975,plain,(
% 21.12/3.02    ( ! [X12,X10,X11] : (r2_hidden(sK3(X10,X12,k4_xboole_0(X10,k4_xboole_0(X10,X11))),X10) | k4_xboole_0(X10,X11) = k4_xboole_0(X10,X12)) )),
% 21.12/3.02    inference(subsumption_resolution,[],[f916,f91])).
% 21.12/3.02  fof(f91,plain,(
% 21.12/3.02    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 21.12/3.02    inference(equality_resolution,[],[f78])).
% 21.12/3.02  fof(f78,plain,(
% 21.12/3.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 21.12/3.02    inference(definition_unfolding,[],[f51,f44])).
% 21.12/3.02  fof(f51,plain,(
% 21.12/3.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 21.12/3.02    inference(cnf_transformation,[],[f29])).
% 21.12/3.02  fof(f916,plain,(
% 21.12/3.02    ( ! [X12,X10,X11] : (k4_xboole_0(X10,X11) = k4_xboole_0(X10,X12) | r2_hidden(sK3(X10,X12,k4_xboole_0(X10,k4_xboole_0(X10,X11))),X10) | r2_hidden(sK3(X10,X12,k4_xboole_0(X10,k4_xboole_0(X10,X11))),k4_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 21.12/3.02    inference(superposition,[],[f261,f66])).
% 21.12/3.02  fof(f13318,plain,(
% 21.12/3.02    spl5_3 | ~spl5_1),
% 21.12/3.02    inference(avatar_split_clause,[],[f13213,f100,f108])).
% 21.12/3.02  fof(f108,plain,(
% 21.12/3.02    spl5_3 <=> r2_hidden(sK1,sK2)),
% 21.12/3.02    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 21.12/3.02  fof(f13213,plain,(
% 21.12/3.02    r2_hidden(sK1,sK2) | ~spl5_1),
% 21.12/3.02    inference(resolution,[],[f13123,f93])).
% 21.12/3.02  fof(f93,plain,(
% 21.12/3.02    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 21.12/3.02    inference(equality_resolution,[],[f92])).
% 21.12/3.02  fof(f92,plain,(
% 21.12/3.02    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 21.12/3.02    inference(equality_resolution,[],[f83])).
% 21.12/3.02  fof(f83,plain,(
% 21.12/3.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 21.12/3.02    inference(definition_unfolding,[],[f60,f50])).
% 21.12/3.02  fof(f50,plain,(
% 21.12/3.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 21.12/3.02    inference(cnf_transformation,[],[f13])).
% 21.12/3.02  fof(f13,axiom,(
% 21.12/3.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 21.12/3.02  fof(f60,plain,(
% 21.12/3.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 21.12/3.02    inference(cnf_transformation,[],[f34])).
% 21.12/3.02  fof(f34,plain,(
% 21.12/3.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 21.12/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 21.12/3.02  fof(f33,plain,(
% 21.12/3.02    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 21.12/3.02    introduced(choice_axiom,[])).
% 21.12/3.02  fof(f32,plain,(
% 21.12/3.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 21.12/3.02    inference(rectify,[],[f31])).
% 21.12/3.02  fof(f31,plain,(
% 21.12/3.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 21.12/3.02    inference(flattening,[],[f30])).
% 21.12/3.02  fof(f30,plain,(
% 21.12/3.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 21.12/3.02    inference(nnf_transformation,[],[f18])).
% 21.12/3.02  fof(f18,plain,(
% 21.12/3.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 21.12/3.02    inference(ennf_transformation,[],[f11])).
% 21.12/3.02  fof(f11,axiom,(
% 21.12/3.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 21.12/3.02  fof(f13123,plain,(
% 21.12/3.02    ( ! [X4] : (~r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK1)) | r2_hidden(X4,sK2)) ) | ~spl5_1),
% 21.12/3.02    inference(forward_demodulation,[],[f13059,f167])).
% 21.12/3.02  fof(f13059,plain,(
% 21.12/3.02    ( ! [X4] : (~r2_hidden(X4,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0)) | r2_hidden(X4,sK2)) ) | ~spl5_1),
% 21.12/3.02    inference(superposition,[],[f90,f101])).
% 21.12/3.02  fof(f101,plain,(
% 21.12/3.02    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~spl5_1),
% 21.12/3.02    inference(avatar_component_clause,[],[f100])).
% 21.12/3.02  fof(f90,plain,(
% 21.12/3.02    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X4,X1)) )),
% 21.12/3.02    inference(equality_resolution,[],[f77])).
% 21.12/3.02  fof(f77,plain,(
% 21.12/3.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 21.12/3.02    inference(definition_unfolding,[],[f52,f44])).
% 21.12/3.02  fof(f52,plain,(
% 21.12/3.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 21.12/3.02    inference(cnf_transformation,[],[f29])).
% 21.12/3.02  fof(f13317,plain,(
% 21.12/3.02    spl5_2 | ~spl5_1),
% 21.12/3.02    inference(avatar_split_clause,[],[f13214,f100,f104])).
% 21.12/3.02  fof(f104,plain,(
% 21.12/3.02    spl5_2 <=> r2_hidden(sK0,sK2)),
% 21.12/3.02    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 21.12/3.02  fof(f13214,plain,(
% 21.12/3.02    r2_hidden(sK0,sK2) | ~spl5_1),
% 21.12/3.02    inference(resolution,[],[f13123,f95])).
% 21.12/3.02  fof(f95,plain,(
% 21.12/3.02    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 21.12/3.02    inference(equality_resolution,[],[f94])).
% 21.12/3.02  fof(f94,plain,(
% 21.12/3.02    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 21.12/3.02    inference(equality_resolution,[],[f84])).
% 21.12/3.02  fof(f84,plain,(
% 21.12/3.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 21.12/3.02    inference(definition_unfolding,[],[f59,f50])).
% 21.12/3.02  fof(f59,plain,(
% 21.12/3.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 21.12/3.02    inference(cnf_transformation,[],[f34])).
% 21.12/3.02  fof(f13047,plain,(
% 21.12/3.02    spl5_18 | spl5_19 | ~spl5_9),
% 21.12/3.02    inference(avatar_split_clause,[],[f13002,f12906,f13044,f13040])).
% 21.12/3.02  fof(f13040,plain,(
% 21.12/3.02    spl5_18 <=> sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 21.12/3.02    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 21.12/3.02  fof(f13044,plain,(
% 21.12/3.02    spl5_19 <=> sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 21.12/3.02    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 21.12/3.02  fof(f13002,plain,(
% 21.12/3.02    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_9),
% 21.12/3.02    inference(duplicate_literal_removal,[],[f13001])).
% 21.12/3.02  fof(f13001,plain,(
% 21.12/3.02    sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK0 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 = sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_9),
% 21.12/3.02    inference(resolution,[],[f12908,f98])).
% 21.12/3.02  fof(f98,plain,(
% 21.12/3.02    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 21.12/3.02    inference(equality_resolution,[],[f86])).
% 21.12/3.02  fof(f86,plain,(
% 21.12/3.02    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 21.12/3.02    inference(definition_unfolding,[],[f57,f50])).
% 21.12/3.02  fof(f57,plain,(
% 21.12/3.02    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 21.12/3.02    inference(cnf_transformation,[],[f34])).
% 21.12/3.02  fof(f12908,plain,(
% 21.12/3.02    r2_hidden(sK3(k2_enumset1(sK0,sK0,sK0,sK1),sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl5_9),
% 21.12/3.02    inference(avatar_component_clause,[],[f12906])).
% 21.12/3.02  fof(f113,plain,(
% 21.12/3.02    spl5_1 | spl5_2),
% 21.12/3.02    inference(avatar_split_clause,[],[f69,f104,f100])).
% 21.12/3.02  fof(f69,plain,(
% 21.12/3.02    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 21.12/3.02    inference(definition_unfolding,[],[f35,f65])).
% 21.12/3.02  fof(f65,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 21.12/3.02    inference(definition_unfolding,[],[f42,f50])).
% 21.12/3.02  fof(f42,plain,(
% 21.12/3.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 21.12/3.02    inference(cnf_transformation,[],[f12])).
% 21.12/3.02  fof(f12,axiom,(
% 21.12/3.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 21.12/3.02  fof(f35,plain,(
% 21.12/3.02    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 21.12/3.02    inference(cnf_transformation,[],[f22])).
% 21.12/3.02  fof(f22,plain,(
% 21.12/3.02    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 21.12/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 21.12/3.02  fof(f21,plain,(
% 21.12/3.02    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 21.12/3.02    introduced(choice_axiom,[])).
% 21.12/3.02  fof(f20,plain,(
% 21.12/3.02    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 21.12/3.02    inference(flattening,[],[f19])).
% 21.12/3.02  fof(f19,plain,(
% 21.12/3.02    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 21.12/3.02    inference(nnf_transformation,[],[f16])).
% 21.12/3.02  fof(f16,plain,(
% 21.12/3.02    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 21.12/3.02    inference(ennf_transformation,[],[f15])).
% 21.12/3.02  fof(f15,negated_conjecture,(
% 21.12/3.02    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 21.12/3.02    inference(negated_conjecture,[],[f14])).
% 21.12/3.02  fof(f14,conjecture,(
% 21.12/3.02    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 21.12/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 21.12/3.02  fof(f112,plain,(
% 21.12/3.02    spl5_1 | spl5_3),
% 21.12/3.02    inference(avatar_split_clause,[],[f68,f108,f100])).
% 21.12/3.02  fof(f68,plain,(
% 21.12/3.02    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 21.12/3.02    inference(definition_unfolding,[],[f36,f65])).
% 21.12/3.02  fof(f36,plain,(
% 21.12/3.02    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 21.12/3.02    inference(cnf_transformation,[],[f22])).
% 21.12/3.02  fof(f111,plain,(
% 21.12/3.02    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 21.12/3.02    inference(avatar_split_clause,[],[f67,f108,f104,f100])).
% 21.12/3.02  fof(f67,plain,(
% 21.12/3.02    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 21.12/3.02    inference(definition_unfolding,[],[f37,f65])).
% 21.12/3.02  fof(f37,plain,(
% 21.12/3.02    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 21.12/3.02    inference(cnf_transformation,[],[f22])).
% 21.12/3.02  % SZS output end Proof for theBenchmark
% 21.12/3.02  % (31361)------------------------------
% 21.12/3.02  % (31361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.12/3.02  % (31361)Termination reason: Refutation
% 21.12/3.02  
% 21.12/3.02  % (31361)Memory used [KB]: 25330
% 21.12/3.02  % (31361)Time elapsed: 2.465 s
% 21.12/3.02  % (31361)------------------------------
% 21.12/3.02  % (31361)------------------------------
% 21.12/3.03  % (31324)Success in time 2.682 s
%------------------------------------------------------------------------------
