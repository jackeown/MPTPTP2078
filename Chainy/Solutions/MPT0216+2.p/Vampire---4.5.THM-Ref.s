%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0216+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:17 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   53 (  85 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 161 expanded)
%              Number of equality atoms :   54 (  96 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f472,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f321,f325,f336,f343,f347,f423,f452,f466])).

fof(f466,plain,
    ( spl3_5
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | spl3_5
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f346,f448,f308])).

fof(f308,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_tarski(X1,X2)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f300])).

fof(f300,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f294])).

fof(f294,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(f448,plain,
    ( k1_tarski(sK0) = k2_tarski(sK2,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl3_9
  <=> k1_tarski(sK0) = k2_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f346,plain,
    ( sK0 != sK2
    | spl3_5 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl3_5
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f452,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f443,f421,f447])).

fof(f421,plain,
    ( spl3_6
  <=> k1_tarski(sK0) = k1_enumset1(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f443,plain,
    ( k1_tarski(sK0) = k2_tarski(sK2,sK0)
    | ~ spl3_6 ),
    inference(superposition,[],[f422,f360])).

fof(f360,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k1_enumset1(X1,X0,X0) ),
    inference(forward_demodulation,[],[f356,f313])).

fof(f313,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f356,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f311,f316])).

fof(f316,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f311,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f227])).

fof(f227,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f422,plain,
    ( k1_tarski(sK0) = k1_enumset1(sK2,sK0,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f421])).

fof(f423,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f419,f341,f421])).

fof(f341,plain,
    ( spl3_4
  <=> k1_tarski(sK0) = k2_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f419,plain,
    ( k1_tarski(sK0) = k1_enumset1(sK2,sK0,sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f418,f316])).

fof(f418,plain,
    ( k2_tarski(sK0,sK0) = k1_enumset1(sK2,sK0,sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f414,f313])).

fof(f414,plain,
    ( k1_enumset1(sK2,sK0,sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl3_4 ),
    inference(superposition,[],[f369,f342])).

fof(f342,plain,
    ( k1_tarski(sK0) = k2_tarski(sK0,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f341])).

fof(f369,plain,
    ( ! [X8] : k1_enumset1(sK2,X8,sK0) = k2_xboole_0(k2_tarski(X8,sK2),k1_tarski(sK0))
    | ~ spl3_4 ),
    inference(superposition,[],[f309,f342])).

fof(f309,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f225])).

fof(f225,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(f347,plain,
    ( ~ spl3_5
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f339,f334,f319,f345])).

fof(f319,plain,
    ( spl3_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f334,plain,
    ( spl3_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f339,plain,
    ( sK0 != sK2
    | spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f320,f335])).

fof(f335,plain,
    ( sK0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f334])).

fof(f320,plain,
    ( sK1 != sK2
    | spl3_1 ),
    inference(avatar_component_clause,[],[f319])).

fof(f343,plain,
    ( spl3_4
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f338,f334,f323,f341])).

fof(f323,plain,
    ( spl3_2
  <=> k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f338,plain,
    ( k1_tarski(sK0) = k2_tarski(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f324,f335])).

fof(f324,plain,
    ( k1_tarski(sK0) = k2_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f323])).

fof(f336,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f332,f323,f334])).

fof(f332,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(equality_resolution,[],[f326])).

fof(f326,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | sK1 = X0 )
    | ~ spl3_2 ),
    inference(superposition,[],[f308,f324])).

fof(f325,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f303,f323])).

fof(f303,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f302])).

fof(f302,plain,
    ( sK1 != sK2
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f298,f301])).

fof(f301,plain,
    ( ? [X0,X1,X2] :
        ( X1 != X2
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK1 != sK2
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f298,plain,(
    ? [X0,X1,X2] :
      ( X1 != X2
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f296])).

fof(f296,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f295])).

fof(f295,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f321,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f304,f319])).

fof(f304,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f302])).
%------------------------------------------------------------------------------
