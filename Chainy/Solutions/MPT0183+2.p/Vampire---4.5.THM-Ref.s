%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0183+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :   22 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f522,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f426,f521])).

fof(f521,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f520])).

fof(f520,plain,
    ( $false
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f519])).

fof(f519,plain,
    ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)) != k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | spl6_1 ),
    inference(forward_demodulation,[],[f518,f365])).

fof(f365,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f249])).

fof(f249,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

fof(f518,plain,
    ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK1,sK0,sK2)) != k4_xboole_0(k1_enumset1(sK1,sK0,sK2),k1_enumset1(sK0,sK1,sK2))
    | spl6_1 ),
    inference(forward_demodulation,[],[f509,f366])).

fof(f366,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f248])).

fof(f248,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(f509,plain,
    ( k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK1,sK2,sK0)) != k4_xboole_0(k1_enumset1(sK1,sK2,sK0),k1_enumset1(sK0,sK1,sK2))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f425,f320])).

fof(f320,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f267])).

fof(f267,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f92])).

fof(f92,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f425,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl6_1
  <=> k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f426,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f286,f423])).

fof(f286,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f274])).

fof(f274,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f253,f273])).

fof(f273,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    introduced(choice_axiom,[])).

fof(f253,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0) ),
    inference(ennf_transformation,[],[f191])).

fof(f191,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(negated_conjecture,[],[f190])).

fof(f190,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

% (18314)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
%------------------------------------------------------------------------------
