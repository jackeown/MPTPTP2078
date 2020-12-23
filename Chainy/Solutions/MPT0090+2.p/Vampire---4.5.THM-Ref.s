%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0090+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  79 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :   15
%              Number of atoms          :   75 ( 155 expanded)
%              Number of equality atoms :   35 (  87 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f581,plain,(
    $false ),
    inference(subsumption_resolution,[],[f580,f256])).

fof(f256,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f123])).

fof(f123,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f580,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,sK2),sK2) ),
    inference(forward_demodulation,[],[f579,f517])).

fof(f517,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f516])).

fof(f516,plain,
    ( sK2 = k4_xboole_0(sK2,sK3)
    | sK2 = k4_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f423,f310])).

fof(f310,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f423,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k1_xboole_0)
    | sK2 = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[],[f322,f368])).

fof(f368,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | sK2 = k4_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f212,f329])).

fof(f329,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f252,f234])).

fof(f234,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f252,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f199])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f212,plain,
    ( r1_xboole_0(sK2,sK3)
    | sK2 = k4_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f198])).

fof(f198,plain,
    ( ( sK2 != k4_xboole_0(sK2,sK3)
      | ~ r1_xboole_0(sK2,sK3) )
    & ( sK2 = k4_xboole_0(sK2,sK3)
      | r1_xboole_0(sK2,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f196,f197])).

fof(f197,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( sK2 != k4_xboole_0(sK2,sK3)
        | ~ r1_xboole_0(sK2,sK3) )
      & ( sK2 = k4_xboole_0(sK2,sK3)
        | r1_xboole_0(sK2,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f196,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f136])).

fof(f136,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f130])).

fof(f130,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f129])).

fof(f129,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f322,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f233,f234])).

fof(f233,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

% (19587)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
fof(f86,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f579,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2) ),
    inference(forward_demodulation,[],[f566,f345])).

fof(f345,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f298,f234,f234])).

fof(f298,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f566,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f532,f327])).

fof(f327,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f251,f234])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f119])).

fof(f119,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f532,plain,(
    ~ r1_xboole_0(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f518,f254])).

fof(f254,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f518,plain,(
    ~ r1_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f213,f517])).

fof(f213,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | sK2 != k4_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f198])).
%------------------------------------------------------------------------------
