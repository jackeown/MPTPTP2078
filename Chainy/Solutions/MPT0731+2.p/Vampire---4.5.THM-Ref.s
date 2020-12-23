%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0731+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:46 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  44 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2109,f2120])).

fof(f2120,plain,(
    ~ spl48_1 ),
    inference(avatar_contradiction_clause,[],[f2119])).

fof(f2119,plain,
    ( $false
    | ~ spl48_1 ),
    inference(subsumption_resolution,[],[f2116,f1553])).

fof(f1553,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1082])).

fof(f1082,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f2116,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl48_1 ),
    inference(superposition,[],[f2033,f2108])).

fof(f2108,plain,
    ( sK0 = k1_ordinal1(sK0)
    | ~ spl48_1 ),
    inference(avatar_component_clause,[],[f2106])).

fof(f2106,plain,
    ( spl48_1
  <=> sK0 = k1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_1])])).

fof(f2033,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f1536])).

fof(f1536,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1390])).

fof(f1390,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f1389])).

fof(f1389,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1060])).

fof(f1060,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f2109,plain,(
    spl48_1 ),
    inference(avatar_split_clause,[],[f1533,f2106])).

fof(f1533,plain,(
    sK0 = k1_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f1388])).

fof(f1388,plain,(
    sK0 = k1_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1072,f1387])).

fof(f1387,plain,
    ( ? [X0] : k1_ordinal1(X0) = X0
   => sK0 = k1_ordinal1(sK0) ),
    introduced(choice_axiom,[])).

fof(f1072,plain,(
    ? [X0] : k1_ordinal1(X0) = X0 ),
    inference(ennf_transformation,[],[f1062])).

fof(f1062,negated_conjecture,(
    ~ ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(negated_conjecture,[],[f1061])).

fof(f1061,conjecture,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
%------------------------------------------------------------------------------
