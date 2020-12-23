%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0865+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:54 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   41 (  63 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 166 expanded)
%              Number of equality atoms :   38 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2086,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1616,f1620,f1624,f1903,f2072,f2076,f2085])).

fof(f2085,plain,
    ( k1_mcart_1(sK0) != sK34(sK0)
    | k2_mcart_1(sK0) != sK35(sK0)
    | sK0 != k4_tarski(sK34(sK0),sK35(sK0))
    | sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2076,plain,
    ( spl48_26
    | ~ spl48_14 ),
    inference(avatar_split_clause,[],[f2055,f1901,f2074])).

fof(f2074,plain,
    ( spl48_26
  <=> k2_mcart_1(sK0) = sK35(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_26])])).

fof(f1901,plain,
    ( spl48_14
  <=> sK0 = k4_tarski(sK34(sK0),sK35(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_14])])).

fof(f2055,plain,
    ( k2_mcart_1(sK0) = sK35(sK0)
    | ~ spl48_14 ),
    inference(superposition,[],[f1562,f1902])).

fof(f1902,plain,
    ( sK0 = k4_tarski(sK34(sK0),sK35(sK0))
    | ~ spl48_14 ),
    inference(avatar_component_clause,[],[f1901])).

fof(f1562,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1311])).

fof(f1311,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f2072,plain,
    ( spl48_25
    | ~ spl48_14 ),
    inference(avatar_split_clause,[],[f2054,f1901,f2070])).

fof(f2070,plain,
    ( spl48_25
  <=> k1_mcart_1(sK0) = sK34(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_25])])).

fof(f2054,plain,
    ( k1_mcart_1(sK0) = sK34(sK0)
    | ~ spl48_14 ),
    inference(superposition,[],[f1561,f1902])).

fof(f1561,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1311])).

fof(f1903,plain,
    ( spl48_14
    | ~ spl48_2
    | ~ spl48_3 ),
    inference(avatar_split_clause,[],[f1896,f1622,f1618,f1901])).

fof(f1618,plain,
    ( spl48_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_2])])).

fof(f1622,plain,
    ( spl48_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_3])])).

fof(f1896,plain,
    ( sK0 = k4_tarski(sK34(sK0),sK35(sK0))
    | ~ spl48_2
    | ~ spl48_3 ),
    inference(resolution,[],[f1891,f1619])).

fof(f1619,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl48_2 ),
    inference(avatar_component_clause,[],[f1618])).

fof(f1891,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k4_tarski(sK34(X0),sK35(X0)) = X0 )
    | ~ spl48_3 ),
    inference(resolution,[],[f1529,f1623])).

fof(f1623,plain,
    ( v1_relat_1(sK1)
    | ~ spl48_3 ),
    inference(avatar_component_clause,[],[f1622])).

fof(f1529,plain,(
    ! [X4,X0] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,X0)
      | k4_tarski(sK34(X4),sK35(X4)) = X4 ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f1430,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK33(X0)
          & r2_hidden(sK33(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK34(X4),sK35(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK33,sK34,sK35])],[f1427,f1429,f1428])).

fof(f1428,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK33(X0)
        & r2_hidden(sK33(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1429,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK34(X4),sK35(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f1427,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f1426])).

fof(f1426,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f1341])).

fof(f1341,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f653])).

fof(f653,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f1624,plain,(
    spl48_3 ),
    inference(avatar_split_clause,[],[f1454,f1622])).

fof(f1454,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1371])).

fof(f1371,plain,
    ( sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    & r2_hidden(sK0,sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1319,f1370])).

fof(f1370,plain,
    ( ? [X0,X1] :
        ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
        & r2_hidden(X0,X1)
        & v1_relat_1(X1) )
   => ( sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
      & r2_hidden(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1319,plain,(
    ? [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
      & r2_hidden(X0,X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1318])).

fof(f1318,plain,(
    ? [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) != X0
      & r2_hidden(X0,X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1305])).

fof(f1305,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,X1)
         => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f1304])).

fof(f1304,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f1620,plain,(
    spl48_2 ),
    inference(avatar_split_clause,[],[f1455,f1618])).

fof(f1455,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f1371])).

fof(f1616,plain,(
    ~ spl48_1 ),
    inference(avatar_split_clause,[],[f1456,f1614])).

fof(f1614,plain,
    ( spl48_1
  <=> sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_1])])).

fof(f1456,plain,(
    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(cnf_transformation,[],[f1371])).
%------------------------------------------------------------------------------
