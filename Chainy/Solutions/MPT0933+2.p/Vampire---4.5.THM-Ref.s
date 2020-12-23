%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0933+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:58 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   45 (  98 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  132 ( 433 expanded)
%              Number of equality atoms :   49 ( 193 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1707,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1531,f1535,f1539,f1543,f1547,f1551,f1692,f1698,f1706])).

fof(f1706,plain,
    ( sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | sK2 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | sK0 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1698,plain,
    ( spl9_15
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f1694,f1549,f1545,f1537,f1533,f1696])).

fof(f1696,plain,
    ( spl9_15
  <=> sK2 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f1533,plain,
    ( spl9_2
  <=> k2_mcart_1(sK0) = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f1537,plain,
    ( spl9_3
  <=> k1_mcart_1(sK0) = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f1545,plain,
    ( spl9_5
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f1549,plain,
    ( spl9_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f1694,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f1693,f1538])).

fof(f1538,plain,
    ( k1_mcart_1(sK0) = k1_mcart_1(sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f1537])).

fof(f1693,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK0))
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f1684,f1534])).

fof(f1534,plain,
    ( k2_mcart_1(sK0) = k2_mcart_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f1533])).

fof(f1684,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f1637,f1546])).

fof(f1546,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f1545])).

fof(f1637,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 )
    | ~ spl9_6 ),
    inference(resolution,[],[f1492,f1550])).

fof(f1550,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f1549])).

fof(f1492,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f1436])).

fof(f1436,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1435])).

fof(f1435,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1338])).

fof(f1338,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f1692,plain,
    ( spl9_14
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f1683,f1549,f1541,f1690])).

fof(f1690,plain,
    ( spl9_14
  <=> sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f1541,plain,
    ( spl9_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f1683,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(resolution,[],[f1637,f1542])).

fof(f1542,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f1541])).

fof(f1551,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f1465,f1549])).

fof(f1465,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1451])).

fof(f1451,plain,
    ( sK0 != sK2
    & k2_mcart_1(sK0) = k2_mcart_1(sK2)
    & k1_mcart_1(sK0) = k1_mcart_1(sK2)
    & r2_hidden(sK0,sK1)
    & r2_hidden(sK2,sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1422,f1450,f1449])).

fof(f1449,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X0 != X2
            & k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( sK0 != X2
          & k2_mcart_1(X2) = k2_mcart_1(sK0)
          & k1_mcart_1(X2) = k1_mcart_1(sK0)
          & r2_hidden(sK0,sK1)
          & r2_hidden(X2,sK1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1450,plain,
    ( ? [X2] :
        ( sK0 != X2
        & k2_mcart_1(X2) = k2_mcart_1(sK0)
        & k1_mcart_1(X2) = k1_mcart_1(sK0)
        & r2_hidden(sK0,sK1)
        & r2_hidden(X2,sK1) )
   => ( sK0 != sK2
      & k2_mcart_1(sK0) = k2_mcart_1(sK2)
      & k1_mcart_1(sK0) = k1_mcart_1(sK2)
      & r2_hidden(sK0,sK1)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1422,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1421])).

fof(f1421,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X0 != X2
          & k2_mcart_1(X0) = k2_mcart_1(X2)
          & k1_mcart_1(X0) = k1_mcart_1(X2)
          & r2_hidden(X0,X1)
          & r2_hidden(X2,X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1414])).

fof(f1414,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
              & k1_mcart_1(X0) = k1_mcart_1(X2)
              & r2_hidden(X0,X1)
              & r2_hidden(X2,X1) )
           => X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f1413])).

fof(f1413,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( k2_mcart_1(X0) = k2_mcart_1(X2)
            & k1_mcart_1(X0) = k1_mcart_1(X2)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
         => X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_mcart_1)).

fof(f1547,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f1466,f1545])).

fof(f1466,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f1451])).

fof(f1543,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f1467,f1541])).

fof(f1467,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f1451])).

fof(f1539,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f1468,f1537])).

fof(f1468,plain,(
    k1_mcart_1(sK0) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f1451])).

fof(f1535,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f1469,f1533])).

fof(f1469,plain,(
    k2_mcart_1(sK0) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f1451])).

fof(f1531,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f1470,f1529])).

fof(f1529,plain,
    ( spl9_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f1470,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f1451])).
%------------------------------------------------------------------------------
