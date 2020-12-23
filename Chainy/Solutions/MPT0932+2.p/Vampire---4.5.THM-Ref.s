%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0932+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:58 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   37 (  59 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 164 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1755,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1539,f1543,f1547,f1715,f1754])).

fof(f1754,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f1753])).

fof(f1753,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f1752,f1538])).

fof(f1538,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f1537])).

fof(f1537,plain,
    ( spl8_1
  <=> r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1752,plain,
    ( r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1)))
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f1740,f1542])).

fof(f1542,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f1541])).

fof(f1541,plain,
    ( spl8_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1740,plain,
    ( ~ r2_hidden(sK1,sK0)
    | r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1)))
    | ~ spl8_3
    | ~ spl8_12 ),
    inference(superposition,[],[f1635,f1714])).

fof(f1714,plain,
    ( sK1 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f1713])).

fof(f1713,plain,
    ( spl8_12
  <=> sK1 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f1635,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
        | r2_hidden(X1,k11_relat_1(sK0,X0)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f1474,f1546])).

fof(f1546,plain,
    ( v1_relat_1(sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f1545])).

fof(f1545,plain,
    ( spl8_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1474,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f1455])).

fof(f1455,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1423])).

fof(f1423,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f808])).

fof(f808,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f1715,plain,
    ( spl8_12
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f1708,f1545,f1541,f1713])).

fof(f1708,plain,
    ( sK1 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1))
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f1654,f1542])).

fof(f1654,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 )
    | ~ spl8_3 ),
    inference(resolution,[],[f1500,f1546])).

fof(f1500,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f1439])).

fof(f1439,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1438])).

fof(f1438,plain,(
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

fof(f1547,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f1470,f1545])).

fof(f1470,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1454])).

fof(f1454,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1)))
    & r2_hidden(sK1,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1421,f1453,f1452])).

fof(f1452,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))
            & r2_hidden(X1,X0) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(sK0,k1_mcart_1(X1)))
          & r2_hidden(X1,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1453,plain,
    ( ? [X1] :
        ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(sK0,k1_mcart_1(X1)))
        & r2_hidden(X1,sK0) )
   => ( ~ r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1)))
      & r2_hidden(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1421,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))
          & r2_hidden(X1,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1413])).

fof(f1413,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r2_hidden(X1,X0)
           => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f1412])).

fof(f1412,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_mcart_1)).

fof(f1543,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f1471,f1541])).

fof(f1471,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f1454])).

fof(f1539,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f1472,f1537])).

fof(f1472,plain,(
    ~ r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1))) ),
    inference(cnf_transformation,[],[f1454])).
%------------------------------------------------------------------------------
