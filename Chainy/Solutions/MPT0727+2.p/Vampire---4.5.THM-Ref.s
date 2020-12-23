%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0727+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  34 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 (  86 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1122,f1127,f1176])).

fof(f1176,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_contradiction_clause,[],[f1175])).

fof(f1175,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f1144,f1101])).

fof(f1101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1070])).

fof(f1070,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f1144,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl12_1
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f1121,f1126,f1087])).

fof(f1087,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1076])).

fof(f1076,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f1074,f1075])).

fof(f1075,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1074,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1073])).

fof(f1073,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1063])).

fof(f1063,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1126,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f1124])).

fof(f1124,plain,
    ( spl12_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f1121,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f1119])).

fof(f1119,plain,
    ( spl12_1
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f1127,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f1084,f1124])).

fof(f1084,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f1072])).

fof(f1072,plain,
    ( r1_tarski(sK1,sK0)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1060,f1071])).

fof(f1071,plain,
    ( ? [X0,X1] :
        ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) )
   => ( r1_tarski(sK1,sK0)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1060,plain,(
    ? [X0,X1] :
      ( r1_tarski(X1,X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1059])).

fof(f1059,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r1_tarski(X1,X0)
          & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f1058])).

fof(f1058,conjecture,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1122,plain,(
    spl12_1 ),
    inference(avatar_split_clause,[],[f1085,f1119])).

fof(f1085,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f1072])).
%------------------------------------------------------------------------------
