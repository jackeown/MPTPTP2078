%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0387+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  31 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  62 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1365,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1318,f1323,f1364])).

fof(f1364,plain,
    ( ~ spl40_1
    | spl40_2 ),
    inference(avatar_contradiction_clause,[],[f1363])).

fof(f1363,plain,
    ( $false
    | ~ spl40_1
    | spl40_2 ),
    inference(subsumption_resolution,[],[f1360,f1350])).

fof(f1350,plain,
    ( ~ r1_tarski(k1_setfam_1(sK0),k1_xboole_0)
    | spl40_2 ),
    inference(unit_resulting_resolution,[],[f1322,f925])).

fof(f925,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f582])).

fof(f582,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f1322,plain,
    ( k1_xboole_0 != k1_setfam_1(sK0)
    | spl40_2 ),
    inference(avatar_component_clause,[],[f1320])).

fof(f1320,plain,
    ( spl40_2
  <=> k1_xboole_0 = k1_setfam_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_2])])).

fof(f1360,plain,
    ( r1_tarski(k1_setfam_1(sK0),k1_xboole_0)
    | ~ spl40_1 ),
    inference(unit_resulting_resolution,[],[f1317,f864])).

fof(f864,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f564])).

fof(f564,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f554])).

fof(f554,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f1317,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | ~ spl40_1 ),
    inference(avatar_component_clause,[],[f1315])).

fof(f1315,plain,
    ( spl40_1
  <=> r2_hidden(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_1])])).

fof(f1323,plain,(
    ~ spl40_2 ),
    inference(avatar_split_clause,[],[f863,f1320])).

fof(f863,plain,(
    k1_xboole_0 != k1_setfam_1(sK0) ),
    inference(cnf_transformation,[],[f732])).

fof(f732,plain,
    ( k1_xboole_0 != k1_setfam_1(sK0)
    & r2_hidden(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f563,f731])).

fof(f731,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_setfam_1(X0)
        & r2_hidden(k1_xboole_0,X0) )
   => ( k1_xboole_0 != k1_setfam_1(sK0)
      & r2_hidden(k1_xboole_0,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f563,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_setfam_1(X0)
      & r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f557])).

fof(f557,negated_conjecture,(
    ~ ! [X0] :
        ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k1_setfam_1(X0) ) ),
    inference(negated_conjecture,[],[f556])).

fof(f556,conjecture,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_xboole_0 = k1_setfam_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

fof(f1318,plain,(
    spl40_1 ),
    inference(avatar_split_clause,[],[f862,f1315])).

fof(f862,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f732])).
%------------------------------------------------------------------------------
