%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0390+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  45 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 118 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1414,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1334,f1339,f1344,f1413])).

fof(f1413,plain,
    ( ~ spl43_1
    | ~ spl43_2
    | spl43_3 ),
    inference(avatar_contradiction_clause,[],[f1412])).

fof(f1412,plain,
    ( $false
    | ~ spl43_1
    | ~ spl43_2
    | spl43_3 ),
    inference(subsumption_resolution,[],[f1391,f1358])).

fof(f1358,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK0)
    | ~ spl43_1 ),
    inference(unit_resulting_resolution,[],[f1333,f879])).

fof(f879,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f572])).

fof(f572,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f554])).

fof(f554,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f1333,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl43_1 ),
    inference(avatar_component_clause,[],[f1331])).

fof(f1331,plain,
    ( spl43_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_1])])).

fof(f1391,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),sK0)
    | ~ spl43_2
    | spl43_3 ),
    inference(unit_resulting_resolution,[],[f1343,f1338,f896])).

fof(f896,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f582])).

fof(f582,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f581])).

fof(f581,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1338,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl43_2 ),
    inference(avatar_component_clause,[],[f1336])).

fof(f1336,plain,
    ( spl43_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_2])])).

fof(f1343,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),sK2)
    | spl43_3 ),
    inference(avatar_component_clause,[],[f1341])).

fof(f1341,plain,
    ( spl43_3
  <=> r1_tarski(k1_setfam_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_3])])).

fof(f1344,plain,(
    ~ spl43_3 ),
    inference(avatar_split_clause,[],[f875,f1341])).

fof(f875,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f741])).

fof(f741,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),sK2)
    & r1_tarski(sK0,sK2)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f567,f740])).

fof(f740,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k1_setfam_1(X1),X2)
        & r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),sK2)
      & r1_tarski(sK0,sK2)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f567,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f566])).

fof(f566,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f561])).

fof(f561,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f560])).

fof(f560,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f1339,plain,(
    spl43_2 ),
    inference(avatar_split_clause,[],[f874,f1336])).

fof(f874,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f741])).

fof(f1334,plain,(
    spl43_1 ),
    inference(avatar_split_clause,[],[f873,f1331])).

fof(f873,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f741])).
%------------------------------------------------------------------------------
