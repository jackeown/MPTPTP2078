%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0391+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:28 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   39 (  56 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  100 ( 152 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1885,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1320,f1325,f1330,f1770,f1882])).

fof(f1882,plain,
    ( spl43_1
    | ~ spl43_2
    | ~ spl43_33 ),
    inference(avatar_contradiction_clause,[],[f1881])).

fof(f1881,plain,
    ( $false
    | spl43_1
    | ~ spl43_2
    | ~ spl43_33 ),
    inference(subsumption_resolution,[],[f1801,f1762])).

fof(f1762,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK0)
    | ~ spl43_33 ),
    inference(avatar_component_clause,[],[f1760])).

fof(f1760,plain,
    ( spl43_33
  <=> r1_tarski(k1_setfam_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_33])])).

fof(f1801,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),sK0)
    | spl43_1
    | ~ spl43_2 ),
    inference(unit_resulting_resolution,[],[f1324,f1319,f913])).

fof(f913,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f602])).

fof(f602,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f601])).

fof(f601,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f129])).

fof(f129,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f1319,plain,
    ( ~ r1_xboole_0(k1_setfam_1(sK1),sK2)
    | spl43_1 ),
    inference(avatar_component_clause,[],[f1317])).

fof(f1317,plain,
    ( spl43_1
  <=> r1_xboole_0(k1_setfam_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_1])])).

fof(f1324,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl43_2 ),
    inference(avatar_component_clause,[],[f1322])).

fof(f1322,plain,
    ( spl43_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_2])])).

fof(f1770,plain,
    ( spl43_33
    | ~ spl43_3 ),
    inference(avatar_split_clause,[],[f1533,f1327,f1760])).

fof(f1327,plain,
    ( spl43_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl43_3])])).

fof(f1533,plain,
    ( r1_tarski(k1_setfam_1(sK1),sK0)
    | ~ spl43_3 ),
    inference(unit_resulting_resolution,[],[f1269,f1329,f879])).

fof(f879,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f570])).

fof(f570,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f569])).

fof(f569,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f560])).

fof(f560,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f1329,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl43_3 ),
    inference(avatar_component_clause,[],[f1327])).

fof(f1269,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f986])).

fof(f986,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f782])).

fof(f782,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f781])).

fof(f781,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1330,plain,(
    spl43_3 ),
    inference(avatar_split_clause,[],[f876,f1327])).

fof(f876,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f744])).

fof(f744,plain,
    ( ~ r1_xboole_0(k1_setfam_1(sK1),sK2)
    & r1_xboole_0(sK0,sK2)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f568,f743])).

fof(f743,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
        & r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k1_setfam_1(sK1),sK2)
      & r1_xboole_0(sK0,sK2)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f568,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f567])).

fof(f567,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f562])).

fof(f562,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f561])).

fof(f561,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

fof(f1325,plain,(
    spl43_2 ),
    inference(avatar_split_clause,[],[f877,f1322])).

fof(f877,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f744])).

fof(f1320,plain,(
    ~ spl43_1 ),
    inference(avatar_split_clause,[],[f878,f1317])).

fof(f878,plain,(
    ~ r1_xboole_0(k1_setfam_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f744])).
%------------------------------------------------------------------------------
