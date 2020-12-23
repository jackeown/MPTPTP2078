%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0398+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:28 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   17 (  18 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f867,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f824,f860])).

fof(f860,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f858])).

fof(f858,plain,
    ( $false
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f784,f823,f672])).

fof(f672,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f577])).

fof(f577,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f556])).

fof(f556,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f823,plain,
    ( ~ r1_setfam_1(k1_xboole_0,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f821])).

fof(f821,plain,
    ( spl7_1
  <=> r1_setfam_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f784,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f824,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f667,f821])).

fof(f667,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f632])).

fof(f632,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f575,f631])).

fof(f631,plain,
    ( ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0)
   => ~ r1_setfam_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f575,plain,(
    ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f561])).

fof(f561,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f560])).

fof(f560,conjecture,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_setfam_1)).
%------------------------------------------------------------------------------
