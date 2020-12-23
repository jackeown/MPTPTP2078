%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0251+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  24 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   29 (  43 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1132,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1131,f596])).

fof(f596,plain,(
    r2_hidden(sK17,sK18) ),
    inference(cnf_transformation,[],[f494])).

fof(f494,plain,
    ( sK18 != k2_xboole_0(k1_tarski(sK17),sK18)
    & r2_hidden(sK17,sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f356,f493])).

fof(f493,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK18 != k2_xboole_0(k1_tarski(sK17),sK18)
      & r2_hidden(sK17,sK18) ) ),
    introduced(choice_axiom,[])).

fof(f356,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f348])).

fof(f348,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f347])).

fof(f347,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f1131,plain,(
    ~ r2_hidden(sK17,sK18) ),
    inference(trivial_inequality_removal,[],[f1124])).

fof(f1124,plain,
    ( sK18 != sK18
    | ~ r2_hidden(sK17,sK18) ),
    inference(superposition,[],[f920,f957])).

fof(f957,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_enumset1(X0,X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f710,f799])).

fof(f799,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f261])).

fof(f261,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f710,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f386])).

fof(f386,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f296])).

fof(f296,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f920,plain,(
    sK18 != k2_xboole_0(k1_enumset1(sK17,sK17,sK17),sK18) ),
    inference(definition_unfolding,[],[f597,f799])).

fof(f597,plain,(
    sK18 != k2_xboole_0(k1_tarski(sK17),sK18) ),
    inference(cnf_transformation,[],[f494])).
%------------------------------------------------------------------------------
