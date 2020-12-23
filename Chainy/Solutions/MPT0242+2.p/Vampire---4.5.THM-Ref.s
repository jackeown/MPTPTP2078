%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0242+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   15 (  23 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  67 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1474,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1419,f1418])).

fof(f1418,plain,(
    ~ r1_tarski(k1_tarski(sK4),sK5) ),
    inference(subsumption_resolution,[],[f613,f768])).

fof(f768,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f533])).

fof(f533,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f294])).

fof(f294,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f613,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r1_tarski(k1_tarski(sK4),sK5) ),
    inference(cnf_transformation,[],[f491])).

fof(f491,plain,
    ( ( ~ r2_hidden(sK4,sK5)
      | ~ r1_tarski(k1_tarski(sK4),sK5) )
    & ( r2_hidden(sK4,sK5)
      | r1_tarski(k1_tarski(sK4),sK5) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f489,f490])).

fof(f490,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | ~ r1_tarski(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | r1_tarski(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK4,sK5)
        | ~ r1_tarski(k1_tarski(sK4),sK5) )
      & ( r2_hidden(sK4,sK5)
        | r1_tarski(k1_tarski(sK4),sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f489,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f347])).

fof(f347,plain,(
    ? [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f337])).

fof(f337,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f336])).

fof(f336,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f1419,plain,(
    r1_tarski(k1_tarski(sK4),sK5) ),
    inference(subsumption_resolution,[],[f612,f769])).

fof(f769,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f533])).

fof(f612,plain,
    ( r2_hidden(sK4,sK5)
    | r1_tarski(k1_tarski(sK4),sK5) ),
    inference(cnf_transformation,[],[f491])).
%------------------------------------------------------------------------------
