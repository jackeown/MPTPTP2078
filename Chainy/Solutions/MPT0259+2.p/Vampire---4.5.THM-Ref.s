%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0259+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   11 (  16 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  33 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1627,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f654,f653,f847])).

fof(f847,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f420])).

fof(f420,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f297])).

fof(f297,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f653,plain,(
    r1_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f525])).

fof(f525,plain,
    ( r2_hidden(sK2,sK3)
    & r1_xboole_0(k1_tarski(sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f366,f524])).

fof(f524,plain,
    ( ? [X0,X1] :
        ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) )
   => ( r2_hidden(sK2,sK3)
      & r1_xboole_0(k1_tarski(sK2),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f366,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,X1)
      & r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f356])).

fof(f356,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_hidden(X0,X1)
          & r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f355])).

fof(f355,conjecture,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).

fof(f654,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f525])).
%------------------------------------------------------------------------------
