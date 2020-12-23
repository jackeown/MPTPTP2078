%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0199+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f634,plain,(
    $false ),
    inference(subsumption_resolution,[],[f605,f400])).

fof(f400,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f205])).

fof(f205,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).

fof(f605,plain,(
    k2_enumset1(sK15,sK16,sK17,sK18) != k2_enumset1(sK17,sK16,sK18,sK15) ),
    inference(superposition,[],[f385,f386])).

fof(f386,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(cnf_transformation,[],[f204])).

fof(f204,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_enumset1)).

fof(f385,plain,(
    k2_enumset1(sK15,sK16,sK17,sK18) != k2_enumset1(sK18,sK16,sK17,sK15) ),
    inference(cnf_transformation,[],[f309])).

fof(f309,plain,(
    k2_enumset1(sK15,sK16,sK17,sK18) != k2_enumset1(sK18,sK16,sK17,sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17,sK18])],[f271,f308])).

fof(f308,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X1,X2,X0)
   => k2_enumset1(sK15,sK16,sK17,sK18) != k2_enumset1(sK18,sK16,sK17,sK15) ),
    introduced(choice_axiom,[])).

fof(f271,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X1,X2,X0) ),
    inference(ennf_transformation,[],[f209])).

fof(f209,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    inference(negated_conjecture,[],[f208])).

fof(f208,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).
%------------------------------------------------------------------------------
