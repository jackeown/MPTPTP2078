%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0869+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 ( 100 expanded)
%              Number of leaves         :    4 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :   56 ( 260 expanded)
%              Number of equality atoms :   55 ( 259 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1738,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1737,f1719])).

fof(f1719,plain,(
    sK2 = sK5 ),
    inference(unit_resulting_resolution,[],[f1629,f1459])).

fof(f1459,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f1331])).

fof(f1331,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f391])).

fof(f391,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f1629,plain,(
    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK0,sK1),sK5) ),
    inference(backward_demodulation,[],[f1516,f1620])).

fof(f1620,plain,(
    k4_tarski(sK0,sK1) = k4_tarski(sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f1516,f1458])).

fof(f1458,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f1331])).

fof(f1516,plain,(
    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(k4_tarski(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f1425,f1427,f1427])).

fof(f1427,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1425,plain,(
    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f1351])).

fof(f1351,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f1321,f1350])).

% (20548)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
fof(f1350,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f1321,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1311])).

fof(f1311,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
       => ( X2 = X5
          & X1 = X4
          & X0 = X3 ) ) ),
    inference(negated_conjecture,[],[f1310])).

fof(f1310,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f1737,plain,(
    sK2 != sK5 ),
    inference(trivial_inequality_removal,[],[f1734])).

fof(f1734,plain,
    ( sK1 != sK1
    | sK2 != sK5 ),
    inference(backward_demodulation,[],[f1657,f1718])).

fof(f1718,plain,(
    sK1 = sK4 ),
    inference(unit_resulting_resolution,[],[f1656,f1459])).

fof(f1656,plain,(
    k4_tarski(sK0,sK1) = k4_tarski(sK0,sK4) ),
    inference(backward_demodulation,[],[f1620,f1633])).

fof(f1633,plain,(
    sK0 = sK3 ),
    inference(unit_resulting_resolution,[],[f1620,f1458])).

fof(f1657,plain,
    ( sK2 != sK5
    | sK1 != sK4 ),
    inference(trivial_inequality_removal,[],[f1654])).

fof(f1654,plain,
    ( sK0 != sK0
    | sK2 != sK5
    | sK1 != sK4 ),
    inference(backward_demodulation,[],[f1426,f1633])).

fof(f1426,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f1351])).
%------------------------------------------------------------------------------
