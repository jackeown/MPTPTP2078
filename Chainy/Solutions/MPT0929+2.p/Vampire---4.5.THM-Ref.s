%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0929+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:58 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   27 (  40 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :   14
%              Number of atoms          :   65 (  85 expanded)
%              Number of equality atoms :   64 (  84 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2208,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2207,f1865])).

fof(f1865,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1396])).

fof(f1396,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f2207,plain,(
    sK0 != k1_mcart_1(k4_tarski(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2206,f1865])).

fof(f2206,plain,(
    sK0 != k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) ),
    inference(subsumption_resolution,[],[f2205,f1866])).

fof(f1866,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f1396])).

fof(f2205,plain,
    ( sK1 != k2_mcart_1(k4_tarski(sK0,sK1))
    | sK0 != k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) ),
    inference(forward_demodulation,[],[f2204,f1865])).

fof(f2204,plain,
    ( sK1 != k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))
    | sK0 != k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) ),
    inference(trivial_inequality_removal,[],[f2202])).

fof(f2202,plain,
    ( sK3 != sK3
    | sK1 != k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))
    | sK0 != k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) ),
    inference(backward_demodulation,[],[f2201,f1865])).

fof(f2201,plain,
    ( sK3 != k1_mcart_1(k4_tarski(sK3,sK4))
    | sK1 != k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))
    | sK0 != k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) ),
    inference(subsumption_resolution,[],[f2200,f1866])).

fof(f2200,plain,
    ( sK4 != k2_mcart_1(k4_tarski(sK3,sK4))
    | sK3 != k1_mcart_1(k4_tarski(sK3,sK4))
    | sK1 != k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))
    | sK0 != k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) ),
    inference(forward_demodulation,[],[f2198,f1866])).

fof(f2198,plain,
    ( sK3 != k1_mcart_1(k4_tarski(sK3,sK4))
    | sK4 != k2_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))))
    | sK1 != k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))
    | sK0 != k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) ),
    inference(backward_demodulation,[],[f2085,f1866])).

fof(f2085,plain,
    ( sK4 != k2_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))))
    | sK3 != k1_mcart_1(k2_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4))))
    | sK1 != k2_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)))
    | sK0 != k1_mcart_1(k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))) ),
    inference(definition_unfolding,[],[f1745,f1746,f1747,f1748,f1749])).

fof(f1749,plain,(
    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f1274])).

fof(f1274,axiom,(
    ! [X0] : k17_mcart_1(X0) = k1_mcart_1(k1_mcart_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_mcart_1)).

fof(f1748,plain,(
    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1275,axiom,(
    ! [X0] : k18_mcart_1(X0) = k2_mcart_1(k1_mcart_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_mcart_1)).

fof(f1747,plain,(
    ! [X0] : k19_mcart_1(X0) = k1_mcart_1(k2_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f1276])).

fof(f1276,axiom,(
    ! [X0] : k19_mcart_1(X0) = k1_mcart_1(k2_mcart_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_mcart_1)).

fof(f1746,plain,(
    ! [X0] : k20_mcart_1(X0) = k2_mcart_1(k2_mcart_1(X0)) ),
    inference(cnf_transformation,[],[f1277])).

fof(f1277,axiom,(
    ! [X0] : k20_mcart_1(X0) = k2_mcart_1(k2_mcart_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_mcart_1)).

fof(f1745,plain,
    ( sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK3 != k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f1590])).

fof(f1590,plain,
    ( sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK3 != k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
    | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f1414,f1589])).

fof(f1589,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4
        | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3
        | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1
        | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0 )
   => ( sK4 != k20_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
      | sK3 != k19_mcart_1(k4_tarski(sK5,k4_tarski(sK3,sK4)))
      | sK1 != k18_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
      | sK0 != k17_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f1414,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X4
      | k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) != X3
      | k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X1
      | k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) != X0 ) ),
    inference(ennf_transformation,[],[f1407])).

fof(f1407,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4
        & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3
        & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1
        & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0 ) ),
    inference(negated_conjecture,[],[f1406])).

fof(f1406,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k20_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X4
      & k19_mcart_1(k4_tarski(X5,k4_tarski(X3,X4))) = X3
      & k18_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X1
      & k17_mcart_1(k4_tarski(k4_tarski(X0,X1),X2)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_mcart_1)).
%------------------------------------------------------------------------------
