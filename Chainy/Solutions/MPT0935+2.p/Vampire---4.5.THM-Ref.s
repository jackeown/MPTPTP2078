%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0935+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:58 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   19 (  29 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  54 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1706,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1705,f1703])).

fof(f1703,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(subsumption_resolution,[],[f1682,f1520])).

fof(f1520,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f697])).

fof(f697,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f1682,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f1516])).

fof(f1516,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(X4)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f1430,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k2_tarski(X0,X2) = k1_relat_1(X4) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f1429])).

fof(f1429,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k2_tarski(X0,X2) = k1_relat_1(X4) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f828])).

fof(f828,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k2_tarski(X0,X2) = k1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

fof(f1705,plain,(
    k2_tarski(sK0,sK3) != k1_relat_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK3,sK4))) ),
    inference(backward_demodulation,[],[f1624,f1703])).

fof(f1624,plain,(
    k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK3,sK4),sK5)))) ),
    inference(definition_unfolding,[],[f1505,f1619,f1619])).

fof(f1619,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1280])).

fof(f1280,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1505,plain,(
    k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) != k2_tarski(sK0,sK3) ),
    inference(cnf_transformation,[],[f1465])).

fof(f1465,plain,(
    k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) != k2_tarski(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f1420,f1464])).

fof(f1464,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) != k2_tarski(X0,X3)
   => k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) != k2_tarski(sK0,sK3) ),
    introduced(choice_axiom,[])).

fof(f1420,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) != k2_tarski(X0,X3) ),
    inference(ennf_transformation,[],[f1416])).

fof(f1416,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3) ),
    inference(negated_conjecture,[],[f1415])).

fof(f1415,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_mcart_1)).
%------------------------------------------------------------------------------
