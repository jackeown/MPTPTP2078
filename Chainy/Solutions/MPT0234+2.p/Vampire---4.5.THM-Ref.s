%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0234+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:18 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   25 (  30 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 (  53 expanded)
%              Number of equality atoms :   31 (  43 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1010,plain,(
    $false ),
    inference(subsumption_resolution,[],[f984,f508])).

fof(f508,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f441])).

fof(f441,plain,
    ( k2_tarski(sK4,sK5) != k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5))
    & sK4 != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f329,f440])).

fof(f440,plain,
    ( ? [X0,X1] :
        ( k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
        & X0 != X1 )
   => ( k2_tarski(sK4,sK5) != k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5))
      & sK4 != sK5 ) ),
    introduced(choice_axiom,[])).

fof(f329,plain,(
    ? [X0,X1] :
      ( k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f320])).

fof(f320,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f319])).

fof(f319,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f984,plain,(
    sK4 = sK5 ),
    inference(resolution,[],[f980,f588])).

fof(f588,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f377])).

fof(f377,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f306])).

fof(f306,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f980,plain,(
    ~ r1_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) ),
    inference(subsumption_resolution,[],[f935,f539])).

fof(f539,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f935,plain,
    ( k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k1_xboole_0)
    | ~ r1_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) ),
    inference(superposition,[],[f759,f739])).

fof(f739,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f507])).

fof(f507,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f759,plain,(
    k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) != k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) ),
    inference(definition_unfolding,[],[f509,f755])).

fof(f755,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(definition_unfolding,[],[f556,f528])).

fof(f528,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f556,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f509,plain,(
    k2_tarski(sK4,sK5) != k5_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f441])).
%------------------------------------------------------------------------------
