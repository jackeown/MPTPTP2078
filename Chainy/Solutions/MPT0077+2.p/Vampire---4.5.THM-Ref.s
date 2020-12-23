%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0077+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:07 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 515 expanded)
%              Number of leaves         :   19 ( 132 expanded)
%              Depth                    :   25
%              Number of atoms          :  182 (1642 expanded)
%              Number of equality atoms :   49 ( 265 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1051,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1050,f790])).

fof(f790,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f764,f736])).

fof(f736,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f726])).

fof(f726,plain,
    ( r1_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f614,f411])).

fof(f411,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f348])).

fof(f348,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f219])).

fof(f219,plain,(
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

fof(f614,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK0)
      | r1_xboole_0(sK0,sK1)
      | r1_xboole_0(X2,sK1) ) ),
    inference(resolution,[],[f418,f320])).

fof(f320,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f418,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_xboole_0(sK1,sK2))
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(sK0,sK1)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f254,f256])).

fof(f256,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X1,X3)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f127,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f126])).

fof(f126,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f106,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f254,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f196])).

fof(f196,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f125,f195])).

fof(f195,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f125,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f115])).

fof(f115,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f114])).

fof(f114,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f764,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r1_xboole_0(sK0,sK1) ) ),
    inference(superposition,[],[f272,f741])).

fof(f741,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f736,f264])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f197])).

fof(f197,plain,(
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

fof(f272,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f139,f200])).

fof(f200,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1050,plain,(
    r2_hidden(sK4(sK0,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1049,f1040])).

fof(f1040,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f1027,f264])).

fof(f1027,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | r1_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f793,f1022])).

fof(f1022,plain,(
    ! [X13] : k3_xboole_0(sK0,X13) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X13)) ),
    inference(forward_demodulation,[],[f1021,f316])).

fof(f316,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f1021,plain,(
    ! [X13] : k3_xboole_0(sK0,X13) = k2_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0)),k3_xboole_0(sK0,X13)) ),
    inference(forward_demodulation,[],[f1020,f399])).

fof(f399,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f1020,plain,(
    ! [X13] : k3_xboole_0(sK0,X13) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X13,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK0)),k3_xboole_0(sK0,X13)) ),
    inference(forward_demodulation,[],[f1019,f322])).

fof(f322,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1019,plain,(
    ! [X13] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X13,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK0)),k3_xboole_0(sK0,X13)) = k3_xboole_0(sK0,k2_xboole_0(X13,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1018,f393])).

fof(f393,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1018,plain,(
    ! [X13] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X13,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK0)),k3_xboole_0(sK0,X13)) = k3_xboole_0(k2_xboole_0(X13,k1_xboole_0),sK0) ),
    inference(forward_demodulation,[],[f1017,f317])).

fof(f317,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f1017,plain,(
    ! [X13] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X13,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK0)),k3_xboole_0(sK0,X13)) = k3_xboole_0(k2_xboole_0(X13,k1_xboole_0),k3_xboole_0(sK0,k2_xboole_0(sK0,X13))) ),
    inference(forward_demodulation,[],[f988,f387])).

fof(f387,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f988,plain,(
    ! [X13] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X13,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK0)),k3_xboole_0(sK0,X13)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X13,k1_xboole_0),sK0),k2_xboole_0(sK0,X13)) ),
    inference(superposition,[],[f293,f827])).

fof(f827,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f772,f826])).

fof(f826,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f785,f397])).

fof(f397,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f785,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f391,f741])).

fof(f391,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f772,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f312,f741])).

fof(f312,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f92])).

fof(f92,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f293,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_xboole_1)).

fof(f793,plain,
    ( r1_xboole_0(sK0,sK2)
    | k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f430,f766])).

fof(f766,plain,(
    ! [X2] : k3_xboole_0(sK0,k2_xboole_0(sK1,X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)) ),
    inference(superposition,[],[f301,f741])).

fof(f301,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f430,plain,
    ( r1_xboole_0(sK0,sK2)
    | k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f255,f264])).

fof(f255,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f196])).

fof(f1049,plain,(
    r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f1048,f790])).

fof(f1048,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0)
    | r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1034,f1040])).

fof(f1034,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,sK2))
    | r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f816,f1022])).

fof(f816,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK2)))
    | r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f811,f736])).

fof(f811,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK2)))
    | ~ r1_xboole_0(sK0,sK1)
    | r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f706,f766])).

fof(f706,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | r2_hidden(sK4(sK0,sK2),k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f445,f271])).

fof(f271,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f201])).

fof(f445,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f250,f271])).

fof(f250,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f196])).
%------------------------------------------------------------------------------
