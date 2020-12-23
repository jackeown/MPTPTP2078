%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0040+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:05 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  47 expanded)
%              Number of leaves         :    3 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 ( 102 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2458,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2438,f701])).

fof(f701,plain,(
    r2_hidden(sK6(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),sK0) ),
    inference(resolution,[],[f341,f242])).

fof(f242,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f341,plain,(
    r2_hidden(sK6(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f128,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f128,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f67])).

fof(f67,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f2438,plain,(
    ~ r2_hidden(sK6(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),sK0) ),
    inference(resolution,[],[f793,f277])).

fof(f277,plain,(
    ! [X30] :
      ( r2_hidden(X30,sK1)
      | ~ r2_hidden(X30,sK0) ) ),
    inference(resolution,[],[f127,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f127,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f85])).

fof(f793,plain,(
    ~ r2_hidden(sK6(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f773,f702])).

fof(f702,plain,(
    ~ r2_hidden(sK6(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),sK2) ),
    inference(resolution,[],[f341,f241])).

fof(f241,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f133])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f773,plain,
    ( ~ r2_hidden(sK6(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),sK1)
    | r2_hidden(sK6(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),sK2) ),
    inference(resolution,[],[f342,f240])).

fof(f240,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f342,plain,(
    ~ r2_hidden(sK6(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f128,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f107])).
%------------------------------------------------------------------------------
