%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0041+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:05 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   26 (  47 expanded)
%              Number of leaves         :    3 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 ( 102 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2360,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2340,f804])).

fof(f804,plain,(
    r2_hidden(sK6(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),sK0) ),
    inference(subsumption_resolution,[],[f784,f711])).

fof(f711,plain,(
    r2_hidden(sK6(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),sK2) ),
    inference(resolution,[],[f345,f245])).

fof(f245,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f345,plain,(
    r2_hidden(sK6(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f130,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f130,plain,(
    ~ r1_tarski(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f69,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(negated_conjecture,[],[f68])).

fof(f68,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f784,plain,
    ( ~ r2_hidden(sK6(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),sK2)
    | r2_hidden(sK6(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),sK0) ),
    inference(resolution,[],[f346,f243])).

fof(f243,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f346,plain,(
    ~ r2_hidden(sK6(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f130,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f2340,plain,(
    ~ r2_hidden(sK6(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),sK0) ),
    inference(resolution,[],[f712,f281])).

fof(f281,plain,(
    ! [X31] :
      ( r2_hidden(X31,sK1)
      | ~ r2_hidden(X31,sK0) ) ),
    inference(resolution,[],[f129,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f129,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f86])).

fof(f712,plain,(
    ~ r2_hidden(sK6(k4_xboole_0(sK2,sK1),k4_xboole_0(sK2,sK0)),sK1) ),
    inference(resolution,[],[f345,f244])).

fof(f244,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
