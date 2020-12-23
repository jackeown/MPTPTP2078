%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0019+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:11 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   22 (  37 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  93 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(subsumption_resolution,[],[f83,f9])).

fof(f9,plain,(
    sK1 != k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(X0,X1) != X1
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => k2_xboole_0(X0,X1) = X1 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f83,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f78,f48])).

fof(f48,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK2(X4,X5,X5),X4)
      | k2_xboole_0(X4,X5) = X5 ) ),
    inference(subsumption_resolution,[],[f44,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f44,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK2(X4,X5,X5),X4)
      | r2_hidden(sK2(X4,X5,X5),X5)
      | k2_xboole_0(X4,X5) = X5 ) ),
    inference(factoring,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f78,plain,(
    ~ r2_hidden(sK2(sK0,sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f73,f9])).

fof(f73,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | sK1 = k2_xboole_0(sK0,sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK1),sK0) ),
    inference(resolution,[],[f48,f25])).

fof(f25,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(sK2(X8,X9,sK1),sK0)
      | sK1 = k2_xboole_0(X8,X9)
      | ~ r2_hidden(sK2(X8,X9,sK1),X8) ) ),
    inference(resolution,[],[f11,f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f10,f8])).

fof(f8,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

%------------------------------------------------------------------------------
