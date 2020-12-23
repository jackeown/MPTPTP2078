%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0008+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   18 (  38 expanded)
%              Number of leaves         :    2 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  94 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f135,f221,f131])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f63,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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

fof(f63,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X2)
      & r1_tarski(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X2)
      & r1_tarski(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,X2) ) ),
    inference(negated_conjecture,[],[f37])).

fof(f37,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f221,plain,(
    ~ r2_hidden(sK3(sK0,sK2),sK1) ),
    inference(resolution,[],[f133,f136])).

fof(f136,plain,(
    ~ r2_hidden(sK3(sK0,sK2),sK2) ),
    inference(resolution,[],[f65,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f65,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f133,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f64,f66])).

fof(f64,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f135,plain,(
    r2_hidden(sK3(sK0,sK2),sK0) ),
    inference(resolution,[],[f65,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
