%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0288+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  45 expanded)
%              Number of leaves         :    3 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  99 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f36,f24,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1)),X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f22,f18])).

fof(f18,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k3_tarski(X0))
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f22,plain,(
    ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1)),k3_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f8,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f8,plain,(
    ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f24,plain,(
    r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1)),sK3(sK0,sK5(k3_tarski(sK0),k3_tarski(sK1)))) ),
    inference(unit_resulting_resolution,[],[f21,f20])).

fof(f20,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK3(X0,X2))
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK3(X0,X2))
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f21,plain,(
    r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1)),k3_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f8,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    r2_hidden(sK3(sK0,sK5(k3_tarski(sK0),k3_tarski(sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f7,f25,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,(
    r2_hidden(sK3(sK0,sK5(k3_tarski(sK0),k3_tarski(sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f21,f19])).

fof(f19,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
