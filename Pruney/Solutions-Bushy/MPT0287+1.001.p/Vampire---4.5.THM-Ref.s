%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0287+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:41 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   22 (  42 expanded)
%              Number of leaves         :    3 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 ( 101 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f54,f37,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k3_tarski(sK0),sK1),X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f29,f9])).

fof(f9,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f29,plain,(
    ~ r2_hidden(sK2(k3_tarski(sK0),sK1),sK1) ),
    inference(resolution,[],[f8,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,plain,(
    ~ r1_tarski(k3_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      & ! [X2] :
          ( r1_tarski(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r1_tarski(X2,X1) )
       => r1_tarski(k3_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f37,plain,(
    r2_hidden(sK2(k3_tarski(sK0),sK1),sK4(sK0,sK2(k3_tarski(sK0),sK1))) ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK4(X0,X2))
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK4(X0,X2))
      | ~ r2_hidden(X2,X1)
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

fof(f28,plain,(
    r2_hidden(sK2(k3_tarski(sK0),sK1),k3_tarski(sK0)) ),
    inference(resolution,[],[f8,f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    r1_tarski(sK4(sK0,sK2(k3_tarski(sK0),sK1)),sK1) ),
    inference(resolution,[],[f38,f7])).

fof(f7,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | r1_tarski(X2,sK1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    r2_hidden(sK4(sK0,sK2(k3_tarski(sK0),sK1)),sK0) ),
    inference(resolution,[],[f28,f19])).

fof(f19,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

%------------------------------------------------------------------------------
