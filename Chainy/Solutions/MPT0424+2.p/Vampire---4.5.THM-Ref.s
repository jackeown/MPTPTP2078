%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0424+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   20 (  32 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  89 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f948,plain,(
    $false ),
    inference(subsumption_resolution,[],[f936,f686])).

fof(f686,plain,(
    r1_tarski(k3_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f646])).

fof(f646,plain,
    ( ~ r1_tarski(sK2,sK1)
    & r2_hidden(sK2,sK0)
    & r1_tarski(k3_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f619,f645])).

fof(f645,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,X1)
        & r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
   => ( ~ r1_tarski(sK2,sK1)
      & r2_hidden(sK2,sK0)
      & r1_tarski(k3_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f619,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,X1)
      & r2_hidden(X2,X0)
      & r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f618])).

fof(f618,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,X1)
      & r2_hidden(X2,X0)
      & r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f611])).

fof(f611,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X0)
          & r1_tarski(k3_tarski(X0),X1) )
       => r1_tarski(X2,X1) ) ),
    inference(negated_conjecture,[],[f610])).

fof(f610,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f936,plain,(
    ~ r1_tarski(k3_tarski(sK0),sK1) ),
    inference(resolution,[],[f802,f792])).

fof(f792,plain,(
    r1_tarski(sK2,k3_tarski(sK0)) ),
    inference(resolution,[],[f687,f735])).

fof(f735,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f643])).

fof(f643,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f441])).

fof(f441,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f687,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f646])).

fof(f802,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK2,X1)
      | ~ r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f688,f708])).

fof(f708,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f631])).

fof(f631,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f630])).

fof(f630,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f688,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f646])).
%------------------------------------------------------------------------------
