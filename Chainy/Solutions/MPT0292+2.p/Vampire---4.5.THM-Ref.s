%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0292+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:22 EST 2020

% Result     : Theorem 3.24s
% Output     : Refutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   37 (  77 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 276 expanded)
%              Number of equality atoms :   23 (  62 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6617,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6615,f6541])).

fof(f6541,plain,(
    r2_hidden(sK4(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f6497,f646])).

fof(f646,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f545])).

fof(f545,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f398,f544])).

fof(f544,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f398,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f385])).

fof(f385,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f6497,plain,(
    ~ r1_tarski(k3_tarski(k1_zfmisc_1(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f639,f1481,f734])).

fof(f734,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f588])).

fof(f588,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f587])).

fof(f587,plain,(
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

fof(f1481,plain,(
    ! [X0] : r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f1461,f651])).

fof(f651,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f401])).

fof(f401,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f308])).

fof(f308,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f1461,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f1232,f1217])).

fof(f1217,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f661])).

fof(f661,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f551])).

fof(f551,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK6(X0,X1),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r1_tarski(sK6(X0,X1),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f549,f550])).

fof(f550,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK6(X0,X1),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( r1_tarski(sK6(X0,X1),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f549,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f548])).

fof(f548,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f284])).

fof(f284,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f1232,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f733])).

fof(f733,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f588])).

fof(f639,plain,(
    sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f537])).

fof(f537,plain,(
    sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f397,f536])).

fof(f536,plain,
    ( ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0
   => sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f397,plain,(
    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f391])).

fof(f391,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f390])).

fof(f390,conjecture,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f6615,plain,(
    ~ r2_hidden(sK4(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f6540,f1218])).

fof(f1218,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f660])).

fof(f660,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f551])).

fof(f6540,plain,(
    ~ r1_tarski(sK4(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f6497,f647])).

fof(f647,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f545])).
%------------------------------------------------------------------------------
