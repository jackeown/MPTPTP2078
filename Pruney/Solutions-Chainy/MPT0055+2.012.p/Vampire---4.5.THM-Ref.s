%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:06 EST 2020

% Result     : Theorem 4.60s
% Output     : Refutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 249 expanded)
%              Number of leaves         :    9 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  176 (1571 expanded)
%              Number of equality atoms :   36 ( 266 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1766,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1759,f1424])).

fof(f1424,plain,(
    ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(global_subsumption,[],[f1080,f1411])).

fof(f1411,plain,(
    ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1400,f81])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1400,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(superposition,[],[f407,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f407,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ) ),
    inference(resolution,[],[f227,f81])).

fof(f227,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f215,f117])).

fof(f117,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f42,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f42,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f29])).

fof(f29,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f215,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(resolution,[],[f123,f80])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f123,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f42,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1080,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(duplicate_literal_removal,[],[f1072])).

fof(f1072,plain,
    ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(superposition,[],[f295,f52])).

fof(f295,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f135,f80])).

fof(f135,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2] :
      ( k3_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),sK0)
      | ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f42,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1759,plain,(
    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(resolution,[],[f1456,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1456,plain,(
    ! [X7] :
      ( ~ r1_tarski(k3_xboole_0(sK0,sK1),X7)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X7) ) ),
    inference(subsumption_resolution,[],[f779,f1424])).

fof(f779,plain,(
    ! [X7] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X7)
      | ~ r1_tarski(k3_xboole_0(sK0,sK1),X7) ) ),
    inference(subsumption_resolution,[],[f769,f455])).

fof(f455,plain,
    ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
    | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(superposition,[],[f189,f73])).

fof(f73,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f44,f43,f43])).

fof(f43,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f189,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ) ),
    inference(resolution,[],[f117,f81])).

fof(f769,plain,(
    ! [X7] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X7)
      | ~ r1_tarski(k3_xboole_0(sK0,sK1),X7) ) ),
    inference(superposition,[],[f190,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f43])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f190,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1))
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f117,f80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:54:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (28580)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (28587)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (28565)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (28565)Refutation not found, incomplete strategy% (28565)------------------------------
% 0.22/0.54  % (28565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28565)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28565)Memory used [KB]: 6140
% 0.22/0.54  % (28565)Time elapsed: 0.109 s
% 0.22/0.54  % (28565)------------------------------
% 0.22/0.54  % (28565)------------------------------
% 0.22/0.57  % (28589)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (28581)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.57  % (28584)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (28563)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (28581)Refutation not found, incomplete strategy% (28581)------------------------------
% 0.22/0.57  % (28581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (28581)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (28581)Memory used [KB]: 10746
% 0.22/0.57  % (28581)Time elapsed: 0.147 s
% 0.22/0.57  % (28581)------------------------------
% 0.22/0.57  % (28581)------------------------------
% 0.22/0.57  % (28566)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.58  % (28569)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.58  % (28576)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.58  % (28569)Refutation not found, incomplete strategy% (28569)------------------------------
% 0.22/0.58  % (28569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (28569)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (28569)Memory used [KB]: 10618
% 0.22/0.58  % (28569)Time elapsed: 0.151 s
% 0.22/0.58  % (28569)------------------------------
% 0.22/0.58  % (28569)------------------------------
% 0.22/0.58  % (28576)Refutation not found, incomplete strategy% (28576)------------------------------
% 0.22/0.58  % (28576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (28576)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (28576)Memory used [KB]: 6268
% 0.22/0.58  % (28576)Time elapsed: 0.105 s
% 0.22/0.58  % (28576)------------------------------
% 0.22/0.58  % (28576)------------------------------
% 0.22/0.59  % (28567)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.59  % (28562)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.59  % (28590)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.59  % (28561)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.59  % (28561)Refutation not found, incomplete strategy% (28561)------------------------------
% 0.22/0.59  % (28561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (28561)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (28561)Memory used [KB]: 1663
% 0.22/0.59  % (28561)Time elapsed: 0.159 s
% 0.22/0.59  % (28561)------------------------------
% 0.22/0.59  % (28561)------------------------------
% 0.22/0.60  % (28588)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.60  % (28586)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.60  % (28564)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.60  % (28586)Refutation not found, incomplete strategy% (28586)------------------------------
% 0.22/0.60  % (28586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (28586)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (28586)Memory used [KB]: 6268
% 0.22/0.60  % (28586)Time elapsed: 0.142 s
% 0.22/0.60  % (28586)------------------------------
% 0.22/0.60  % (28586)------------------------------
% 0.22/0.60  % (28568)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.60  % (28563)Refutation not found, incomplete strategy% (28563)------------------------------
% 0.22/0.60  % (28563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (28563)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (28563)Memory used [KB]: 10618
% 0.22/0.60  % (28563)Time elapsed: 0.173 s
% 0.22/0.60  % (28563)------------------------------
% 0.22/0.60  % (28563)------------------------------
% 0.22/0.60  % (28574)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.60  % (28582)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.60  % (28582)Refutation not found, incomplete strategy% (28582)------------------------------
% 0.22/0.60  % (28582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (28582)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (28582)Memory used [KB]: 1663
% 0.22/0.60  % (28582)Time elapsed: 0.184 s
% 0.22/0.60  % (28582)------------------------------
% 0.22/0.60  % (28582)------------------------------
% 0.22/0.60  % (28577)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.61  % (28585)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.91/0.61  % (28571)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.91/0.61  % (28571)Refutation not found, incomplete strategy% (28571)------------------------------
% 1.91/0.61  % (28571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.61  % (28571)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.61  
% 1.91/0.61  % (28571)Memory used [KB]: 10618
% 1.91/0.61  % (28571)Time elapsed: 0.183 s
% 1.91/0.61  % (28571)------------------------------
% 1.91/0.61  % (28571)------------------------------
% 1.91/0.61  % (28572)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.91/0.61  % (28570)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.91/0.62  % (28575)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.91/0.62  % (28573)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.05/0.63  % (28583)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 2.05/0.63  % (28579)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.05/0.63  % (28583)Refutation not found, incomplete strategy% (28583)------------------------------
% 2.05/0.63  % (28583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.63  % (28583)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.63  
% 2.05/0.63  % (28583)Memory used [KB]: 10746
% 2.05/0.63  % (28583)Time elapsed: 0.203 s
% 2.05/0.63  % (28583)------------------------------
% 2.05/0.63  % (28583)------------------------------
% 2.05/0.63  % (28578)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.05/0.63  % (28578)Refutation not found, incomplete strategy% (28578)------------------------------
% 2.05/0.63  % (28578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.63  % (28578)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.63  
% 2.05/0.63  % (28578)Memory used [KB]: 10618
% 2.05/0.63  % (28578)Time elapsed: 0.203 s
% 2.05/0.63  % (28578)------------------------------
% 2.05/0.63  % (28578)------------------------------
% 2.05/0.63  % (28570)Refutation not found, incomplete strategy% (28570)------------------------------
% 2.05/0.63  % (28570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.63  % (28570)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.63  
% 2.05/0.63  % (28570)Memory used [KB]: 10618
% 2.05/0.63  % (28570)Time elapsed: 0.214 s
% 2.05/0.63  % (28570)------------------------------
% 2.05/0.63  % (28570)------------------------------
% 2.12/0.66  % (28623)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.12/0.66  % (28623)Refutation not found, incomplete strategy% (28623)------------------------------
% 2.12/0.66  % (28623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.66  % (28623)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.66  
% 2.12/0.66  % (28623)Memory used [KB]: 1791
% 2.12/0.66  % (28623)Time elapsed: 0.005 s
% 2.12/0.66  % (28623)------------------------------
% 2.12/0.66  % (28623)------------------------------
% 2.12/0.70  % (28615)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.57/0.71  % (28615)Refutation not found, incomplete strategy% (28615)------------------------------
% 2.57/0.71  % (28615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.57/0.71  % (28615)Termination reason: Refutation not found, incomplete strategy
% 2.57/0.71  
% 2.57/0.71  % (28615)Memory used [KB]: 6140
% 2.57/0.71  % (28615)Time elapsed: 0.099 s
% 2.57/0.71  % (28615)------------------------------
% 2.57/0.71  % (28615)------------------------------
% 2.57/0.72  % (28616)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.57/0.72  % (28622)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.57/0.72  % (28621)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.57/0.72  % (28617)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.57/0.72  % (28619)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.57/0.73  % (28618)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.57/0.73  % (28620)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.57/0.74  % (28625)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.57/0.76  % (28624)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.88/0.79  % (28626)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.88/0.81  % (28627)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.88/0.84  % (28641)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.88/0.84  % (28641)Refutation not found, incomplete strategy% (28641)------------------------------
% 2.88/0.84  % (28641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.88/0.84  % (28641)Termination reason: Refutation not found, incomplete strategy
% 2.88/0.84  
% 2.88/0.84  % (28641)Memory used [KB]: 1663
% 2.88/0.84  % (28641)Time elapsed: 0.103 s
% 2.88/0.84  % (28641)------------------------------
% 2.88/0.84  % (28641)------------------------------
% 2.88/0.85  % (28566)Time limit reached!
% 2.88/0.85  % (28566)------------------------------
% 2.88/0.85  % (28566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.88/0.85  % (28566)Termination reason: Time limit
% 2.88/0.85  
% 2.88/0.85  % (28566)Memory used [KB]: 8827
% 2.88/0.85  % (28566)Time elapsed: 0.426 s
% 2.88/0.85  % (28566)------------------------------
% 2.88/0.85  % (28566)------------------------------
% 3.59/0.92  % (28562)Time limit reached!
% 3.59/0.92  % (28562)------------------------------
% 3.59/0.92  % (28562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.77/0.93  % (28573)Time limit reached!
% 3.77/0.93  % (28573)------------------------------
% 3.77/0.93  % (28573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.77/0.93  % (28573)Termination reason: Time limit
% 3.77/0.93  
% 3.77/0.93  % (28573)Memory used [KB]: 9466
% 3.77/0.93  % (28573)Time elapsed: 0.513 s
% 3.77/0.93  % (28573)------------------------------
% 3.77/0.93  % (28573)------------------------------
% 3.87/0.94  % (28562)Termination reason: Time limit
% 3.87/0.94  % (28562)Termination phase: Saturation
% 3.87/0.94  
% 3.87/0.94  % (28562)Memory used [KB]: 9083
% 3.87/0.94  % (28562)Time elapsed: 0.502 s
% 3.87/0.94  % (28562)------------------------------
% 3.87/0.94  % (28562)------------------------------
% 3.87/0.98  % (28705)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 3.87/0.99  % (28698)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 4.17/1.01  % (28618)Time limit reached!
% 4.17/1.01  % (28618)------------------------------
% 4.17/1.01  % (28618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/1.01  % (28618)Termination reason: Time limit
% 4.17/1.01  % (28618)Termination phase: Saturation
% 4.17/1.01  
% 4.17/1.01  % (28618)Memory used [KB]: 8059
% 4.17/1.01  % (28618)Time elapsed: 0.403 s
% 4.17/1.01  % (28618)------------------------------
% 4.17/1.01  % (28618)------------------------------
% 4.17/1.03  % (28758)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 4.17/1.03  % (28619)Time limit reached!
% 4.17/1.03  % (28619)------------------------------
% 4.17/1.03  % (28619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/1.03  % (28619)Termination reason: Time limit
% 4.17/1.03  
% 4.17/1.03  % (28619)Memory used [KB]: 13176
% 4.17/1.03  % (28619)Time elapsed: 0.419 s
% 4.17/1.03  % (28619)------------------------------
% 4.17/1.03  % (28619)------------------------------
% 4.17/1.04  % (28577)Time limit reached!
% 4.17/1.04  % (28577)------------------------------
% 4.17/1.04  % (28577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/1.04  % (28577)Termination reason: Time limit
% 4.17/1.04  
% 4.17/1.04  % (28577)Memory used [KB]: 18677
% 4.17/1.04  % (28577)Time elapsed: 0.612 s
% 4.17/1.04  % (28577)------------------------------
% 4.17/1.04  % (28577)------------------------------
% 4.17/1.05  % (28765)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 4.17/1.05  % (28589)Time limit reached!
% 4.17/1.05  % (28589)------------------------------
% 4.17/1.05  % (28589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/1.05  % (28589)Termination reason: Time limit
% 4.17/1.05  
% 4.17/1.05  % (28589)Memory used [KB]: 10106
% 4.17/1.05  % (28589)Time elapsed: 0.619 s
% 4.17/1.05  % (28589)------------------------------
% 4.17/1.05  % (28589)------------------------------
% 4.17/1.05  % (28765)Refutation not found, incomplete strategy% (28765)------------------------------
% 4.17/1.05  % (28765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/1.05  % (28765)Termination reason: Refutation not found, incomplete strategy
% 4.17/1.05  
% 4.17/1.05  % (28765)Memory used [KB]: 6140
% 4.17/1.05  % (28765)Time elapsed: 0.058 s
% 4.17/1.05  % (28765)------------------------------
% 4.17/1.05  % (28765)------------------------------
% 4.60/1.07  % (28568)Time limit reached!
% 4.60/1.07  % (28568)------------------------------
% 4.60/1.07  % (28568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.60/1.08  % (28568)Termination reason: Time limit
% 4.60/1.08  % (28568)Termination phase: Saturation
% 4.60/1.08  
% 4.60/1.08  % (28568)Memory used [KB]: 11001
% 4.60/1.08  % (28568)Time elapsed: 0.600 s
% 4.60/1.08  % (28568)------------------------------
% 4.60/1.08  % (28568)------------------------------
% 4.60/1.14  % (28787)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 4.60/1.14  % (28789)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 4.60/1.14  % (28788)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 4.60/1.15  % (28625)Refutation found. Thanks to Tanya!
% 4.60/1.15  % SZS status Theorem for theBenchmark
% 4.60/1.15  % SZS output start Proof for theBenchmark
% 4.60/1.15  fof(f1766,plain,(
% 4.60/1.15    $false),
% 4.60/1.15    inference(subsumption_resolution,[],[f1759,f1424])).
% 4.60/1.15  fof(f1424,plain,(
% 4.60/1.15    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.60/1.15    inference(global_subsumption,[],[f1080,f1411])).
% 4.60/1.15  fof(f1411,plain,(
% 4.60/1.15    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 4.60/1.15    inference(subsumption_resolution,[],[f1400,f81])).
% 4.60/1.15  fof(f81,plain,(
% 4.60/1.15    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 4.60/1.15    inference(equality_resolution,[],[f68])).
% 4.60/1.15  fof(f68,plain,(
% 4.60/1.15    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.60/1.15    inference(cnf_transformation,[],[f41])).
% 4.60/1.15  fof(f41,plain,(
% 4.60/1.15    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.60/1.15    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 4.60/1.15  fof(f40,plain,(
% 4.60/1.15    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 4.60/1.15    introduced(choice_axiom,[])).
% 4.60/1.15  fof(f39,plain,(
% 4.60/1.15    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.60/1.15    inference(rectify,[],[f38])).
% 4.60/1.15  fof(f38,plain,(
% 4.60/1.15    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.60/1.15    inference(flattening,[],[f37])).
% 4.60/1.15  fof(f37,plain,(
% 4.60/1.15    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.60/1.15    inference(nnf_transformation,[],[f4])).
% 4.60/1.15  fof(f4,axiom,(
% 4.60/1.15    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.60/1.15    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 4.60/1.15  fof(f1400,plain,(
% 4.60/1.15    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 4.60/1.15    inference(superposition,[],[f407,f52])).
% 4.60/1.15  fof(f52,plain,(
% 4.60/1.15    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.60/1.15    inference(cnf_transformation,[],[f18])).
% 4.60/1.15  fof(f18,axiom,(
% 4.60/1.15    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.60/1.15    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 4.60/1.15  fof(f407,plain,(
% 4.60/1.15    ( ! [X0] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1))) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)) )),
% 4.60/1.15    inference(resolution,[],[f227,f81])).
% 4.60/1.15  fof(f227,plain,(
% 4.60/1.15    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 4.60/1.15    inference(subsumption_resolution,[],[f215,f117])).
% 4.60/1.15  fof(f117,plain,(
% 4.60/1.15    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.60/1.15    inference(equality_resolution,[],[f87])).
% 4.60/1.15  fof(f87,plain,(
% 4.60/1.15    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 4.60/1.15    inference(superposition,[],[f42,f70])).
% 4.60/1.15  fof(f70,plain,(
% 4.60/1.15    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 4.60/1.15    inference(cnf_transformation,[],[f41])).
% 4.60/1.15  fof(f42,plain,(
% 4.60/1.15    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.60/1.15    inference(cnf_transformation,[],[f30])).
% 4.60/1.15  fof(f30,plain,(
% 4.60/1.15    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.60/1.15    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f29])).
% 4.60/1.15  fof(f29,plain,(
% 4.60/1.15    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.60/1.15    introduced(choice_axiom,[])).
% 4.60/1.15  fof(f24,plain,(
% 4.60/1.15    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.60/1.15    inference(ennf_transformation,[],[f21])).
% 4.60/1.16  fof(f21,negated_conjecture,(
% 4.60/1.16    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.60/1.16    inference(negated_conjecture,[],[f20])).
% 4.60/1.16  fof(f20,conjecture,(
% 4.60/1.16    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.60/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.60/1.16  fof(f215,plain,(
% 4.60/1.16    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.60/1.16    inference(resolution,[],[f123,f80])).
% 4.60/1.16  fof(f80,plain,(
% 4.60/1.16    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 4.60/1.16    inference(equality_resolution,[],[f69])).
% 4.60/1.16  fof(f69,plain,(
% 4.60/1.16    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 4.60/1.16    inference(cnf_transformation,[],[f41])).
% 4.60/1.16  fof(f123,plain,(
% 4.60/1.16    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 4.60/1.16    inference(equality_resolution,[],[f88])).
% 4.60/1.16  fof(f88,plain,(
% 4.60/1.16    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 4.60/1.16    inference(superposition,[],[f42,f71])).
% 4.60/1.16  fof(f71,plain,(
% 4.60/1.16    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 4.60/1.16    inference(cnf_transformation,[],[f41])).
% 4.60/1.16  fof(f1080,plain,(
% 4.60/1.16    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.60/1.16    inference(duplicate_literal_removal,[],[f1072])).
% 4.60/1.16  fof(f1072,plain,(
% 4.60/1.16    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.60/1.16    inference(superposition,[],[f295,f52])).
% 4.60/1.16  fof(f295,plain,(
% 4.60/1.16    ( ! [X1] : (r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1))) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 4.60/1.16    inference(resolution,[],[f135,f80])).
% 4.60/1.16  fof(f135,plain,(
% 4.60/1.16    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 4.60/1.16    inference(equality_resolution,[],[f89])).
% 4.60/1.16  fof(f89,plain,(
% 4.60/1.16    ( ! [X2] : (k3_xboole_0(sK0,sK1) != X2 | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),sK0) | ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),X2),X2)) )),
% 4.60/1.16    inference(superposition,[],[f42,f72])).
% 4.60/1.16  fof(f72,plain,(
% 4.60/1.16    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 4.60/1.16    inference(cnf_transformation,[],[f41])).
% 4.60/1.16  fof(f1759,plain,(
% 4.60/1.16    r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.60/1.16    inference(resolution,[],[f1456,f48])).
% 4.60/1.16  fof(f48,plain,(
% 4.60/1.16    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.60/1.16    inference(cnf_transformation,[],[f10])).
% 4.60/1.16  fof(f10,axiom,(
% 4.60/1.16    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.60/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 4.60/1.16  fof(f1456,plain,(
% 4.60/1.16    ( ! [X7] : (~r1_tarski(k3_xboole_0(sK0,sK1),X7) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X7)) )),
% 4.60/1.16    inference(subsumption_resolution,[],[f779,f1424])).
% 4.60/1.16  fof(f779,plain,(
% 4.60/1.16    ( ! [X7] : (r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X7) | ~r1_tarski(k3_xboole_0(sK0,sK1),X7)) )),
% 4.60/1.16    inference(subsumption_resolution,[],[f769,f455])).
% 4.60/1.16  fof(f455,plain,(
% 4.60/1.16    ~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.60/1.16    inference(superposition,[],[f189,f73])).
% 4.60/1.16  fof(f73,plain,(
% 4.60/1.16    ( ! [X0] : (o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0)) )),
% 4.60/1.16    inference(definition_unfolding,[],[f44,f43,f43])).
% 4.60/1.16  fof(f43,plain,(
% 4.60/1.16    k1_xboole_0 = o_0_0_xboole_0),
% 4.60/1.16    inference(cnf_transformation,[],[f3])).
% 4.60/1.16  fof(f3,axiom,(
% 4.60/1.16    k1_xboole_0 = o_0_0_xboole_0),
% 4.60/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 4.60/1.16  fof(f44,plain,(
% 4.60/1.16    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 4.60/1.16    inference(cnf_transformation,[],[f19])).
% 4.60/1.16  fof(f19,axiom,(
% 4.60/1.16    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 4.60/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 4.60/1.16  fof(f189,plain,(
% 4.60/1.16    ( ! [X0] : (~r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1))) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)) )),
% 4.60/1.16    inference(resolution,[],[f117,f81])).
% 4.60/1.16  fof(f769,plain,(
% 4.60/1.16    ( ! [X7] : (r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),o_0_0_xboole_0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X7) | ~r1_tarski(k3_xboole_0(sK0,sK1),X7)) )),
% 4.60/1.16    inference(superposition,[],[f190,f78])).
% 4.60/1.16  fof(f78,plain,(
% 4.60/1.16    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 4.60/1.16    inference(definition_unfolding,[],[f61,f43])).
% 4.60/1.16  fof(f61,plain,(
% 4.60/1.16    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 4.60/1.16    inference(cnf_transformation,[],[f34])).
% 4.60/1.16  fof(f34,plain,(
% 4.60/1.16    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 4.60/1.16    inference(nnf_transformation,[],[f8])).
% 4.60/1.16  fof(f8,axiom,(
% 4.60/1.16    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 4.60/1.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.60/1.16  fof(f190,plain,(
% 4.60/1.16    ( ! [X1] : (r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1)) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK4(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 4.60/1.16    inference(resolution,[],[f117,f80])).
% 4.60/1.16  % SZS output end Proof for theBenchmark
% 4.60/1.16  % (28625)------------------------------
% 4.60/1.16  % (28625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.60/1.16  % (28625)Termination reason: Refutation
% 4.60/1.16  
% 4.60/1.16  % (28625)Memory used [KB]: 8059
% 4.60/1.16  % (28625)Time elapsed: 0.468 s
% 4.60/1.16  % (28625)------------------------------
% 4.60/1.16  % (28625)------------------------------
% 4.60/1.16  % (28794)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 6.26/1.17  % (28560)Success in time 0.793 s
%------------------------------------------------------------------------------
