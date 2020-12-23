%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:04 EST 2020

% Result     : Theorem 4.36s
% Output     : Refutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 417 expanded)
%              Number of leaves         :   10 ( 103 expanded)
%              Depth                    :   21
%              Number of atoms          :  220 (2508 expanded)
%              Number of equality atoms :   33 ( 416 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6304,plain,(
    $false ),
    inference(resolution,[],[f6244,f6181])).

fof(f6181,plain,(
    r2_hidden(sK4(k3_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f6017,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f6017,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f6015,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f6015,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f5972,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f5972,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) ),
    inference(subsumption_resolution,[],[f5971,f699])).

fof(f699,plain,(
    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f684,f92])).

fof(f92,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f42,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f42,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f29])).

fof(f29,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f684,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f641,f93])).

fof(f93,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f42,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f641,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(duplicate_literal_removal,[],[f635])).

fof(f635,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(superposition,[],[f184,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f184,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f100,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2] :
      ( k3_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),sK0)
      | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f42,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5971,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0))
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f5970,f834])).

fof(f834,plain,(
    ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f827,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f827,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(superposition,[],[f237,f52])).

fof(f237,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ) ),
    inference(resolution,[],[f119,f69])).

fof(f119,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f112,f92])).

fof(f112,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(resolution,[],[f93,f68])).

fof(f5970,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0))
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f5961,f42])).

fof(f5961,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0))
    | k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f1192,f67])).

fof(f1192,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) ),
    inference(factoring,[],[f434])).

fof(f434,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)
      | ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),X1)) ) ),
    inference(duplicate_literal_removal,[],[f416])).

fof(f416,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)
      | ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),X1))
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ) ),
    inference(resolution,[],[f104,f105])).

fof(f105,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X2)
      | ~ r1_xboole_0(k3_xboole_0(sK0,sK1),X2)
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ) ),
    inference(resolution,[],[f92,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f104,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1))
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f92,f68])).

fof(f6244,plain,(
    ! [X0] : ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f6239,f44])).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f6239,plain,(
    ! [X0] : ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f6181,f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:51:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (6680)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (6697)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (6681)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (6677)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (6674)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (6677)Refutation not found, incomplete strategy% (6677)------------------------------
% 0.21/0.53  % (6677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6677)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6677)Memory used [KB]: 6140
% 0.21/0.53  % (6677)Time elapsed: 0.113 s
% 0.21/0.53  % (6677)------------------------------
% 0.21/0.53  % (6677)------------------------------
% 0.21/0.55  % (6673)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (6696)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (6673)Refutation not found, incomplete strategy% (6673)------------------------------
% 0.21/0.55  % (6673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6673)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6673)Memory used [KB]: 10618
% 0.21/0.55  % (6673)Time elapsed: 0.120 s
% 0.21/0.55  % (6673)------------------------------
% 0.21/0.55  % (6673)------------------------------
% 0.21/0.55  % (6691)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (6676)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.56  % (6678)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.56  % (6682)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.56  % (6694)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.58  % (6678)Refutation not found, incomplete strategy% (6678)------------------------------
% 0.21/0.58  % (6678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (6678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (6678)Memory used [KB]: 10490
% 0.21/0.58  % (6678)Time elapsed: 0.154 s
% 0.21/0.58  % (6678)------------------------------
% 0.21/0.58  % (6678)------------------------------
% 0.21/0.58  % (6675)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.59  % (6684)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.59  % (6672)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.59  % (6690)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.81/0.59  % (6693)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.81/0.60  % (6679)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.81/0.60  % (6695)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.81/0.60  % (6688)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.81/0.60  % (6686)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.81/0.60  % (6689)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.81/0.61  % (6698)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.81/0.61  % (6692)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 2.00/0.62  % (6683)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 2.20/0.64  % (6685)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 2.20/0.64  % (6683)Refutation not found, incomplete strategy% (6683)------------------------------
% 2.20/0.64  % (6683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.64  % (6683)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.64  
% 2.20/0.64  % (6683)Memory used [KB]: 10490
% 2.20/0.64  % (6683)Time elapsed: 0.204 s
% 2.20/0.64  % (6683)------------------------------
% 2.20/0.64  % (6683)------------------------------
% 2.20/0.65  % (6681)Refutation not found, incomplete strategy% (6681)------------------------------
% 2.20/0.65  % (6681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.65  % (6681)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.65  
% 2.20/0.65  % (6681)Memory used [KB]: 6012
% 2.20/0.65  % (6681)Time elapsed: 0.218 s
% 2.20/0.65  % (6681)------------------------------
% 2.20/0.65  % (6681)------------------------------
% 4.36/0.93  % (6691)Refutation found. Thanks to Tanya!
% 4.36/0.93  % SZS status Theorem for theBenchmark
% 4.57/0.94  % SZS output start Proof for theBenchmark
% 4.57/0.94  fof(f6304,plain,(
% 4.57/0.94    $false),
% 4.57/0.94    inference(resolution,[],[f6244,f6181])).
% 4.57/0.94  fof(f6181,plain,(
% 4.57/0.94    r2_hidden(sK4(k3_xboole_0(sK0,sK1),k1_xboole_0),k1_xboole_0)),
% 4.57/0.94    inference(resolution,[],[f6017,f56])).
% 4.57/0.94  fof(f56,plain,(
% 4.57/0.94    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 4.57/0.94    inference(cnf_transformation,[],[f36])).
% 4.57/0.94  fof(f36,plain,(
% 4.57/0.94    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.57/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f35])).
% 4.57/0.94  fof(f35,plain,(
% 4.57/0.94    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 4.57/0.94    introduced(choice_axiom,[])).
% 4.57/0.94  fof(f26,plain,(
% 4.57/0.94    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.57/0.94    inference(ennf_transformation,[],[f21])).
% 4.57/0.94  fof(f21,plain,(
% 4.57/0.94    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.57/0.94    inference(rectify,[],[f4])).
% 4.57/0.94  fof(f4,axiom,(
% 4.57/0.94    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.57/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 4.57/0.94  fof(f6017,plain,(
% 4.57/0.94    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)),
% 4.57/0.94    inference(subsumption_resolution,[],[f6015,f47])).
% 4.57/0.94  fof(f47,plain,(
% 4.57/0.94    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.57/0.94    inference(cnf_transformation,[],[f9])).
% 4.57/0.94  fof(f9,axiom,(
% 4.57/0.94    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.57/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 4.57/0.94  fof(f6015,plain,(
% 4.57/0.94    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 4.57/0.94    inference(superposition,[],[f5972,f59])).
% 4.57/0.94  fof(f59,plain,(
% 4.57/0.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 4.57/0.94    inference(cnf_transformation,[],[f28])).
% 4.57/0.94  fof(f28,plain,(
% 4.57/0.94    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 4.57/0.94    inference(ennf_transformation,[],[f22])).
% 4.57/0.94  fof(f22,plain,(
% 4.57/0.94    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 4.57/0.94    inference(unused_predicate_definition_removal,[],[f7])).
% 4.57/0.94  fof(f7,axiom,(
% 4.57/0.94    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.57/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.57/0.94  fof(f5972,plain,(
% 4.57/0.94    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0))),
% 4.57/0.94    inference(subsumption_resolution,[],[f5971,f699])).
% 4.57/0.94  fof(f699,plain,(
% 4.57/0.94    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 4.57/0.94    inference(subsumption_resolution,[],[f684,f92])).
% 4.57/0.94  fof(f92,plain,(
% 4.57/0.94    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.57/0.94    inference(equality_resolution,[],[f75])).
% 4.57/0.94  fof(f75,plain,(
% 4.57/0.94    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 4.57/0.94    inference(superposition,[],[f42,f65])).
% 4.57/0.94  fof(f65,plain,(
% 4.57/0.94    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 4.57/0.94    inference(cnf_transformation,[],[f41])).
% 4.57/0.94  fof(f41,plain,(
% 4.57/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.57/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 4.57/0.94  fof(f40,plain,(
% 4.57/0.94    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 4.57/0.94    introduced(choice_axiom,[])).
% 4.57/0.94  fof(f39,plain,(
% 4.57/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.57/0.94    inference(rectify,[],[f38])).
% 4.57/0.94  fof(f38,plain,(
% 4.57/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.57/0.94    inference(flattening,[],[f37])).
% 4.57/0.94  fof(f37,plain,(
% 4.57/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.57/0.94    inference(nnf_transformation,[],[f3])).
% 4.57/0.94  fof(f3,axiom,(
% 4.57/0.94    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.57/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 4.57/0.94  fof(f42,plain,(
% 4.57/0.94    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.57/0.94    inference(cnf_transformation,[],[f30])).
% 4.57/0.94  fof(f30,plain,(
% 4.57/0.94    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.57/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f29])).
% 4.57/0.94  fof(f29,plain,(
% 4.57/0.94    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.57/0.94    introduced(choice_axiom,[])).
% 4.57/0.94  fof(f23,plain,(
% 4.57/0.94    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.57/0.94    inference(ennf_transformation,[],[f19])).
% 4.57/0.94  fof(f19,negated_conjecture,(
% 4.57/0.94    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.57/0.94    inference(negated_conjecture,[],[f18])).
% 4.57/0.94  fof(f18,conjecture,(
% 4.57/0.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.57/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.57/0.94  fof(f684,plain,(
% 4.57/0.94    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 4.57/0.94    inference(resolution,[],[f641,f93])).
% 4.57/0.94  fof(f93,plain,(
% 4.57/0.94    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 4.57/0.94    inference(equality_resolution,[],[f76])).
% 4.57/0.94  fof(f76,plain,(
% 4.57/0.94    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 4.57/0.94    inference(superposition,[],[f42,f66])).
% 4.57/0.94  fof(f66,plain,(
% 4.57/0.94    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 4.57/0.94    inference(cnf_transformation,[],[f41])).
% 4.57/0.94  fof(f641,plain,(
% 4.57/0.94    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.57/0.94    inference(duplicate_literal_removal,[],[f635])).
% 4.57/0.94  fof(f635,plain,(
% 4.57/0.94    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.57/0.94    inference(superposition,[],[f184,f52])).
% 4.57/0.94  fof(f52,plain,(
% 4.57/0.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.57/0.94    inference(cnf_transformation,[],[f17])).
% 4.57/0.94  fof(f17,axiom,(
% 4.57/0.94    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.57/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 4.57/0.94  fof(f184,plain,(
% 4.57/0.94    ( ! [X1] : (r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1))) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 4.57/0.94    inference(resolution,[],[f100,f68])).
% 4.57/0.94  fof(f68,plain,(
% 4.57/0.94    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 4.57/0.94    inference(equality_resolution,[],[f64])).
% 4.57/0.94  fof(f64,plain,(
% 4.57/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 4.57/0.94    inference(cnf_transformation,[],[f41])).
% 4.57/0.94  fof(f100,plain,(
% 4.57/0.94    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 4.57/0.94    inference(equality_resolution,[],[f77])).
% 4.57/0.94  fof(f77,plain,(
% 4.57/0.94    ( ! [X2] : (k3_xboole_0(sK0,sK1) != X2 | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),sK0) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X2),X2)) )),
% 4.57/0.94    inference(superposition,[],[f42,f67])).
% 4.57/0.94  fof(f67,plain,(
% 4.57/0.94    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 4.57/0.94    inference(cnf_transformation,[],[f41])).
% 4.57/0.94  fof(f5971,plain,(
% 4.57/0.94    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 4.57/0.94    inference(subsumption_resolution,[],[f5970,f834])).
% 4.57/0.94  fof(f834,plain,(
% 4.57/0.94    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 4.57/0.94    inference(subsumption_resolution,[],[f827,f69])).
% 4.57/0.94  fof(f69,plain,(
% 4.57/0.94    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 4.57/0.94    inference(equality_resolution,[],[f63])).
% 4.57/0.94  fof(f63,plain,(
% 4.57/0.94    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.57/0.94    inference(cnf_transformation,[],[f41])).
% 4.57/0.94  fof(f827,plain,(
% 4.57/0.94    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 4.57/0.94    inference(superposition,[],[f237,f52])).
% 4.57/0.94  fof(f237,plain,(
% 4.57/0.94    ( ! [X0] : (~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1))) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)) )),
% 4.57/0.94    inference(resolution,[],[f119,f69])).
% 4.57/0.94  fof(f119,plain,(
% 4.57/0.94    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 4.57/0.94    inference(subsumption_resolution,[],[f112,f92])).
% 4.57/0.94  fof(f112,plain,(
% 4.57/0.94    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.57/0.94    inference(resolution,[],[f93,f68])).
% 4.57/0.94  fof(f5970,plain,(
% 4.57/0.94    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 4.57/0.94    inference(subsumption_resolution,[],[f5961,f42])).
% 4.57/0.94  fof(f5961,plain,(
% 4.57/0.94    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) | k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 4.57/0.94    inference(resolution,[],[f1192,f67])).
% 4.57/0.94  fof(f1192,plain,(
% 4.57/0.94    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK0))),
% 4.57/0.94    inference(factoring,[],[f434])).
% 4.57/0.94  fof(f434,plain,(
% 4.57/0.94    ( ! [X1] : (r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) | ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),X1))) )),
% 4.57/0.94    inference(duplicate_literal_removal,[],[f416])).
% 4.57/0.94  fof(f416,plain,(
% 4.57/0.94    ( ! [X1] : (r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) | ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),X1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)) )),
% 4.57/0.94    inference(resolution,[],[f104,f105])).
% 4.57/0.94  fof(f105,plain,(
% 4.57/0.94    ( ! [X2] : (~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X2) | ~r1_xboole_0(k3_xboole_0(sK0,sK1),X2) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)) )),
% 4.57/0.94    inference(resolution,[],[f92,f57])).
% 4.57/0.94  fof(f57,plain,(
% 4.57/0.94    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.57/0.94    inference(cnf_transformation,[],[f36])).
% 4.57/0.94  fof(f104,plain,(
% 4.57/0.94    ( ! [X1] : (r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 4.57/0.94    inference(resolution,[],[f92,f68])).
% 4.57/0.94  fof(f6244,plain,(
% 4.57/0.94    ( ! [X0] : (~r2_hidden(sK4(k3_xboole_0(sK0,sK1),k1_xboole_0),X0)) )),
% 4.57/0.94    inference(forward_demodulation,[],[f6239,f44])).
% 4.57/0.94  fof(f44,plain,(
% 4.57/0.94    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.57/0.94    inference(cnf_transformation,[],[f15])).
% 4.57/0.94  fof(f15,axiom,(
% 4.57/0.94    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.57/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 4.57/0.94  fof(f6239,plain,(
% 4.57/0.94    ( ! [X0] : (~r2_hidden(sK4(k3_xboole_0(sK0,sK1),k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) )),
% 4.57/0.94    inference(resolution,[],[f6181,f69])).
% 4.57/0.94  % SZS output end Proof for theBenchmark
% 4.57/0.94  % (6691)------------------------------
% 4.57/0.94  % (6691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.57/0.94  % (6691)Termination reason: Refutation
% 4.57/0.94  
% 4.57/0.94  % (6691)Memory used [KB]: 3582
% 4.57/0.94  % (6691)Time elapsed: 0.500 s
% 4.57/0.94  % (6691)------------------------------
% 4.57/0.94  % (6691)------------------------------
% 4.57/0.94  % (6671)Success in time 0.579 s
%------------------------------------------------------------------------------
