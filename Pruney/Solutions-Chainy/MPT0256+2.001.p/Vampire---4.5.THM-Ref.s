%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:59 EST 2020

% Result     : Theorem 3.91s
% Output     : Refutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  104 (6981 expanded)
%              Number of leaves         :   19 (2323 expanded)
%              Depth                    :   35
%              Number of atoms          :  291 (11269 expanded)
%              Number of equality atoms :  130 (7143 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3057,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3049,f1674])).

fof(f1674,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f1610,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1610,plain,(
    ! [X6] : ~ r2_hidden(X6,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f1608])).

fof(f1608,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | ~ r2_hidden(X6,k1_xboole_0) ) ),
    inference(superposition,[],[f90,f1562])).

fof(f1562,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1560,f1559])).

fof(f1559,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f460,f1558])).

fof(f1558,plain,(
    ! [X7] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7)) ),
    inference(forward_demodulation,[],[f1557,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1557,plain,(
    ! [X7] : k1_xboole_0 = k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7)) ),
    inference(forward_demodulation,[],[f1553,f80])).

fof(f1553,plain,(
    ! [X7] : k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7)),k4_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7))) ),
    inference(superposition,[],[f211,f97])).

fof(f97,plain,(
    ! [X1] : k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1) = k3_xboole_0(sK0,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1)) ),
    inference(superposition,[],[f62,f79])).

fof(f79,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f45,f49,f49])).

fof(f49,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).

fof(f45,plain,(
    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_hidden(sK1,sK0)
    & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) )
   => ( ~ r2_hidden(sK1,sK0)
      & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
       => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f211,plain,(
    ! [X10,X9] : k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X10),k4_xboole_0(X10,sK0)),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X9)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X9),k3_xboole_0(X10,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X9))),k4_xboole_0(k3_xboole_0(X10,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X9)),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X9))) ),
    inference(superposition,[],[f82,f97])).

fof(f82,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)),k4_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X0,X1))) = k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X2,X0)),X1) ),
    inference(definition_unfolding,[],[f65,f53,f53])).

fof(f65,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f460,plain,(
    ! [X1] : k3_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f62,f327])).

fof(f327,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f326,f80])).

fof(f326,plain,(
    k1_xboole_0 = k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f325,f80])).

fof(f325,plain,(
    k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f100,f79])).

fof(f100,plain,(
    ! [X4] : k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X4),k4_xboole_0(X4,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k4_xboole_0(k3_xboole_0(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f82,f79])).

fof(f1560,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f462,f1559])).

fof(f462,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X3),k1_xboole_0) ),
    inference(superposition,[],[f64,f327])).

fof(f64,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
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

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f3049,plain,(
    ! [X0] : ~ r1_xboole_0(k2_tarski(X0,sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f540,f3048])).

fof(f3048,plain,(
    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(forward_demodulation,[],[f3047,f327])).

fof(f3047,plain,(
    k3_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(forward_demodulation,[],[f3046,f2484])).

fof(f2484,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) ),
    inference(superposition,[],[f2410,f80])).

fof(f2410,plain,(
    ! [X12] : k2_xboole_0(X12,X12) = X12 ),
    inference(superposition,[],[f2254,f1859])).

fof(f1859,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f1674,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f2254,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f2253,f1859])).

fof(f2253,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f2200,f1559])).

fof(f2200,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f63,f1859])).

fof(f63,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f3046,plain,(
    k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) = k3_xboole_0(k4_xboole_0(sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f3045,f2485])).

fof(f2485,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(X4,k3_xboole_0(X5,X5)) ),
    inference(superposition,[],[f2410,f63])).

fof(f3045,plain,(
    k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) = k3_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f3044,f63])).

fof(f3044,plain,(
    k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(forward_demodulation,[],[f3043,f2773])).

fof(f2773,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f2534,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2534,plain,(
    ! [X13] : k2_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(superposition,[],[f2254,f2484])).

fof(f3043,plain,(
    k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)) ),
    inference(forward_demodulation,[],[f3017,f2484])).

fof(f3017,plain,(
    k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)) ),
    inference(superposition,[],[f2804,f79])).

% (27979)Time limit reached!
% (27979)------------------------------
% (27979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27979)Termination reason: Time limit

% (27979)Memory used [KB]: 4733
% (27979)Time elapsed: 0.512 s
% (27979)------------------------------
% (27979)------------------------------
fof(f2804,plain,(
    ! [X5] : k3_xboole_0(k2_xboole_0(k4_xboole_0(X5,sK0),k4_xboole_0(sK0,X5)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X5,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X5)) ),
    inference(backward_demodulation,[],[f2631,f2773])).

fof(f2631,plain,(
    ! [X5] : k3_xboole_0(k2_xboole_0(k4_xboole_0(X5,sK0),k4_xboole_0(sK0,X5)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X5,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k2_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X5))) ),
    inference(backward_demodulation,[],[f101,f2612])).

fof(f2612,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k3_xboole_0(X4,X3)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f2529,f52])).

fof(f2529,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k3_xboole_0(X4,X3)) = k2_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0) ),
    inference(superposition,[],[f63,f2484])).

fof(f101,plain,(
    ! [X5] : k3_xboole_0(k2_xboole_0(k4_xboole_0(X5,sK0),k4_xboole_0(sK0,X5)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X5,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(X5,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f82,f79])).

fof(f540,plain,(
    ! [X0] : ~ r1_xboole_0(k2_tarski(X0,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)) ),
    inference(unit_resulting_resolution,[],[f113,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f113,plain,(
    ! [X0] : ~ r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k2_tarski(X0,sK1),sK0)) ),
    inference(unit_resulting_resolution,[],[f93,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f49])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f93,plain,(
    ! [X0] : r2_hidden(sK1,k4_xboole_0(k2_tarski(X0,sK1),sK0)) ),
    inference(unit_resulting_resolution,[],[f85,f46,f89])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f46,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (27989)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (27963)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (27987)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (27977)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (27979)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.49/0.56  % (27992)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.49/0.56  % (27985)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.49/0.56  % (27966)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.49/0.57  % (27974)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.49/0.57  % (27986)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.57  % (27971)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.49/0.57  % (27969)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.57  % (27984)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.49/0.57  % (27965)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.49/0.57  % (27964)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.49/0.57  % (27967)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.49/0.57  % (27970)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.49/0.57  % (27981)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.49/0.58  % (27976)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.49/0.58  % (27972)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.68/0.58  % (27991)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.68/0.58  % (27993)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.68/0.58  % (27982)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.68/0.59  % (27980)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.68/0.59  % (27990)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.68/0.60  % (27981)Refutation not found, incomplete strategy% (27981)------------------------------
% 1.68/0.60  % (27981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.60  % (27981)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.60  
% 1.68/0.60  % (27981)Memory used [KB]: 10618
% 1.68/0.60  % (27981)Time elapsed: 0.164 s
% 1.68/0.60  % (27981)------------------------------
% 1.68/0.60  % (27981)------------------------------
% 1.68/0.60  % (27988)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.68/0.60  % (27968)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.68/0.61  % (27983)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.68/0.61  % (27978)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.68/0.62  % (27994)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.68/0.62  % (27994)Refutation not found, incomplete strategy% (27994)------------------------------
% 1.68/0.62  % (27994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.62  % (27994)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.62  
% 1.68/0.62  % (27994)Memory used [KB]: 1663
% 1.68/0.62  % (27994)Time elapsed: 0.205 s
% 1.68/0.62  % (27994)------------------------------
% 1.68/0.62  % (27994)------------------------------
% 2.89/0.78  % (28018)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.89/0.78  % (28020)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.51/0.85  % (27965)Time limit reached!
% 3.51/0.85  % (27965)------------------------------
% 3.51/0.85  % (27965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/0.85  % (27989)Time limit reached!
% 3.51/0.85  % (27989)------------------------------
% 3.51/0.85  % (27989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/0.86  % (27965)Termination reason: Time limit
% 3.51/0.86  % (27965)Termination phase: Saturation
% 3.51/0.86  
% 3.51/0.86  % (27965)Memory used [KB]: 8443
% 3.51/0.86  % (27965)Time elapsed: 0.400 s
% 3.51/0.86  % (27965)------------------------------
% 3.51/0.86  % (27965)------------------------------
% 3.51/0.87  % (27989)Termination reason: Time limit
% 3.51/0.87  % (27989)Termination phase: Saturation
% 3.51/0.87  
% 3.51/0.87  % (27989)Memory used [KB]: 16375
% 3.51/0.87  % (27989)Time elapsed: 0.400 s
% 3.51/0.87  % (27989)------------------------------
% 3.51/0.87  % (27989)------------------------------
% 3.91/0.90  % (27976)Refutation found. Thanks to Tanya!
% 3.91/0.90  % SZS status Theorem for theBenchmark
% 3.91/0.91  % SZS output start Proof for theBenchmark
% 3.91/0.91  fof(f3057,plain,(
% 3.91/0.91    $false),
% 3.91/0.91    inference(subsumption_resolution,[],[f3049,f1674])).
% 3.91/0.91  fof(f1674,plain,(
% 3.91/0.91    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.91/0.91    inference(unit_resulting_resolution,[],[f1610,f57])).
% 3.91/0.91  fof(f57,plain,(
% 3.91/0.91    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.91/0.91    inference(cnf_transformation,[],[f33])).
% 3.91/0.91  fof(f33,plain,(
% 3.91/0.91    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.91/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f32])).
% 3.91/0.91  fof(f32,plain,(
% 3.91/0.91    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 3.91/0.91    introduced(choice_axiom,[])).
% 3.91/0.91  fof(f25,plain,(
% 3.91/0.91    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.91/0.91    inference(ennf_transformation,[],[f21])).
% 3.91/0.91  fof(f21,plain,(
% 3.91/0.91    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.91/0.91    inference(rectify,[],[f4])).
% 3.91/0.91  fof(f4,axiom,(
% 3.91/0.91    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 3.91/0.91  fof(f1610,plain,(
% 3.91/0.91    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0)) )),
% 3.91/0.91    inference(duplicate_literal_removal,[],[f1608])).
% 3.91/0.91  fof(f1608,plain,(
% 3.91/0.91    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0) | ~r2_hidden(X6,k1_xboole_0)) )),
% 3.91/0.91    inference(superposition,[],[f90,f1562])).
% 3.91/0.91  fof(f1562,plain,(
% 3.91/0.91    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.91/0.91    inference(forward_demodulation,[],[f1560,f1559])).
% 3.91/0.91  fof(f1559,plain,(
% 3.91/0.91    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 3.91/0.91    inference(backward_demodulation,[],[f460,f1558])).
% 3.91/0.91  fof(f1558,plain,(
% 3.91/0.91    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7))) )),
% 3.91/0.91    inference(forward_demodulation,[],[f1557,f80])).
% 3.91/0.91  fof(f80,plain,(
% 3.91/0.91    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) )),
% 3.91/0.91    inference(definition_unfolding,[],[f48,f53])).
% 3.91/0.91  fof(f53,plain,(
% 3.91/0.91    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 3.91/0.91    inference(cnf_transformation,[],[f3])).
% 3.91/0.91  fof(f3,axiom,(
% 3.91/0.91    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 3.91/0.91  fof(f48,plain,(
% 3.91/0.91    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.91/0.91    inference(cnf_transformation,[],[f14])).
% 3.91/0.91  fof(f14,axiom,(
% 3.91/0.91    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 3.91/0.91  fof(f1557,plain,(
% 3.91/0.91    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7))) )),
% 3.91/0.91    inference(forward_demodulation,[],[f1553,f80])).
% 3.91/0.91  fof(f1553,plain,(
% 3.91/0.91    ( ! [X7] : (k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7)),k4_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X7)))) )),
% 3.91/0.91    inference(superposition,[],[f211,f97])).
% 3.91/0.91  fof(f97,plain,(
% 3.91/0.91    ( ! [X1] : (k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1) = k3_xboole_0(sK0,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1))) )),
% 3.91/0.91    inference(superposition,[],[f62,f79])).
% 3.91/0.91  fof(f79,plain,(
% 3.91/0.91    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 3.91/0.91    inference(definition_unfolding,[],[f45,f49,f49])).
% 3.91/0.91  fof(f49,plain,(
% 3.91/0.91    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.91/0.91    inference(cnf_transformation,[],[f16])).
% 3.91/0.91  fof(f16,axiom,(
% 3.91/0.91    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).
% 3.91/0.91  fof(f45,plain,(
% 3.91/0.91    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1))),
% 3.91/0.91    inference(cnf_transformation,[],[f29])).
% 3.91/0.91  fof(f29,plain,(
% 3.91/0.91    ~r2_hidden(sK1,sK0) & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1))),
% 3.91/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f28])).
% 3.91/0.91  fof(f28,plain,(
% 3.91/0.91    ? [X0,X1] : (~r2_hidden(X1,X0) & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))) => (~r2_hidden(sK1,sK0) & k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)))),
% 3.91/0.91    introduced(choice_axiom,[])).
% 3.91/0.91  fof(f22,plain,(
% 3.91/0.91    ? [X0,X1] : (~r2_hidden(X1,X0) & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)))),
% 3.91/0.91    inference(ennf_transformation,[],[f19])).
% 3.91/0.91  fof(f19,negated_conjecture,(
% 3.91/0.91    ~! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 3.91/0.91    inference(negated_conjecture,[],[f18])).
% 3.91/0.91  fof(f18,conjecture,(
% 3.91/0.91    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).
% 3.91/0.91  fof(f62,plain,(
% 3.91/0.91    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 3.91/0.91    inference(cnf_transformation,[],[f8])).
% 3.91/0.91  fof(f8,axiom,(
% 3.91/0.91    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 3.91/0.91  fof(f211,plain,(
% 3.91/0.91    ( ! [X10,X9] : (k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X10),k4_xboole_0(X10,sK0)),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X9)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X9),k3_xboole_0(X10,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X9))),k4_xboole_0(k3_xboole_0(X10,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X9)),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X9)))) )),
% 3.91/0.91    inference(superposition,[],[f82,f97])).
% 3.91/0.91  fof(f82,plain,(
% 3.91/0.91    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)),k4_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X0,X1))) = k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X2,X0)),X1)) )),
% 3.91/0.91    inference(definition_unfolding,[],[f65,f53,f53])).
% 3.91/0.91  fof(f65,plain,(
% 3.91/0.91    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 3.91/0.91    inference(cnf_transformation,[],[f7])).
% 3.91/0.91  fof(f7,axiom,(
% 3.91/0.91    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 3.91/0.91  fof(f460,plain,(
% 3.91/0.91    ( ! [X1] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1)) = k3_xboole_0(k1_xboole_0,X1)) )),
% 3.91/0.91    inference(superposition,[],[f62,f327])).
% 3.91/0.91  fof(f327,plain,(
% 3.91/0.91    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 3.91/0.91    inference(forward_demodulation,[],[f326,f80])).
% 3.91/0.91  fof(f326,plain,(
% 3.91/0.91    k1_xboole_0 = k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 3.91/0.91    inference(forward_demodulation,[],[f325,f80])).
% 3.91/0.91  fof(f325,plain,(
% 3.91/0.91    k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 3.91/0.91    inference(superposition,[],[f100,f79])).
% 3.91/0.91  fof(f100,plain,(
% 3.91/0.91    ( ! [X4] : (k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X4),k4_xboole_0(X4,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k4_xboole_0(k3_xboole_0(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) )),
% 3.91/0.91    inference(superposition,[],[f82,f79])).
% 3.91/0.91  fof(f1560,plain,(
% 3.91/0.91    ( ! [X3] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 3.91/0.91    inference(backward_demodulation,[],[f462,f1559])).
% 3.91/0.91  fof(f462,plain,(
% 3.91/0.91    ( ! [X3] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X3),k1_xboole_0)) )),
% 3.91/0.91    inference(superposition,[],[f64,f327])).
% 3.91/0.91  fof(f64,plain,(
% 3.91/0.91    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 3.91/0.91    inference(cnf_transformation,[],[f10])).
% 3.91/0.91  fof(f10,axiom,(
% 3.91/0.91    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
% 3.91/0.91  fof(f90,plain,(
% 3.91/0.91    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.91/0.91    inference(equality_resolution,[],[f74])).
% 3.91/0.91  fof(f74,plain,(
% 3.91/0.91    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.91/0.91    inference(cnf_transformation,[],[f44])).
% 3.91/0.91  fof(f44,plain,(
% 3.91/0.91    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.91/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 3.91/0.91  fof(f43,plain,(
% 3.91/0.91    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 3.91/0.91    introduced(choice_axiom,[])).
% 3.91/0.91  fof(f42,plain,(
% 3.91/0.91    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.91/0.91    inference(rectify,[],[f41])).
% 3.91/0.91  fof(f41,plain,(
% 3.91/0.91    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.91/0.91    inference(flattening,[],[f40])).
% 3.91/0.91  fof(f40,plain,(
% 3.91/0.91    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.91/0.91    inference(nnf_transformation,[],[f2])).
% 3.91/0.91  fof(f2,axiom,(
% 3.91/0.91    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.91/0.91  fof(f3049,plain,(
% 3.91/0.91    ( ! [X0] : (~r1_xboole_0(k2_tarski(X0,sK1),k1_xboole_0)) )),
% 3.91/0.91    inference(backward_demodulation,[],[f540,f3048])).
% 3.91/0.91  fof(f3048,plain,(
% 3.91/0.91    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 3.91/0.91    inference(forward_demodulation,[],[f3047,f327])).
% 3.91/0.91  fof(f3047,plain,(
% 3.91/0.91    k3_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 3.91/0.91    inference(forward_demodulation,[],[f3046,f2484])).
% 3.91/0.91  fof(f2484,plain,(
% 3.91/0.91    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) )),
% 3.91/0.91    inference(superposition,[],[f2410,f80])).
% 3.91/0.91  fof(f2410,plain,(
% 3.91/0.91    ( ! [X12] : (k2_xboole_0(X12,X12) = X12) )),
% 3.91/0.91    inference(superposition,[],[f2254,f1859])).
% 3.91/0.91  fof(f1859,plain,(
% 3.91/0.91    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.91/0.91    inference(unit_resulting_resolution,[],[f1674,f59])).
% 3.91/0.91  fof(f59,plain,(
% 3.91/0.91    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 3.91/0.91    inference(cnf_transformation,[],[f34])).
% 3.91/0.91  fof(f34,plain,(
% 3.91/0.91    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.91/0.91    inference(nnf_transformation,[],[f13])).
% 3.91/0.91  fof(f13,axiom,(
% 3.91/0.91    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 3.91/0.91  fof(f2254,plain,(
% 3.91/0.91    ( ! [X2,X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1) )),
% 3.91/0.91    inference(forward_demodulation,[],[f2253,f1859])).
% 3.91/0.91  fof(f2253,plain,(
% 3.91/0.91    ( ! [X2,X1] : (k4_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 3.91/0.91    inference(forward_demodulation,[],[f2200,f1559])).
% 3.91/0.91  fof(f2200,plain,(
% 3.91/0.91    ( ! [X2,X1] : (k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 3.91/0.91    inference(superposition,[],[f63,f1859])).
% 3.91/0.91  fof(f63,plain,(
% 3.91/0.91    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 3.91/0.91    inference(cnf_transformation,[],[f6])).
% 3.91/0.91  fof(f6,axiom,(
% 3.91/0.91    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 3.91/0.91  fof(f3046,plain,(
% 3.91/0.91    k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) = k3_xboole_0(k4_xboole_0(sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 3.91/0.91    inference(forward_demodulation,[],[f3045,f2485])).
% 3.91/0.91  fof(f2485,plain,(
% 3.91/0.91    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(X4,k3_xboole_0(X5,X5))) )),
% 3.91/0.91    inference(superposition,[],[f2410,f63])).
% 3.91/0.91  fof(f3045,plain,(
% 3.91/0.91    k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) = k3_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 3.91/0.91    inference(forward_demodulation,[],[f3044,f63])).
% 3.91/0.91  fof(f3044,plain,(
% 3.91/0.91    k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 3.91/0.91    inference(forward_demodulation,[],[f3043,f2773])).
% 3.91/0.91  fof(f2773,plain,(
% 3.91/0.91    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 3.91/0.91    inference(superposition,[],[f2534,f52])).
% 3.91/0.91  fof(f52,plain,(
% 3.91/0.91    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.91/0.91    inference(cnf_transformation,[],[f1])).
% 3.91/0.91  fof(f1,axiom,(
% 3.91/0.91    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.91/0.91  fof(f2534,plain,(
% 3.91/0.91    ( ! [X13] : (k2_xboole_0(X13,k1_xboole_0) = X13) )),
% 3.91/0.91    inference(superposition,[],[f2254,f2484])).
% 3.91/0.91  fof(f3043,plain,(
% 3.91/0.91    k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0))),
% 3.91/0.91    inference(forward_demodulation,[],[f3017,f2484])).
% 3.91/0.91  fof(f3017,plain,(
% 3.91/0.91    k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0))),
% 3.91/0.91    inference(superposition,[],[f2804,f79])).
% 3.91/0.91  % (27979)Time limit reached!
% 3.91/0.91  % (27979)------------------------------
% 3.91/0.91  % (27979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.91  % (27979)Termination reason: Time limit
% 3.91/0.91  
% 3.91/0.91  % (27979)Memory used [KB]: 4733
% 3.91/0.91  % (27979)Time elapsed: 0.512 s
% 3.91/0.91  % (27979)------------------------------
% 3.91/0.91  % (27979)------------------------------
% 3.91/0.91  fof(f2804,plain,(
% 3.91/0.91    ( ! [X5] : (k3_xboole_0(k2_xboole_0(k4_xboole_0(X5,sK0),k4_xboole_0(sK0,X5)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X5,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X5))) )),
% 3.91/0.91    inference(backward_demodulation,[],[f2631,f2773])).
% 3.91/0.91  fof(f2631,plain,(
% 3.91/0.91    ( ! [X5] : (k3_xboole_0(k2_xboole_0(k4_xboole_0(X5,sK0),k4_xboole_0(sK0,X5)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X5,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k2_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X5)))) )),
% 3.91/0.91    inference(backward_demodulation,[],[f101,f2612])).
% 3.91/0.91  fof(f2612,plain,(
% 3.91/0.91    ( ! [X4,X3] : (k4_xboole_0(X3,k3_xboole_0(X4,X3)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4))) )),
% 3.91/0.91    inference(forward_demodulation,[],[f2529,f52])).
% 3.91/0.91  fof(f2529,plain,(
% 3.91/0.91    ( ! [X4,X3] : (k4_xboole_0(X3,k3_xboole_0(X4,X3)) = k2_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0)) )),
% 3.91/0.91    inference(superposition,[],[f63,f2484])).
% 3.91/0.91  fof(f101,plain,(
% 3.91/0.91    ( ! [X5] : (k3_xboole_0(k2_xboole_0(k4_xboole_0(X5,sK0),k4_xboole_0(sK0,X5)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X5,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(X5,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) )),
% 3.91/0.91    inference(superposition,[],[f82,f79])).
% 3.91/0.91  fof(f540,plain,(
% 3.91/0.91    ( ! [X0] : (~r1_xboole_0(k2_tarski(X0,sK1),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0))) )),
% 3.91/0.91    inference(unit_resulting_resolution,[],[f113,f66])).
% 3.91/0.91  fof(f66,plain,(
% 3.91/0.91    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) )),
% 3.91/0.91    inference(cnf_transformation,[],[f27])).
% 3.91/0.91  fof(f27,plain,(
% 3.91/0.91    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 3.91/0.91    inference(ennf_transformation,[],[f12])).
% 3.91/0.91  fof(f12,axiom,(
% 3.91/0.91    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 3.91/0.91  fof(f113,plain,(
% 3.91/0.91    ( ! [X0] : (~r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k2_tarski(X0,sK1),sK0))) )),
% 3.91/0.91    inference(unit_resulting_resolution,[],[f93,f81])).
% 3.91/0.91  fof(f81,plain,(
% 3.91/0.91    ( ! [X0,X1] : (~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.91/0.91    inference(definition_unfolding,[],[f61,f49])).
% 3.91/0.91  fof(f61,plain,(
% 3.91/0.91    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 3.91/0.91    inference(cnf_transformation,[],[f26])).
% 3.91/0.91  fof(f26,plain,(
% 3.91/0.91    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.91/0.91    inference(ennf_transformation,[],[f17])).
% 3.91/0.91  fof(f17,axiom,(
% 3.91/0.91    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 3.91/0.91  fof(f93,plain,(
% 3.91/0.91    ( ! [X0] : (r2_hidden(sK1,k4_xboole_0(k2_tarski(X0,sK1),sK0))) )),
% 3.91/0.91    inference(unit_resulting_resolution,[],[f85,f46,f89])).
% 3.91/0.91  fof(f89,plain,(
% 3.91/0.91    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.91/0.91    inference(equality_resolution,[],[f75])).
% 3.91/0.91  fof(f75,plain,(
% 3.91/0.91    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.91/0.91    inference(cnf_transformation,[],[f44])).
% 3.91/0.91  fof(f46,plain,(
% 3.91/0.91    ~r2_hidden(sK1,sK0)),
% 3.91/0.91    inference(cnf_transformation,[],[f29])).
% 3.91/0.91  fof(f85,plain,(
% 3.91/0.91    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 3.91/0.91    inference(equality_resolution,[],[f84])).
% 3.91/0.91  fof(f84,plain,(
% 3.91/0.91    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 3.91/0.91    inference(equality_resolution,[],[f69])).
% 3.91/0.91  fof(f69,plain,(
% 3.91/0.91    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.91/0.91    inference(cnf_transformation,[],[f39])).
% 3.91/0.91  fof(f39,plain,(
% 3.91/0.91    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.91/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 3.91/0.91  fof(f38,plain,(
% 3.91/0.91    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.91/0.91    introduced(choice_axiom,[])).
% 3.91/0.91  fof(f37,plain,(
% 3.91/0.91    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.91/0.91    inference(rectify,[],[f36])).
% 3.91/0.91  fof(f36,plain,(
% 3.91/0.91    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.91/0.91    inference(flattening,[],[f35])).
% 3.91/0.91  fof(f35,plain,(
% 3.91/0.91    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.91/0.91    inference(nnf_transformation,[],[f15])).
% 3.91/0.91  fof(f15,axiom,(
% 3.91/0.91    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.91/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 3.91/0.91  % SZS output end Proof for theBenchmark
% 3.91/0.91  % (27976)------------------------------
% 3.91/0.91  % (27976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.91  % (27976)Termination reason: Refutation
% 3.91/0.91  
% 3.91/0.91  % (27976)Memory used [KB]: 9722
% 3.91/0.91  % (27976)Time elapsed: 0.496 s
% 3.91/0.91  % (27976)------------------------------
% 3.91/0.91  % (27976)------------------------------
% 3.91/0.92  % (27958)Success in time 0.554 s
%------------------------------------------------------------------------------
