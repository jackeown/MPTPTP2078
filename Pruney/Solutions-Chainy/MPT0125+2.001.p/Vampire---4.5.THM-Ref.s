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
% DateTime   : Thu Dec  3 12:33:02 EST 2020

% Result     : Theorem 2.36s
% Output     : Refutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 405 expanded)
%              Number of leaves         :   10 (  96 expanded)
%              Depth                    :   22
%              Number of atoms          :  319 (2536 expanded)
%              Number of equality atoms :  126 (1152 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1316,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1312,f50])).

fof(f50,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1312,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f1300,f1190])).

fof(f1190,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_tarski(sK0))
      | ~ r2_hidden(sK0,X0) ) ),
    inference(forward_demodulation,[],[f1189,f951])).

fof(f951,plain,(
    sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f950,f53])).

fof(f53,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
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

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f950,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f939,f50])).

fof(f939,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f918])).

fof(f918,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f66,f870])).

fof(f870,plain,
    ( sK1 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))
    | sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f869,f51])).

fof(f51,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f869,plain,
    ( r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK1))
    | sK1 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))
    | sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f848,f51])).

fof(f848,plain,
    ( r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK0))
    | r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK1))
    | sK1 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))
    | sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f326,f56])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f326,plain,
    ( r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK0))
    | r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( k2_tarski(sK0,sK1) != X0
      | r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X0),k1_tarski(sK1))
      | r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X0),k1_tarski(sK0))
      | r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X0),X0) ) ),
    inference(superposition,[],[f29,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f29,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f66,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X2),k1_tarski(sK1))
      | k2_tarski(sK0,sK1) != X2
      | ~ r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X2),X2) ) ),
    inference(superposition,[],[f29,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1189,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),X0)
      | ~ r1_tarski(X0,k1_tarski(sK0)) ) ),
    inference(subsumption_resolution,[],[f952,f55])).

fof(f55,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f952,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
      | ~ r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),X0)
      | ~ r1_tarski(X0,k1_tarski(sK0)) ) ),
    inference(backward_demodulation,[],[f108,f951])).

fof(f108,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
      | ~ r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),X0)
      | ~ r1_tarski(X0,k1_tarski(sK0)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X5] :
      ( k2_tarski(sK0,sK1) != X5
      | ~ r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X5),X5)
      | ~ r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X5),X6)
      | ~ r1_tarski(X6,k1_tarski(sK0)) ) ),
    inference(resolution,[],[f65,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f65,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X1),k1_tarski(sK0))
      | k2_tarski(sK0,sK1) != X1
      | ~ r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X1),X1) ) ),
    inference(superposition,[],[f29,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1300,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(resolution,[],[f1296,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1296,plain,(
    r2_hidden(sK2(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(resolution,[],[f1283,f50])).

fof(f1283,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r2_hidden(sK2(X0,k1_tarski(sK0)),X0) ) ),
    inference(resolution,[],[f1190,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (21285)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (21299)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (21303)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (21295)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (21282)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (21281)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (21286)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (21282)Refutation not found, incomplete strategy% (21282)------------------------------
% 0.22/0.52  % (21282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21282)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21282)Memory used [KB]: 10618
% 0.22/0.52  % (21282)Time elapsed: 0.104 s
% 0.22/0.52  % (21282)------------------------------
% 0.22/0.52  % (21282)------------------------------
% 0.22/0.52  % (21293)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.52  % (21283)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.53  % (21287)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.53  % (21280)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.53  % (21297)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.53  % (21291)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.25/0.53  % (21289)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.25/0.53  % (21292)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.53  % (21302)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.53  % (21294)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.53  % (21290)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.25/0.54  % (21301)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.25/0.54  % (21307)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.54  % (21301)Refutation not found, incomplete strategy% (21301)------------------------------
% 1.25/0.54  % (21301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (21301)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (21301)Memory used [KB]: 1663
% 1.25/0.54  % (21301)Time elapsed: 0.120 s
% 1.25/0.54  % (21301)------------------------------
% 1.25/0.54  % (21301)------------------------------
% 1.25/0.54  % (21284)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.54  % (21296)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.25/0.54  % (21298)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.54  % (21306)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.54  % (21305)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.25/0.54  % (21302)Refutation not found, incomplete strategy% (21302)------------------------------
% 1.25/0.54  % (21302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (21302)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (21302)Memory used [KB]: 10618
% 1.25/0.54  % (21302)Time elapsed: 0.125 s
% 1.25/0.54  % (21302)------------------------------
% 1.25/0.54  % (21302)------------------------------
% 1.25/0.54  % (21308)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.54  % (21300)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (21309)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.55  % (21288)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.55  % (21288)Refutation not found, incomplete strategy% (21288)------------------------------
% 1.41/0.55  % (21288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (21288)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (21288)Memory used [KB]: 10618
% 1.41/0.55  % (21288)Time elapsed: 0.140 s
% 1.41/0.55  % (21288)------------------------------
% 1.41/0.55  % (21288)------------------------------
% 1.41/0.55  % (21300)Refutation not found, incomplete strategy% (21300)------------------------------
% 1.41/0.55  % (21300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (21300)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (21300)Memory used [KB]: 10618
% 1.41/0.55  % (21300)Time elapsed: 0.141 s
% 1.41/0.55  % (21300)------------------------------
% 1.41/0.55  % (21300)------------------------------
% 1.41/0.55  % (21297)Refutation not found, incomplete strategy% (21297)------------------------------
% 1.41/0.55  % (21297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (21297)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (21297)Memory used [KB]: 10618
% 1.41/0.55  % (21297)Time elapsed: 0.138 s
% 1.41/0.55  % (21297)------------------------------
% 1.41/0.55  % (21297)------------------------------
% 1.41/0.55  % (21304)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.00/0.65  % (21310)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.00/0.68  % (21311)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.00/0.68  % (21313)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.00/0.68  % (21314)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.36/0.69  % (21315)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.36/0.69  % (21312)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.36/0.72  % (21303)Refutation found. Thanks to Tanya!
% 2.36/0.72  % SZS status Theorem for theBenchmark
% 2.36/0.72  % SZS output start Proof for theBenchmark
% 2.36/0.72  fof(f1316,plain,(
% 2.36/0.72    $false),
% 2.36/0.72    inference(subsumption_resolution,[],[f1312,f50])).
% 2.36/0.72  fof(f50,plain,(
% 2.36/0.72    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.36/0.72    inference(equality_resolution,[],[f49])).
% 2.36/0.72  fof(f49,plain,(
% 2.36/0.72    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.36/0.72    inference(equality_resolution,[],[f34])).
% 2.36/0.72  fof(f34,plain,(
% 2.36/0.72    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.36/0.72    inference(cnf_transformation,[],[f18])).
% 2.36/0.72  fof(f18,plain,(
% 2.36/0.72    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.36/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 2.36/0.72  fof(f17,plain,(
% 2.36/0.72    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 2.36/0.72    introduced(choice_axiom,[])).
% 2.36/0.72  fof(f16,plain,(
% 2.36/0.72    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.36/0.72    inference(rectify,[],[f15])).
% 2.36/0.72  fof(f15,plain,(
% 2.36/0.72    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.36/0.72    inference(nnf_transformation,[],[f3])).
% 2.36/0.72  fof(f3,axiom,(
% 2.36/0.72    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.36/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.36/0.72  fof(f1312,plain,(
% 2.36/0.72    ~r2_hidden(sK0,k1_tarski(sK0))),
% 2.36/0.72    inference(resolution,[],[f1300,f1190])).
% 2.36/0.72  fof(f1190,plain,(
% 2.36/0.72    ( ! [X0] : (~r1_tarski(X0,k1_tarski(sK0)) | ~r2_hidden(sK0,X0)) )),
% 2.36/0.72    inference(forward_demodulation,[],[f1189,f951])).
% 2.36/0.72  fof(f951,plain,(
% 2.36/0.72    sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))),
% 2.36/0.72    inference(subsumption_resolution,[],[f950,f53])).
% 2.36/0.72  fof(f53,plain,(
% 2.36/0.72    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 2.36/0.72    inference(equality_resolution,[],[f52])).
% 2.36/0.72  fof(f52,plain,(
% 2.36/0.72    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 2.36/0.72    inference(equality_resolution,[],[f39])).
% 2.36/0.72  fof(f39,plain,(
% 2.36/0.72    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.36/0.72    inference(cnf_transformation,[],[f23])).
% 2.36/0.72  fof(f23,plain,(
% 2.36/0.72    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.36/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 2.36/0.72  fof(f22,plain,(
% 2.36/0.72    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.36/0.72    introduced(choice_axiom,[])).
% 2.36/0.72  fof(f21,plain,(
% 2.36/0.72    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.36/0.72    inference(rectify,[],[f20])).
% 2.36/0.72  fof(f20,plain,(
% 2.36/0.72    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.36/0.72    inference(flattening,[],[f19])).
% 2.36/0.72  fof(f19,plain,(
% 2.36/0.72    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.36/0.72    inference(nnf_transformation,[],[f4])).
% 2.36/0.72  fof(f4,axiom,(
% 2.36/0.72    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.36/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.36/0.72  fof(f950,plain,(
% 2.36/0.72    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))),
% 2.36/0.72    inference(subsumption_resolution,[],[f939,f50])).
% 2.36/0.72  fof(f939,plain,(
% 2.36/0.72    ~r2_hidden(sK1,k1_tarski(sK1)) | ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))),
% 2.36/0.72    inference(trivial_inequality_removal,[],[f918])).
% 2.36/0.72  fof(f918,plain,(
% 2.36/0.72    ~r2_hidden(sK1,k1_tarski(sK1)) | k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))),
% 2.36/0.72    inference(superposition,[],[f66,f870])).
% 2.36/0.72  fof(f870,plain,(
% 2.36/0.72    sK1 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)) | sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))),
% 2.36/0.72    inference(subsumption_resolution,[],[f869,f51])).
% 2.36/0.72  fof(f51,plain,(
% 2.36/0.72    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.36/0.72    inference(equality_resolution,[],[f33])).
% 2.36/0.72  fof(f33,plain,(
% 2.36/0.72    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.36/0.72    inference(cnf_transformation,[],[f18])).
% 2.36/0.72  fof(f869,plain,(
% 2.36/0.72    r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK1)) | sK1 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)) | sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))),
% 2.36/0.72    inference(subsumption_resolution,[],[f848,f51])).
% 2.36/0.72  fof(f848,plain,(
% 2.36/0.72    r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK0)) | r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK1)) | sK1 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)) | sK0 = sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1))),
% 2.36/0.72    inference(resolution,[],[f326,f56])).
% 2.36/0.72  fof(f56,plain,(
% 2.36/0.72    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 2.36/0.72    inference(equality_resolution,[],[f37])).
% 2.36/0.72  fof(f37,plain,(
% 2.36/0.72    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.36/0.72    inference(cnf_transformation,[],[f23])).
% 2.36/0.72  fof(f326,plain,(
% 2.36/0.72    r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK0)) | r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k1_tarski(sK1))),
% 2.36/0.72    inference(equality_resolution,[],[f64])).
% 2.36/0.72  fof(f64,plain,(
% 2.36/0.72    ( ! [X0] : (k2_tarski(sK0,sK1) != X0 | r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X0),k1_tarski(sK1)) | r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X0),k1_tarski(sK0)) | r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X0),X0)) )),
% 2.36/0.72    inference(superposition,[],[f29,f46])).
% 2.36/0.72  fof(f46,plain,(
% 2.36/0.72    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.36/0.72    inference(cnf_transformation,[],[f28])).
% 2.36/0.72  fof(f28,plain,(
% 2.36/0.72    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.36/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 2.36/0.72  fof(f27,plain,(
% 2.36/0.72    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.36/0.72    introduced(choice_axiom,[])).
% 2.36/0.72  fof(f26,plain,(
% 2.36/0.72    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.36/0.72    inference(rectify,[],[f25])).
% 2.36/0.72  fof(f25,plain,(
% 2.36/0.72    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.36/0.72    inference(flattening,[],[f24])).
% 2.36/0.72  fof(f24,plain,(
% 2.36/0.72    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.36/0.72    inference(nnf_transformation,[],[f2])).
% 2.36/0.72  fof(f2,axiom,(
% 2.36/0.72    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.36/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.36/0.72  fof(f29,plain,(
% 2.36/0.72    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.36/0.72    inference(cnf_transformation,[],[f10])).
% 2.36/0.72  fof(f10,plain,(
% 2.36/0.72    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.36/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).
% 2.36/0.72  fof(f9,plain,(
% 2.36/0.72    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.36/0.72    introduced(choice_axiom,[])).
% 2.36/0.72  fof(f7,plain,(
% 2.36/0.72    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 2.36/0.72    inference(ennf_transformation,[],[f6])).
% 2.36/0.72  fof(f6,negated_conjecture,(
% 2.36/0.72    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 2.36/0.72    inference(negated_conjecture,[],[f5])).
% 2.36/0.72  fof(f5,conjecture,(
% 2.36/0.72    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 2.36/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 2.36/0.72  fof(f66,plain,(
% 2.36/0.72    ( ! [X2] : (~r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X2),k1_tarski(sK1)) | k2_tarski(sK0,sK1) != X2 | ~r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X2),X2)) )),
% 2.36/0.72    inference(superposition,[],[f29,f48])).
% 2.36/0.72  fof(f48,plain,(
% 2.36/0.72    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.36/0.72    inference(cnf_transformation,[],[f28])).
% 2.36/0.72  fof(f1189,plain,(
% 2.36/0.72    ( ! [X0] : (~r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),X0) | ~r1_tarski(X0,k1_tarski(sK0))) )),
% 2.36/0.72    inference(subsumption_resolution,[],[f952,f55])).
% 2.36/0.72  fof(f55,plain,(
% 2.36/0.72    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 2.36/0.72    inference(equality_resolution,[],[f54])).
% 2.36/0.72  fof(f54,plain,(
% 2.36/0.72    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 2.36/0.72    inference(equality_resolution,[],[f38])).
% 2.36/0.72  fof(f38,plain,(
% 2.36/0.72    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.36/0.72    inference(cnf_transformation,[],[f23])).
% 2.36/0.72  fof(f952,plain,(
% 2.36/0.72    ( ! [X0] : (~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),X0) | ~r1_tarski(X0,k1_tarski(sK0))) )),
% 2.36/0.72    inference(backward_demodulation,[],[f108,f951])).
% 2.36/0.72  fof(f108,plain,(
% 2.36/0.72    ( ! [X0] : (~r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | ~r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK0,sK1)),X0) | ~r1_tarski(X0,k1_tarski(sK0))) )),
% 2.36/0.72    inference(equality_resolution,[],[f91])).
% 2.36/0.72  fof(f91,plain,(
% 2.36/0.72    ( ! [X6,X5] : (k2_tarski(sK0,sK1) != X5 | ~r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X5),X5) | ~r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X5),X6) | ~r1_tarski(X6,k1_tarski(sK0))) )),
% 2.36/0.72    inference(resolution,[],[f65,f30])).
% 2.36/0.72  fof(f30,plain,(
% 2.36/0.72    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.36/0.72    inference(cnf_transformation,[],[f14])).
% 2.36/0.72  fof(f14,plain,(
% 2.36/0.72    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.36/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).
% 2.36/0.72  fof(f13,plain,(
% 2.36/0.72    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.36/0.72    introduced(choice_axiom,[])).
% 2.36/0.72  fof(f12,plain,(
% 2.36/0.72    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.36/0.72    inference(rectify,[],[f11])).
% 2.36/0.72  fof(f11,plain,(
% 2.36/0.72    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.36/0.72    inference(nnf_transformation,[],[f8])).
% 2.36/0.72  fof(f8,plain,(
% 2.36/0.72    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.36/0.72    inference(ennf_transformation,[],[f1])).
% 2.36/0.72  fof(f1,axiom,(
% 2.36/0.72    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.36/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.36/0.72  fof(f65,plain,(
% 2.36/0.72    ( ! [X1] : (~r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X1),k1_tarski(sK0)) | k2_tarski(sK0,sK1) != X1 | ~r2_hidden(sK5(k1_tarski(sK0),k1_tarski(sK1),X1),X1)) )),
% 2.36/0.72    inference(superposition,[],[f29,f47])).
% 2.36/0.72  fof(f47,plain,(
% 2.36/0.72    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.36/0.72    inference(cnf_transformation,[],[f28])).
% 2.36/0.72  fof(f1300,plain,(
% 2.36/0.72    r1_tarski(k1_tarski(sK0),k1_tarski(sK0))),
% 2.36/0.72    inference(resolution,[],[f1296,f32])).
% 2.36/0.72  fof(f32,plain,(
% 2.36/0.72    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 2.36/0.72    inference(cnf_transformation,[],[f14])).
% 2.36/0.72  fof(f1296,plain,(
% 2.36/0.72    r2_hidden(sK2(k1_tarski(sK0),k1_tarski(sK0)),k1_tarski(sK0))),
% 2.36/0.72    inference(resolution,[],[f1283,f50])).
% 2.36/0.72  fof(f1283,plain,(
% 2.36/0.72    ( ! [X0] : (~r2_hidden(sK0,X0) | r2_hidden(sK2(X0,k1_tarski(sK0)),X0)) )),
% 2.36/0.72    inference(resolution,[],[f1190,f31])).
% 2.36/0.72  fof(f31,plain,(
% 2.36/0.72    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 2.36/0.72    inference(cnf_transformation,[],[f14])).
% 2.36/0.72  % SZS output end Proof for theBenchmark
% 2.36/0.72  % (21303)------------------------------
% 2.36/0.72  % (21303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.72  % (21303)Termination reason: Refutation
% 2.36/0.72  
% 2.36/0.72  % (21303)Memory used [KB]: 2942
% 2.36/0.72  % (21303)Time elapsed: 0.271 s
% 2.36/0.72  % (21303)------------------------------
% 2.36/0.72  % (21303)------------------------------
% 2.36/0.73  % (21279)Success in time 0.359 s
%------------------------------------------------------------------------------
