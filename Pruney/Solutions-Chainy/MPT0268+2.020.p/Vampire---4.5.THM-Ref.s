%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:39 EST 2020

% Result     : Theorem 2.50s
% Output     : Refutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  121 (4171 expanded)
%              Number of leaves         :   18 (1217 expanded)
%              Depth                    :   42
%              Number of atoms          :  365 (10770 expanded)
%              Number of equality atoms :  156 (2999 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3733,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3732,f373])).

fof(f373,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f48,f333])).

fof(f333,plain,(
    ! [X10] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10) ),
    inference(resolution,[],[f301,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f301,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(backward_demodulation,[],[f288,f291])).

fof(f291,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f277,f46])).

fof(f277,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f269,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f269,plain,(
    r1_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f48,f261])).

fof(f261,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f254,f172])).

fof(f172,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f150,f46])).

fof(f150,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK0,k1_tarski(sK1)))
      | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(resolution,[],[f138,f54])).

fof(f138,plain,
    ( r1_xboole_0(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f48,f115])).

fof(f115,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f91,f46])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK0,k1_tarski(sK1)))
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(forward_demodulation,[],[f90,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f90,plain,(
    ! [X0] :
      ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
      | ~ r2_hidden(X0,k3_xboole_0(k1_tarski(sK1),sK0)) ) ),
    inference(resolution,[],[f86,f54])).

fof(f86,plain,
    ( r1_xboole_0(k1_tarski(sK1),sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f43,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f43,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f254,plain,(
    k3_xboole_0(sK0,k1_tarski(sK1)) = k4_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f52,f198])).

fof(f198,plain,(
    k4_xboole_0(sK0,k1_tarski(sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f51,f172])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f288,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)),X1)) ),
    inference(resolution,[],[f277,f76])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f48,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f3732,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f3730,f1777])).

fof(f1777,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(superposition,[],[f1592,f47])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1592,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_tarski(sK1),X0) ),
    inference(resolution,[],[f1577,f851])).

fof(f851,plain,(
    ! [X12,X11] :
      ( ~ r1_xboole_0(X11,X12)
      | k1_xboole_0 = k3_xboole_0(X11,X12) ) ),
    inference(resolution,[],[f348,f54])).

fof(f348,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK4(k1_xboole_0,X11,X12),X12)
      | k1_xboole_0 = X12 ) ),
    inference(backward_demodulation,[],[f311,f333])).

fof(f311,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK4(k1_xboole_0,X11,X12),X12)
      | k4_xboole_0(k1_xboole_0,X11) = X12 ) ),
    inference(forward_demodulation,[],[f310,f291])).

fof(f310,plain,(
    ! [X12,X11] :
      ( k4_xboole_0(k1_xboole_0,X11) = X12
      | r2_hidden(sK4(k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)),X11,X12),X12) ) ),
    inference(forward_demodulation,[],[f296,f291])).

fof(f296,plain,(
    ! [X12,X11] :
      ( k4_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)),X11) = X12
      | r2_hidden(sK4(k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)),X11,X12),X12) ) ),
    inference(resolution,[],[f277,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1577,plain,(
    ! [X1] : r1_xboole_0(k1_tarski(sK1),X1) ),
    inference(resolution,[],[f1490,f791])).

fof(f791,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,sK0)
      | r1_xboole_0(k1_tarski(sK1),X1) ) ),
    inference(resolution,[],[f769,f662])).

fof(f662,plain,(
    ! [X10,X9] :
      ( r1_xboole_0(k1_tarski(X9),X10)
      | r2_hidden(X9,k1_tarski(X9)) ) ),
    inference(resolution,[],[f650,f55])).

fof(f650,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f512,f47])).

fof(f512,plain,(
    ! [X10,X8,X9] :
      ( r1_xboole_0(k3_xboole_0(X8,X9),X10)
      | ~ r1_xboole_0(X8,X9) ) ),
    inference(resolution,[],[f387,f54])).

fof(f387,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(superposition,[],[f373,f46])).

fof(f769,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f446,f300])).

fof(f300,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k4_xboole_0(X3,k1_xboole_0))
      | ~ r2_hidden(X2,X3) ) ),
    inference(backward_demodulation,[],[f289,f291])).

fof(f289,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k4_xboole_0(X3,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0))))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f277,f74])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f446,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k4_xboole_0(sK0,k1_xboole_0))
      | ~ r2_hidden(X4,k1_tarski(sK1)) ) ),
    inference(backward_demodulation,[],[f259,f403])).

fof(f403,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f51,f390])).

fof(f390,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f369,f49])).

fof(f369,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f333,f52])).

fof(f259,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_xboole_0(sK0,k1_xboole_0))
      | ~ r2_hidden(X4,k1_tarski(sK1)) ) ),
    inference(superposition,[],[f75,f198])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1490,plain,(
    r2_hidden(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f1445])).

fof(f1445,plain,
    ( sK0 != sK0
    | r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f409,f1420])).

fof(f1420,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f1393,f47])).

fof(f1393,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f929,f52])).

fof(f929,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(X4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f922,f403])).

fof(f922,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f51,f904])).

fof(f904,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f862,f49])).

fof(f862,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(resolution,[],[f851,f48])).

fof(f409,plain,
    ( sK0 != k4_xboole_0(sK0,k1_xboole_0)
    | r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f200,f403])).

fof(f200,plain,
    ( sK0 != k5_xboole_0(sK0,k1_xboole_0)
    | r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f44,f198])).

fof(f44,plain,
    ( sK0 != k4_xboole_0(sK0,k1_tarski(sK1))
    | r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f3730,plain,(
    ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(superposition,[],[f3717,f45])).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f3717,plain,(
    ! [X0] : ~ r1_xboole_0(k2_tarski(X0,sK1),k2_tarski(X0,sK1)) ),
    inference(superposition,[],[f3570,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f3570,plain,(
    ! [X14,X13] : ~ r1_xboole_0(k1_enumset1(X13,X14,sK1),k1_enumset1(X13,X14,sK1)) ),
    inference(resolution,[],[f3548,f78])).

fof(f78,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK5(X0,X1,X2,X3) != X2
              & sK5(X0,X1,X2,X3) != X1
              & sK5(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sK5(X0,X1,X2,X3) = X2
            | sK5(X0,X1,X2,X3) = X1
            | sK5(X0,X1,X2,X3) = X0
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK5(X0,X1,X2,X3) != X2
            & sK5(X0,X1,X2,X3) != X1
            & sK5(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sK5(X0,X1,X2,X3) = X2
          | sK5(X0,X1,X2,X3) = X1
          | sK5(X0,X1,X2,X3) = X0
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f3548,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f3498,f47])).

fof(f3498,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(sK1,k3_xboole_0(X17,X18))
      | ~ r1_xboole_0(X18,X17) ) ),
    inference(resolution,[],[f3474,f651])).

fof(f651,plain,(
    ! [X4,X2,X3] :
      ( r1_xboole_0(k3_xboole_0(X3,X2),X4)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f512,f49])).

fof(f3474,plain,(
    ! [X9] :
      ( ~ r1_xboole_0(X9,sK0)
      | ~ r2_hidden(sK1,X9) ) ),
    inference(resolution,[],[f3456,f54])).

fof(f3456,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k3_xboole_0(X0,sK0))
      | ~ r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f1613,f52])).

fof(f1613,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK1,k4_xboole_0(X4,k4_xboole_0(X5,sK0)))
      | ~ r2_hidden(sK1,X4) ) ),
    inference(resolution,[],[f1581,f74])).

fof(f1581,plain,(
    ! [X4] : ~ r2_hidden(sK1,k4_xboole_0(X4,sK0)) ),
    inference(resolution,[],[f1490,f75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:37:37 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.23/0.51  % (4475)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.52  % (4467)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.52  % (4459)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.52  % (4478)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.53  % (4462)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.53  % (4458)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.53  % (4465)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.53  % (4457)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.53  % (4474)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.54  % (4454)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.54  % (4471)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.54  % (4453)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.54  % (4466)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.54  % (4456)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.55  % (4473)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.55  % (4481)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.55  % (4479)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.55  % (4460)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.55  % (4452)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.55  % (4472)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.55  % (4470)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.55  % (4455)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.55  % (4461)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.56  % (4476)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.56  % (4480)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.56  % (4454)Refutation not found, incomplete strategy% (4454)------------------------------
% 0.23/0.56  % (4454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (4454)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (4454)Memory used [KB]: 10746
% 0.23/0.56  % (4454)Time elapsed: 0.126 s
% 0.23/0.56  % (4454)------------------------------
% 0.23/0.56  % (4454)------------------------------
% 0.23/0.56  % (4477)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.56  % (4463)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.56  % (4464)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.56  % (4468)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.57  % (4460)Refutation not found, incomplete strategy% (4460)------------------------------
% 0.23/0.57  % (4460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (4469)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.57  % (4460)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (4460)Memory used [KB]: 10618
% 0.23/0.57  % (4460)Time elapsed: 0.142 s
% 0.23/0.57  % (4460)------------------------------
% 0.23/0.57  % (4460)------------------------------
% 1.94/0.69  % (4525)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.50/0.73  % (4531)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.50/0.75  % (4475)Refutation found. Thanks to Tanya!
% 2.50/0.75  % SZS status Theorem for theBenchmark
% 2.50/0.75  % SZS output start Proof for theBenchmark
% 2.50/0.75  fof(f3733,plain,(
% 2.50/0.75    $false),
% 2.50/0.75    inference(subsumption_resolution,[],[f3732,f373])).
% 2.50/0.75  fof(f373,plain,(
% 2.50/0.75    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.50/0.75    inference(superposition,[],[f48,f333])).
% 2.50/0.76  fof(f333,plain,(
% 2.50/0.76    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10)) )),
% 2.50/0.76    inference(resolution,[],[f301,f46])).
% 2.50/0.76  fof(f46,plain,(
% 2.50/0.76    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.50/0.76    inference(cnf_transformation,[],[f30])).
% 2.50/0.76  fof(f30,plain,(
% 2.50/0.76    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.50/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f29])).
% 2.50/0.76  fof(f29,plain,(
% 2.50/0.76    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.50/0.76    introduced(choice_axiom,[])).
% 2.50/0.76  fof(f22,plain,(
% 2.50/0.76    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.50/0.76    inference(ennf_transformation,[],[f5])).
% 2.50/0.76  fof(f5,axiom,(
% 2.50/0.76    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.50/0.76  fof(f301,plain,(
% 2.50/0.76    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,X1))) )),
% 2.50/0.76    inference(backward_demodulation,[],[f288,f291])).
% 2.50/0.76  fof(f291,plain,(
% 2.50/0.76    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0))),
% 2.50/0.76    inference(resolution,[],[f277,f46])).
% 2.50/0.76  fof(f277,plain,(
% 2.50/0.76    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)))) )),
% 2.50/0.76    inference(resolution,[],[f269,f54])).
% 2.50/0.76  fof(f54,plain,(
% 2.50/0.76    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.50/0.76    inference(cnf_transformation,[],[f32])).
% 2.50/0.76  fof(f32,plain,(
% 2.50/0.76    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.50/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f31])).
% 2.50/0.76  fof(f31,plain,(
% 2.50/0.76    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.50/0.76    introduced(choice_axiom,[])).
% 2.50/0.76  fof(f23,plain,(
% 2.50/0.76    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.50/0.76    inference(ennf_transformation,[],[f20])).
% 2.50/0.76  fof(f20,plain,(
% 2.50/0.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.50/0.76    inference(rectify,[],[f4])).
% 2.50/0.76  fof(f4,axiom,(
% 2.50/0.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.50/0.76  fof(f269,plain,(
% 2.50/0.76    r1_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0))),
% 2.50/0.76    inference(superposition,[],[f48,f261])).
% 2.50/0.76  fof(f261,plain,(
% 2.50/0.76    k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0))),
% 2.50/0.76    inference(forward_demodulation,[],[f254,f172])).
% 2.50/0.76  fof(f172,plain,(
% 2.50/0.76    k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 2.50/0.76    inference(duplicate_literal_removal,[],[f165])).
% 2.50/0.76  fof(f165,plain,(
% 2.50/0.76    k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 2.50/0.76    inference(resolution,[],[f150,f46])).
% 2.50/0.76  fof(f150,plain,(
% 2.50/0.76    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,k1_tarski(sK1))) | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))) )),
% 2.50/0.76    inference(resolution,[],[f138,f54])).
% 2.50/0.76  fof(f138,plain,(
% 2.50/0.76    r1_xboole_0(sK0,k1_tarski(sK1)) | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 2.50/0.76    inference(superposition,[],[f48,f115])).
% 2.50/0.76  fof(f115,plain,(
% 2.50/0.76    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 2.50/0.76    inference(resolution,[],[f91,f46])).
% 2.50/0.76  fof(f91,plain,(
% 2.50/0.76    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,k1_tarski(sK1))) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))) )),
% 2.50/0.76    inference(forward_demodulation,[],[f90,f49])).
% 2.50/0.76  fof(f49,plain,(
% 2.50/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.50/0.76    inference(cnf_transformation,[],[f1])).
% 2.50/0.76  fof(f1,axiom,(
% 2.50/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.50/0.76  fof(f90,plain,(
% 2.50/0.76    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~r2_hidden(X0,k3_xboole_0(k1_tarski(sK1),sK0))) )),
% 2.50/0.76    inference(resolution,[],[f86,f54])).
% 2.50/0.76  fof(f86,plain,(
% 2.50/0.76    r1_xboole_0(k1_tarski(sK1),sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.50/0.76    inference(resolution,[],[f43,f55])).
% 2.50/0.76  fof(f55,plain,(
% 2.50/0.76    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.50/0.76    inference(cnf_transformation,[],[f24])).
% 2.50/0.76  fof(f24,plain,(
% 2.50/0.76    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.50/0.76    inference(ennf_transformation,[],[f16])).
% 2.50/0.76  fof(f16,axiom,(
% 2.50/0.76    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.50/0.76  fof(f43,plain,(
% 2.50/0.76    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.50/0.76    inference(cnf_transformation,[],[f28])).
% 2.50/0.76  fof(f28,plain,(
% 2.50/0.76    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 2.50/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 2.50/0.76  fof(f27,plain,(
% 2.50/0.76    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 2.50/0.76    introduced(choice_axiom,[])).
% 2.50/0.76  fof(f26,plain,(
% 2.50/0.76    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 2.50/0.76    inference(nnf_transformation,[],[f21])).
% 2.50/0.76  fof(f21,plain,(
% 2.50/0.76    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 2.50/0.76    inference(ennf_transformation,[],[f18])).
% 2.50/0.76  fof(f18,negated_conjecture,(
% 2.50/0.76    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.50/0.76    inference(negated_conjecture,[],[f17])).
% 2.50/0.76  fof(f17,conjecture,(
% 2.50/0.76    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 2.50/0.76  fof(f254,plain,(
% 2.50/0.76    k3_xboole_0(sK0,k1_tarski(sK1)) = k4_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0))),
% 2.50/0.76    inference(superposition,[],[f52,f198])).
% 2.50/0.76  fof(f198,plain,(
% 2.50/0.76    k4_xboole_0(sK0,k1_tarski(sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 2.50/0.76    inference(superposition,[],[f51,f172])).
% 2.50/0.76  fof(f51,plain,(
% 2.50/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.50/0.76    inference(cnf_transformation,[],[f6])).
% 2.50/0.76  fof(f6,axiom,(
% 2.50/0.76    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.50/0.76  fof(f52,plain,(
% 2.50/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.50/0.76    inference(cnf_transformation,[],[f7])).
% 2.50/0.76  fof(f7,axiom,(
% 2.50/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.50/0.76  fof(f288,plain,(
% 2.50/0.76    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)),X1))) )),
% 2.50/0.76    inference(resolution,[],[f277,f76])).
% 2.50/0.76  fof(f76,plain,(
% 2.50/0.76    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.50/0.76    inference(equality_resolution,[],[f57])).
% 2.50/0.76  fof(f57,plain,(
% 2.50/0.76    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.50/0.76    inference(cnf_transformation,[],[f37])).
% 2.50/0.76  fof(f37,plain,(
% 2.50/0.76    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.50/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 2.50/0.76  fof(f36,plain,(
% 2.50/0.76    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.50/0.76    introduced(choice_axiom,[])).
% 2.50/0.76  fof(f35,plain,(
% 2.50/0.76    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.50/0.76    inference(rectify,[],[f34])).
% 2.50/0.76  fof(f34,plain,(
% 2.50/0.76    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.50/0.76    inference(flattening,[],[f33])).
% 2.50/0.76  fof(f33,plain,(
% 2.50/0.76    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.50/0.76    inference(nnf_transformation,[],[f2])).
% 2.50/0.76  fof(f2,axiom,(
% 2.50/0.76    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.50/0.76  fof(f48,plain,(
% 2.50/0.76    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.50/0.76    inference(cnf_transformation,[],[f8])).
% 2.50/0.76  fof(f8,axiom,(
% 2.50/0.76    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.50/0.76  fof(f3732,plain,(
% 2.50/0.76    ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.50/0.76    inference(forward_demodulation,[],[f3730,f1777])).
% 2.50/0.76  fof(f1777,plain,(
% 2.50/0.76    k1_xboole_0 = k1_tarski(sK1)),
% 2.50/0.76    inference(superposition,[],[f1592,f47])).
% 2.50/0.76  fof(f47,plain,(
% 2.50/0.76    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.50/0.76    inference(cnf_transformation,[],[f19])).
% 2.50/0.76  fof(f19,plain,(
% 2.50/0.76    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.50/0.76    inference(rectify,[],[f3])).
% 2.50/0.76  fof(f3,axiom,(
% 2.50/0.76    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.50/0.76  fof(f1592,plain,(
% 2.50/0.76    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_tarski(sK1),X0)) )),
% 2.50/0.76    inference(resolution,[],[f1577,f851])).
% 2.50/0.76  fof(f851,plain,(
% 2.50/0.76    ( ! [X12,X11] : (~r1_xboole_0(X11,X12) | k1_xboole_0 = k3_xboole_0(X11,X12)) )),
% 2.50/0.76    inference(resolution,[],[f348,f54])).
% 2.50/0.76  fof(f348,plain,(
% 2.50/0.76    ( ! [X12,X11] : (r2_hidden(sK4(k1_xboole_0,X11,X12),X12) | k1_xboole_0 = X12) )),
% 2.50/0.76    inference(backward_demodulation,[],[f311,f333])).
% 2.50/0.76  fof(f311,plain,(
% 2.50/0.76    ( ! [X12,X11] : (r2_hidden(sK4(k1_xboole_0,X11,X12),X12) | k4_xboole_0(k1_xboole_0,X11) = X12) )),
% 2.50/0.76    inference(forward_demodulation,[],[f310,f291])).
% 2.50/0.76  fof(f310,plain,(
% 2.50/0.76    ( ! [X12,X11] : (k4_xboole_0(k1_xboole_0,X11) = X12 | r2_hidden(sK4(k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)),X11,X12),X12)) )),
% 2.50/0.76    inference(forward_demodulation,[],[f296,f291])).
% 2.50/0.76  fof(f296,plain,(
% 2.50/0.76    ( ! [X12,X11] : (k4_xboole_0(k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)),X11) = X12 | r2_hidden(sK4(k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)),X11,X12),X12)) )),
% 2.50/0.76    inference(resolution,[],[f277,f60])).
% 2.50/0.76  fof(f60,plain,(
% 2.50/0.76    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.50/0.76    inference(cnf_transformation,[],[f37])).
% 2.50/0.76  fof(f1577,plain,(
% 2.50/0.76    ( ! [X1] : (r1_xboole_0(k1_tarski(sK1),X1)) )),
% 2.50/0.76    inference(resolution,[],[f1490,f791])).
% 2.50/0.76  fof(f791,plain,(
% 2.50/0.76    ( ! [X1] : (~r2_hidden(sK1,sK0) | r1_xboole_0(k1_tarski(sK1),X1)) )),
% 2.50/0.76    inference(resolution,[],[f769,f662])).
% 2.50/0.76  fof(f662,plain,(
% 2.50/0.76    ( ! [X10,X9] : (r1_xboole_0(k1_tarski(X9),X10) | r2_hidden(X9,k1_tarski(X9))) )),
% 2.50/0.76    inference(resolution,[],[f650,f55])).
% 2.50/0.76  fof(f650,plain,(
% 2.50/0.76    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 2.50/0.76    inference(superposition,[],[f512,f47])).
% 2.50/0.76  fof(f512,plain,(
% 2.50/0.76    ( ! [X10,X8,X9] : (r1_xboole_0(k3_xboole_0(X8,X9),X10) | ~r1_xboole_0(X8,X9)) )),
% 2.50/0.76    inference(resolution,[],[f387,f54])).
% 2.50/0.76  fof(f387,plain,(
% 2.50/0.76    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0),X0)) )),
% 2.50/0.76    inference(superposition,[],[f373,f46])).
% 2.50/0.76  fof(f769,plain,(
% 2.50/0.76    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK1)) | ~r2_hidden(X0,sK0)) )),
% 2.50/0.76    inference(resolution,[],[f446,f300])).
% 2.50/0.76  fof(f300,plain,(
% 2.50/0.76    ( ! [X2,X3] : (r2_hidden(X2,k4_xboole_0(X3,k1_xboole_0)) | ~r2_hidden(X2,X3)) )),
% 2.50/0.76    inference(backward_demodulation,[],[f289,f291])).
% 2.50/0.76  fof(f289,plain,(
% 2.50/0.76    ( ! [X2,X3] : (r2_hidden(X2,k4_xboole_0(X3,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k1_xboole_0)))) | ~r2_hidden(X2,X3)) )),
% 2.50/0.76    inference(resolution,[],[f277,f74])).
% 2.50/0.76  fof(f74,plain,(
% 2.50/0.76    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.50/0.76    inference(equality_resolution,[],[f59])).
% 2.50/0.76  fof(f59,plain,(
% 2.50/0.76    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.50/0.76    inference(cnf_transformation,[],[f37])).
% 2.50/0.76  fof(f446,plain,(
% 2.50/0.76    ( ! [X4] : (~r2_hidden(X4,k4_xboole_0(sK0,k1_xboole_0)) | ~r2_hidden(X4,k1_tarski(sK1))) )),
% 2.50/0.76    inference(backward_demodulation,[],[f259,f403])).
% 2.50/0.76  fof(f403,plain,(
% 2.50/0.76    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0)) )),
% 2.50/0.76    inference(superposition,[],[f51,f390])).
% 2.50/0.76  fof(f390,plain,(
% 2.50/0.76    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 2.50/0.76    inference(superposition,[],[f369,f49])).
% 2.50/0.76  fof(f369,plain,(
% 2.50/0.76    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 2.50/0.76    inference(superposition,[],[f333,f52])).
% 2.50/0.76  fof(f259,plain,(
% 2.50/0.76    ( ! [X4] : (~r2_hidden(X4,k5_xboole_0(sK0,k1_xboole_0)) | ~r2_hidden(X4,k1_tarski(sK1))) )),
% 2.50/0.76    inference(superposition,[],[f75,f198])).
% 2.50/0.76  fof(f75,plain,(
% 2.50/0.76    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.50/0.76    inference(equality_resolution,[],[f58])).
% 2.50/0.76  fof(f58,plain,(
% 2.50/0.76    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.50/0.76    inference(cnf_transformation,[],[f37])).
% 2.50/0.76  fof(f1490,plain,(
% 2.50/0.76    r2_hidden(sK1,sK0)),
% 2.50/0.76    inference(trivial_inequality_removal,[],[f1445])).
% 2.50/0.76  fof(f1445,plain,(
% 2.50/0.76    sK0 != sK0 | r2_hidden(sK1,sK0)),
% 2.50/0.76    inference(backward_demodulation,[],[f409,f1420])).
% 2.50/0.76  fof(f1420,plain,(
% 2.50/0.76    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.50/0.76    inference(forward_demodulation,[],[f1393,f47])).
% 2.50/0.76  fof(f1393,plain,(
% 2.50/0.76    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 2.50/0.76    inference(superposition,[],[f929,f52])).
% 2.50/0.76  fof(f929,plain,(
% 2.50/0.76    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(X4,k1_xboole_0)) )),
% 2.50/0.76    inference(forward_demodulation,[],[f922,f403])).
% 2.50/0.76  fof(f922,plain,(
% 2.50/0.76    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k1_xboole_0)) )),
% 2.50/0.76    inference(superposition,[],[f51,f904])).
% 2.50/0.76  fof(f904,plain,(
% 2.50/0.76    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 2.50/0.76    inference(superposition,[],[f862,f49])).
% 2.50/0.76  fof(f862,plain,(
% 2.50/0.76    ( ! [X2,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X2),X2)) )),
% 2.50/0.76    inference(resolution,[],[f851,f48])).
% 2.50/0.76  fof(f409,plain,(
% 2.50/0.76    sK0 != k4_xboole_0(sK0,k1_xboole_0) | r2_hidden(sK1,sK0)),
% 2.50/0.76    inference(backward_demodulation,[],[f200,f403])).
% 2.50/0.76  fof(f200,plain,(
% 2.50/0.76    sK0 != k5_xboole_0(sK0,k1_xboole_0) | r2_hidden(sK1,sK0)),
% 2.50/0.76    inference(backward_demodulation,[],[f44,f198])).
% 2.50/0.76  fof(f44,plain,(
% 2.50/0.76    sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) | r2_hidden(sK1,sK0)),
% 2.50/0.76    inference(cnf_transformation,[],[f28])).
% 2.50/0.76  fof(f3730,plain,(
% 2.50/0.76    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 2.50/0.76    inference(superposition,[],[f3717,f45])).
% 2.50/0.76  fof(f45,plain,(
% 2.50/0.76    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.50/0.76    inference(cnf_transformation,[],[f10])).
% 2.50/0.76  fof(f10,axiom,(
% 2.50/0.76    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.50/0.76  fof(f3717,plain,(
% 2.50/0.76    ( ! [X0] : (~r1_xboole_0(k2_tarski(X0,sK1),k2_tarski(X0,sK1))) )),
% 2.50/0.76    inference(superposition,[],[f3570,f50])).
% 2.50/0.76  fof(f50,plain,(
% 2.50/0.76    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.50/0.76    inference(cnf_transformation,[],[f11])).
% 2.50/0.76  fof(f11,axiom,(
% 2.50/0.76    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.50/0.76  fof(f3570,plain,(
% 2.50/0.76    ( ! [X14,X13] : (~r1_xboole_0(k1_enumset1(X13,X14,sK1),k1_enumset1(X13,X14,sK1))) )),
% 2.50/0.76    inference(resolution,[],[f3548,f78])).
% 2.50/0.76  fof(f78,plain,(
% 2.50/0.76    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 2.50/0.76    inference(equality_resolution,[],[f77])).
% 2.50/0.76  fof(f77,plain,(
% 2.50/0.76    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 2.50/0.76    inference(equality_resolution,[],[f67])).
% 2.50/0.76  fof(f67,plain,(
% 2.50/0.76    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.50/0.76    inference(cnf_transformation,[],[f42])).
% 2.50/0.76  fof(f42,plain,(
% 2.50/0.76    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.50/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 2.50/0.76  fof(f41,plain,(
% 2.50/0.76    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK5(X0,X1,X2,X3) != X2 & sK5(X0,X1,X2,X3) != X1 & sK5(X0,X1,X2,X3) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sK5(X0,X1,X2,X3) = X2 | sK5(X0,X1,X2,X3) = X1 | sK5(X0,X1,X2,X3) = X0 | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 2.50/0.76    introduced(choice_axiom,[])).
% 2.50/0.76  fof(f40,plain,(
% 2.50/0.76    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.50/0.76    inference(rectify,[],[f39])).
% 2.50/0.76  fof(f39,plain,(
% 2.50/0.76    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.50/0.76    inference(flattening,[],[f38])).
% 2.50/0.76  fof(f38,plain,(
% 2.50/0.76    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.50/0.76    inference(nnf_transformation,[],[f25])).
% 2.50/0.76  fof(f25,plain,(
% 2.50/0.76    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.50/0.76    inference(ennf_transformation,[],[f9])).
% 2.50/0.76  fof(f9,axiom,(
% 2.50/0.76    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.50/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.50/0.76  fof(f3548,plain,(
% 2.50/0.76    ( ! [X0] : (~r2_hidden(sK1,X0) | ~r1_xboole_0(X0,X0)) )),
% 2.50/0.76    inference(superposition,[],[f3498,f47])).
% 2.50/0.76  fof(f3498,plain,(
% 2.50/0.76    ( ! [X17,X18] : (~r2_hidden(sK1,k3_xboole_0(X17,X18)) | ~r1_xboole_0(X18,X17)) )),
% 2.50/0.76    inference(resolution,[],[f3474,f651])).
% 2.50/0.76  fof(f651,plain,(
% 2.50/0.76    ( ! [X4,X2,X3] : (r1_xboole_0(k3_xboole_0(X3,X2),X4) | ~r1_xboole_0(X2,X3)) )),
% 2.50/0.76    inference(superposition,[],[f512,f49])).
% 2.50/0.76  fof(f3474,plain,(
% 2.50/0.76    ( ! [X9] : (~r1_xboole_0(X9,sK0) | ~r2_hidden(sK1,X9)) )),
% 2.50/0.76    inference(resolution,[],[f3456,f54])).
% 2.50/0.76  fof(f3456,plain,(
% 2.50/0.76    ( ! [X0] : (r2_hidden(sK1,k3_xboole_0(X0,sK0)) | ~r2_hidden(sK1,X0)) )),
% 2.50/0.76    inference(superposition,[],[f1613,f52])).
% 2.50/0.76  fof(f1613,plain,(
% 2.50/0.76    ( ! [X4,X5] : (r2_hidden(sK1,k4_xboole_0(X4,k4_xboole_0(X5,sK0))) | ~r2_hidden(sK1,X4)) )),
% 2.50/0.76    inference(resolution,[],[f1581,f74])).
% 2.50/0.76  fof(f1581,plain,(
% 2.50/0.76    ( ! [X4] : (~r2_hidden(sK1,k4_xboole_0(X4,sK0))) )),
% 2.50/0.76    inference(resolution,[],[f1490,f75])).
% 2.50/0.76  % SZS output end Proof for theBenchmark
% 2.50/0.76  % (4475)------------------------------
% 2.50/0.76  % (4475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.50/0.76  % (4475)Termination reason: Refutation
% 2.50/0.76  
% 2.50/0.76  % (4475)Memory used [KB]: 3198
% 2.50/0.76  % (4475)Time elapsed: 0.293 s
% 2.50/0.76  % (4475)------------------------------
% 2.50/0.76  % (4475)------------------------------
% 2.50/0.76  % (4451)Success in time 0.384 s
%------------------------------------------------------------------------------
