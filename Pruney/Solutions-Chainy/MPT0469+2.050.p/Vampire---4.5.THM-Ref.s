%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 (3344 expanded)
%              Number of leaves         :   12 (1049 expanded)
%              Depth                    :   24
%              Number of atoms          :  257 (20195 expanded)
%              Number of equality atoms :   41 (3628 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(subsumption_resolution,[],[f144,f143])).

fof(f143,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),X0) ),
    inference(forward_demodulation,[],[f140,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f140,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f112,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f112,plain,(
    r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f111,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),X0)
      | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f107,f31])).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k4_xboole_0(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f95,f53])).

fof(f95,plain,
    ( r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f94,f93])).

fof(f93,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),X2)
      | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f89,f31])).

fof(f89,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k4_xboole_0(X2,k1_xboole_0)) ) ),
    inference(resolution,[],[f84,f53])).

fof(f84,plain,
    ( r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f83,f82])).

fof(f82,plain,(
    ! [X2] :
      ( r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(sK4(k1_xboole_0,k1_xboole_0),X2) ) ),
    inference(forward_demodulation,[],[f79,f31])).

fof(f79,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k4_xboole_0(X2,k1_xboole_0)) ) ),
    inference(resolution,[],[f71,f53])).

fof(f71,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0),sK2(k1_xboole_0,X0)),k1_xboole_0)
      | r2_hidden(sK1(k1_xboole_0,X0),X0) ) ),
    inference(superposition,[],[f58,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17,f16,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f58,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | r2_hidden(k4_tarski(sK5(k1_xboole_0,X0),sK4(k1_xboole_0,X0)),k1_xboole_0)
      | r2_hidden(sK4(k1_xboole_0,X0),X0) ) ),
    inference(superposition,[],[f30,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f30,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f83,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),X3) ) ),
    inference(subsumption_resolution,[],[f80,f82])).

fof(f80,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X3))
      | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),X3) ) ),
    inference(resolution,[],[f71,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),X3) ) ),
    inference(subsumption_resolution,[],[f90,f93])).

fof(f90,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X3))
      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),X3) ) ),
    inference(resolution,[],[f84,f52])).

fof(f111,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),X1) ) ),
    inference(subsumption_resolution,[],[f108,f110])).

fof(f108,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k4_xboole_0(k1_xboole_0,X1))
      | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),X1) ) ),
    inference(resolution,[],[f95,f52])).

fof(f144,plain,(
    ! [X1] : r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),X1) ),
    inference(subsumption_resolution,[],[f141,f143])).

fof(f141,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k4_xboole_0(k1_xboole_0,X1))
      | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),X1) ) ),
    inference(resolution,[],[f112,f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (30914)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (30914)Refutation not found, incomplete strategy% (30914)------------------------------
% 0.22/0.47  % (30914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (30914)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (30914)Memory used [KB]: 10618
% 0.22/0.47  % (30914)Time elapsed: 0.052 s
% 0.22/0.47  % (30914)------------------------------
% 0.22/0.47  % (30914)------------------------------
% 0.22/0.47  % (30918)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (30925)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (30913)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (30915)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (30926)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (30926)Refutation not found, incomplete strategy% (30926)------------------------------
% 0.22/0.48  % (30926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (30926)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (30926)Memory used [KB]: 6140
% 0.22/0.48  % (30926)Time elapsed: 0.002 s
% 0.22/0.48  % (30926)------------------------------
% 0.22/0.48  % (30926)------------------------------
% 0.22/0.48  % (30917)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (30915)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f144,f143])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),X0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f140,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.48    inference(resolution,[],[f112,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(equality_resolution,[],[f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f27,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.48    inference(rectify,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.48    inference(flattening,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.48    inference(nnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f111,f110])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),X0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f107,f31])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.48    inference(resolution,[],[f95,f53])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f94,f93])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X2] : (~r2_hidden(sK1(k1_xboole_0,k1_xboole_0),X2) | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f89,f31])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X2] : (r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k4_xboole_0(X2,k1_xboole_0))) )),
% 0.22/0.48    inference(resolution,[],[f84,f53])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f83,f82])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ( ! [X2] : (r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~r2_hidden(sK4(k1_xboole_0,k1_xboole_0),X2)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f79,f31])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X2] : (r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k4_xboole_0(X2,k1_xboole_0))) )),
% 0.22/0.48    inference(resolution,[],[f71,f53])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.48    inference(equality_resolution,[],[f64])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0),sK2(k1_xboole_0,X0)),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,X0),X0)) )),
% 0.22/0.48    inference(superposition,[],[f58,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17,f16,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.48    inference(rectify,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    k1_xboole_0 != k1_relat_1(k1_xboole_0) | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.48    inference(equality_resolution,[],[f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | r2_hidden(k4_tarski(sK5(k1_xboole_0,X0),sK4(k1_xboole_0,X0)),k1_xboole_0) | r2_hidden(sK4(k1_xboole_0,X0),X0)) )),
% 0.22/0.48    inference(superposition,[],[f30,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f23,f22,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.48    inference(rectify,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,negated_conjecture,(
% 0.22/0.48    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.22/0.48    inference(negated_conjecture,[],[f6])).
% 0.22/0.48  fof(f6,conjecture,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ( ! [X3] : (r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),X3)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f80,f82])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X3] : (r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X3)) | r2_hidden(sK4(k1_xboole_0,k1_xboole_0),X3)) )),
% 0.22/0.48    inference(resolution,[],[f71,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X3] : (r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),X3)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f90,f93])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ( ! [X3] : (r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X3)) | r2_hidden(sK1(k1_xboole_0,k1_xboole_0),X3)) )),
% 0.22/0.48    inference(resolution,[],[f84,f52])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ( ! [X1] : (r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f108,f110])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    ( ! [X1] : (r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k4_xboole_0(k1_xboole_0,X1)) | r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),X1)) )),
% 0.22/0.48    inference(resolution,[],[f95,f52])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    ( ! [X1] : (r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f141,f143])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ( ! [X1] : (r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k4_xboole_0(k1_xboole_0,X1)) | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),X1)) )),
% 0.22/0.48    inference(resolution,[],[f112,f52])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (30915)------------------------------
% 0.22/0.48  % (30915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (30915)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (30915)Memory used [KB]: 1663
% 0.22/0.48  % (30915)Time elapsed: 0.074 s
% 0.22/0.48  % (30915)------------------------------
% 0.22/0.48  % (30915)------------------------------
% 0.22/0.48  % (30908)Success in time 0.125 s
%------------------------------------------------------------------------------
