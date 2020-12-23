%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t60_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:03 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 524 expanded)
%              Number of leaves         :   15 ( 177 expanded)
%              Depth                    :   30
%              Number of atoms          :  261 (2109 expanded)
%              Number of equality atoms :   48 ( 334 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f999,plain,(
    $false ),
    inference(subsumption_resolution,[],[f998,f262])).

fof(f262,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f256,f188])).

fof(f188,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f182,f63])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t60_relat_1.p',fc1_xboole_0)).

fof(f182,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f181,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t60_relat_1.p',t2_xboole_1)).

fof(f181,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | ~ v1_xboole_0(X0)
      | k2_relat_1(X0) = X0 ) ),
    inference(subsumption_resolution,[],[f175,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t60_relat_1.p',t7_boole)).

fof(f175,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | ~ v1_xboole_0(X0)
      | k2_relat_1(X0) = X0
      | r2_hidden(k4_tarski(sK1(X0,X0),sK0(X0,X0)),X0) ) ),
    inference(resolution,[],[f174,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK0(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37,f36,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK0(X0,X1)),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK2(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t60_relat_1.p',d5_relat_1)).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0(X0,X0),X1)
      | ~ r1_tarski(X1,k1_xboole_0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f166,f61])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t60_relat_1.p',t6_boole)).

fof(f166,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f162,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t60_relat_1.p',d3_tarski)).

fof(f162,plain,(
    ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f159,f62])).

fof(f159,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(factoring,[],[f132])).

fof(f132,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),X1)
      | ~ r1_tarski(X1,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f127,f66])).

fof(f127,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f123,f73])).

fof(f73,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ) ),
    inference(resolution,[],[f119,f63])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_xboole_0(X1)
      | ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f118,f65])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | ~ v1_xboole_0(X1)
      | r2_hidden(sK3(X1,X1),X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( X0 != X1
      | ~ r2_hidden(k4_tarski(X2,sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | ~ v1_xboole_0(X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(subsumption_resolution,[],[f87,f65])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( X0 != X1
      | ~ r2_hidden(k4_tarski(X2,sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | ~ v1_xboole_0(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(superposition,[],[f84,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f43,f42,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t60_relat_1.p',d4_relat_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != X0
      | ~ r2_hidden(k4_tarski(X1,sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f83,f61])).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | ~ r2_hidden(k4_tarski(X0,sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | ~ r2_hidden(k4_tarski(X2,sK0(k1_xboole_0,X1)),k1_xboole_0)
      | ~ r2_hidden(sK0(k1_xboole_0,X1),X1) ) ),
    inference(superposition,[],[f51,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK0(X0,X1)),X0)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f51,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t60_relat_1.p',t60_relat_1)).

fof(f256,plain,(
    ! [X1] : ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f233,f73])).

fof(f233,plain,(
    ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0) ),
    inference(resolution,[],[f232,f74])).

fof(f74,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f232,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f227,f63])).

fof(f227,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f221,f65])).

fof(f221,plain,(
    ! [X3] :
      ( r2_hidden(sK5(k1_xboole_0,X3),k1_xboole_0)
      | ~ r2_hidden(X3,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f205,f75])).

fof(f75,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f205,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X1),k1_xboole_0)
      | r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f72,f188])).

fof(f72,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f998,plain,(
    r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f997,f233])).

fof(f997,plain,
    ( r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f994,f233])).

fof(f994,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK4(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK3(k1_xboole_0,X0),sK4(k1_xboole_0,X0)),k1_xboole_0)
      | r2_hidden(sK3(k1_xboole_0,X0),X0) ) ),
    inference(superposition,[],[f100,f59])).

fof(f100,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f94,f63])).

fof(f94,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f91,f65])).

fof(f91,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k4_tarski(sK1(k1_xboole_0,k1_xboole_0),sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0),sK0(k1_xboole_0,X0)),k1_xboole_0)
      | r2_hidden(sK0(k1_xboole_0,X0),X0) ) ),
    inference(superposition,[],[f51,f54])).
%------------------------------------------------------------------------------
