%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t83_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:33 EDT 2019

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  108 (7448 expanded)
%              Number of leaves         :   12 (1814 expanded)
%              Depth                    :   39
%              Number of atoms          :  370 (39627 expanded)
%              Number of equality atoms :  107 (9403 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7591,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7572,f7495])).

fof(f7495,plain,(
    k3_xboole_0(sK1,sK0) != k1_xboole_0 ),
    inference(trivial_inequality_removal,[],[f7466])).

fof(f7466,plain,
    ( sK0 != sK0
    | k3_xboole_0(sK1,sK0) != k1_xboole_0 ),
    inference(backward_demodulation,[],[f7461,f90])).

fof(f90,plain,
    ( k4_xboole_0(sK0,sK1) != sK0
    | k3_xboole_0(sK1,sK0) != k1_xboole_0 ),
    inference(resolution,[],[f81,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t83_xboole_1.p',d7_xboole_0)).

fof(f81,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | k4_xboole_0(sK0,sK1) != sK0 ),
    inference(resolution,[],[f46,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t83_xboole_1.p',symmetry_r1_xboole_0)).

fof(f46,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != sK0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( k4_xboole_0(sK0,sK1) != sK0
      | ~ r1_xboole_0(sK0,sK1) )
    & ( k4_xboole_0(sK0,sK1) = sK0
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( k4_xboole_0(sK0,sK1) != sK0
        | ~ r1_xboole_0(sK0,sK1) )
      & ( k4_xboole_0(sK0,sK1) = sK0
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t83_xboole_1.p',t83_xboole_1)).

fof(f7461,plain,(
    k4_xboole_0(sK0,sK1) = sK0 ),
    inference(subsumption_resolution,[],[f7460,f45])).

fof(f45,plain,
    ( r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f31])).

fof(f7460,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = sK0 ),
    inference(subsumption_resolution,[],[f7459,f5331])).

fof(f5331,plain,(
    r2_hidden(sK2(sK0,sK1,sK0),sK0) ),
    inference(subsumption_resolution,[],[f5330,f4692])).

fof(f4692,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X2,X1) = k1_xboole_0
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(superposition,[],[f4658,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f33])).

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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t83_xboole_1.p',d5_xboole_0)).

fof(f4658,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),X1) = k1_xboole_0 ),
    inference(resolution,[],[f4626,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4626,plain,(
    ! [X2,X3] : r1_xboole_0(k4_xboole_0(X2,X3),X3) ),
    inference(resolution,[],[f4615,f57])).

fof(f4615,plain,(
    ! [X2,X3] : r1_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(trivial_inequality_removal,[],[f4573])).

fof(f4573,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X2,k4_xboole_0(X3,X2)) ) ),
    inference(superposition,[],[f56,f4555])).

fof(f4555,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(duplicate_literal_removal,[],[f4531])).

fof(f4531,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k1_xboole_0
      | k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k1_xboole_0 ) ),
    inference(resolution,[],[f2521,f1870])).

fof(f1870,plain,(
    ! [X23,X22] :
      ( r2_hidden(sK4(X22,X23,k1_xboole_0),X23)
      | k3_xboole_0(X22,X23) = k1_xboole_0 ) ),
    inference(resolution,[],[f1805,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t83_xboole_1.p',d4_xboole_0)).

fof(f1805,plain,(
    ! [X6] : ~ r2_hidden(X6,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1795,f1794])).

fof(f1794,plain,(
    ! [X4,X3] :
      ( r2_hidden(X4,X3)
      | ~ r2_hidden(X4,k1_xboole_0) ) ),
    inference(superposition,[],[f72,f1607])).

fof(f1607,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(trivial_inequality_removal,[],[f1604])).

fof(f1604,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k4_xboole_0(X0,X0) = k1_xboole_0 ) ),
    inference(equality_factoring,[],[f1541])).

fof(f1541,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X0) = k1_xboole_0
      | k4_xboole_0(X1,X1) = k1_xboole_0 ) ),
    inference(subsumption_resolution,[],[f1533,f1512])).

fof(f1512,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK0,sK1),sK0)
      | k4_xboole_0(X2,X2) = k1_xboole_0 ) ),
    inference(resolution,[],[f1018,f75])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1018,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK0,sK1),k3_xboole_0(sK0,sK1))
      | k4_xboole_0(X1,X1) = k1_xboole_0 ) ),
    inference(trivial_inequality_removal,[],[f1007])).

fof(f1007,plain,(
    ! [X1] :
      ( sK0 != sK0
      | r2_hidden(sK3(sK0,sK1),k3_xboole_0(sK0,sK1))
      | k4_xboole_0(X1,X1) = k1_xboole_0 ) ),
    inference(superposition,[],[f80,f945])).

fof(f945,plain,(
    ! [X2] :
      ( k4_xboole_0(X2,X2) = k1_xboole_0
      | k4_xboole_0(sK0,sK1) = sK0 ) ),
    inference(duplicate_literal_removal,[],[f894])).

fof(f894,plain,(
    ! [X2] :
      ( k4_xboole_0(X2,X2) = k1_xboole_0
      | k4_xboole_0(sK0,sK1) = sK0
      | k4_xboole_0(sK0,sK1) = sK0 ) ),
    inference(superposition,[],[f888,f78])).

fof(f78,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0
    | k4_xboole_0(sK0,sK1) = sK0 ),
    inference(resolution,[],[f45,f55])).

fof(f888,plain,(
    ! [X3] :
      ( k4_xboole_0(X3,X3) = k3_xboole_0(sK0,sK1)
      | k4_xboole_0(sK0,sK1) = sK0 ) ),
    inference(subsumption_resolution,[],[f885,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
      | k4_xboole_0(sK0,sK1) = sK0 ) ),
    inference(resolution,[],[f45,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t83_xboole_1.p',t4_xboole_0)).

fof(f885,plain,(
    ! [X3] :
      ( k4_xboole_0(X3,X3) = k3_xboole_0(sK0,sK1)
      | k4_xboole_0(sK0,sK1) = sK0
      | r2_hidden(sK2(X3,X3,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f841])).

fof(f841,plain,(
    ! [X3] :
      ( k4_xboole_0(X3,X3) = k3_xboole_0(sK0,sK1)
      | k4_xboole_0(sK0,sK1) = sK0
      | k4_xboole_0(X3,X3) = k3_xboole_0(sK0,sK1)
      | r2_hidden(sK2(X3,X3,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f98,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK2(X11,X12,k3_xboole_0(sK0,sK1)),X11)
      | k4_xboole_0(X11,X12) = k3_xboole_0(sK0,sK1)
      | k4_xboole_0(sK0,sK1) = sK0 ) ),
    inference(resolution,[],[f76,f50])).

fof(f80,plain,
    ( k4_xboole_0(sK0,sK1) != sK0
    | r2_hidden(sK3(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f46,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1533,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X0) = k1_xboole_0
      | ~ r2_hidden(sK3(sK0,sK1),sK0)
      | k4_xboole_0(X1,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f1513,f1011])).

fof(f1011,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK1)
      | ~ r2_hidden(X6,sK0)
      | k4_xboole_0(X7,X7) = k1_xboole_0 ) ),
    inference(superposition,[],[f71,f945])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1513,plain,(
    ! [X3] :
      ( r2_hidden(sK3(sK0,sK1),sK1)
      | k4_xboole_0(X3,X3) = k1_xboole_0 ) ),
    inference(resolution,[],[f1018,f74])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1795,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | ~ r2_hidden(X6,X5) ) ),
    inference(superposition,[],[f71,f1607])).

fof(f2521,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(sK4(X11,X12,k1_xboole_0),k4_xboole_0(X13,X11))
      | k3_xboole_0(X11,X12) = k1_xboole_0 ) ),
    inference(resolution,[],[f1869,f71])).

fof(f1869,plain,(
    ! [X21,X20] :
      ( r2_hidden(sK4(X20,X21,k1_xboole_0),X20)
      | k3_xboole_0(X20,X21) = k1_xboole_0 ) ),
    inference(resolution,[],[f1805,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5330,plain,
    ( k3_xboole_0(sK0,sK1) != k1_xboole_0
    | r2_hidden(sK2(sK0,sK1,sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f5329])).

fof(f5329,plain,
    ( k3_xboole_0(sK0,sK1) != k1_xboole_0
    | r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | r2_hidden(sK2(sK0,sK1,sK0),sK0) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X0] :
      ( sK0 != X0
      | k3_xboole_0(sK0,sK1) != k1_xboole_0
      | r2_hidden(sK2(sK0,sK1,X0),sK0)
      | r2_hidden(sK2(sK0,sK1,X0),X0) ) ),
    inference(superposition,[],[f82,f50])).

fof(f82,plain,
    ( k4_xboole_0(sK0,sK1) != sK0
    | k3_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(resolution,[],[f46,f56])).

fof(f7459,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = sK0
    | ~ r2_hidden(sK2(sK0,sK1,sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f7446])).

fof(f7446,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = sK0
    | ~ r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | ~ r2_hidden(sK2(sK0,sK1,sK0),sK0) ),
    inference(resolution,[],[f7324,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7324,plain,(
    ! [X100] :
      ( ~ r2_hidden(sK2(sK0,sK1,sK0),X100)
      | ~ r1_xboole_0(sK0,X100) ) ),
    inference(resolution,[],[f7191,f5331])).

fof(f7191,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f7165,f73])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7165,plain,(
    ! [X24,X23,X25] :
      ( ~ r2_hidden(X25,k3_xboole_0(X23,X24))
      | ~ r1_xboole_0(X24,X23) ) ),
    inference(superposition,[],[f5201,f54])).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t83_xboole_1.p',t3_boole)).

fof(f5201,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(X5,k4_xboole_0(k3_xboole_0(X4,X3),X6))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f5120,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t83_xboole_1.p',commutativity_k3_xboole_0)).

fof(f5120,plain,(
    ! [X107,X105,X106,X104] :
      ( ~ r2_hidden(X104,k4_xboole_0(k3_xboole_0(X105,X106),X107))
      | ~ r1_xboole_0(X105,X106) ) ),
    inference(resolution,[],[f2321,f59])).

fof(f2321,plain,(
    ! [X30,X31,X29,X32] :
      ( r2_hidden(sK4(k1_xboole_0,X32,k4_xboole_0(X30,X31)),X30)
      | ~ r2_hidden(X29,k4_xboole_0(X30,X31)) ) ),
    inference(resolution,[],[f1909,f72])).

fof(f1909,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(sK4(k1_xboole_0,X7,X8),X8)
      | ~ r2_hidden(X9,X8) ) ),
    inference(subsumption_resolution,[],[f1900,f1805])).

fof(f1900,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X9,X8)
      | r2_hidden(sK4(k1_xboole_0,X7,X8),k1_xboole_0)
      | r2_hidden(sK4(k1_xboole_0,X7,X8),X8) ) ),
    inference(superposition,[],[f1857,f63])).

fof(f1857,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(resolution,[],[f1805,f75])).

fof(f7572,plain,(
    k3_xboole_0(sK1,sK0) = k1_xboole_0 ),
    inference(superposition,[],[f4555,f7461])).
%------------------------------------------------------------------------------
