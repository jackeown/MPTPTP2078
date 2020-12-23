%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t3_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:17 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 154 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  263 ( 869 expanded)
%              Number of equality atoms :   64 ( 220 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2847,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2846,f69])).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t3_setfam_1.p',t2_xboole_1)).

fof(f2846,plain,(
    ~ r1_tarski(k1_xboole_0,k3_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1718,f74])).

fof(f74,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | k1_xboole_0 != X1
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK5(X0,X1),sK6(X0,X1))
                  & r2_hidden(sK6(X0,X1),X0) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK5(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK7(X0,X5))
                    & r2_hidden(sK7(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f45,f48,f47,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK5(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK5(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK7(X0,X5))
        & r2_hidden(sK7(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t3_setfam_1.p',d1_setfam_1)).

fof(f1718,plain,(
    ~ r1_tarski(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f1717,f50])).

fof(f50,plain,(
    ~ r1_tarski(k1_setfam_1(sK0),k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ~ r1_tarski(k1_setfam_1(sK0),k3_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f32])).

fof(f32,plain,
    ( ? [X0] : ~ r1_tarski(k1_setfam_1(X0),k3_tarski(X0))
   => ~ r1_tarski(k1_setfam_1(sK0),k3_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] : ~ r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t3_setfam_1.p',t3_setfam_1)).

fof(f1717,plain,(
    k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f1707])).

fof(f1707,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f1645,f1565])).

fof(f1565,plain,(
    ! [X20] :
      ( r2_hidden(X20,k1_setfam_1(sK0))
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f1562])).

fof(f1562,plain,(
    ! [X20] :
      ( k1_xboole_0 = sK0
      | r2_hidden(X20,k1_setfam_1(sK0))
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f1538,f78])).

fof(f78,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK7(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK7(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1538,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f1497])).

fof(f1497,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f88,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k1_setfam_1(sK0),k3_tarski(sK0)),X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f81,f70])).

fof(f70,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(X2,sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t3_setfam_1.p',d4_tarski)).

fof(f81,plain,(
    ~ r2_hidden(sK1(k1_setfam_1(sK0),k3_tarski(sK0)),k3_tarski(sK0)) ),
    inference(resolution,[],[f50,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/setfam_1__t3_setfam_1.p',d3_tarski)).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_setfam_1(sK0),k3_tarski(sK0)),X0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f80,f79])).

fof(f79,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    r2_hidden(sK1(k1_setfam_1(sK0),k3_tarski(sK0)),k1_setfam_1(sK0)) ),
    inference(resolution,[],[f50,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1645,plain,(
    ! [X16] :
      ( ~ r2_hidden(k1_setfam_1(sK0),X16)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f1565,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t3_setfam_1.p',antisymmetry_r2_hidden)).
%------------------------------------------------------------------------------
