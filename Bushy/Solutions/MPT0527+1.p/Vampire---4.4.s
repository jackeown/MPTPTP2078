%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t127_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:49 EDT 2019

% Result     : Theorem 100.62s
% Output     : Refutation 100.62s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 347 expanded)
%              Number of leaves         :    9 (  83 expanded)
%              Depth                    :   25
%              Number of atoms          :  448 (2168 expanded)
%              Number of equality atoms :   42 ( 289 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41597,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41596,f52])).

fof(f52,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k8_relat_1(k3_xboole_0(sK0,sK1),sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(k3_xboole_0(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( k8_relat_1(k3_xboole_0(sK0,sK1),sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(k3_xboole_0(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t127_relat_1.p',t127_relat_1)).

fof(f41596,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f41594,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t127_relat_1.p',dt_k8_relat_1)).

fof(f41594,plain,(
    ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f41593,f52])).

fof(f41593,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f41592,f64])).

fof(f41592,plain,
    ( ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f41591,f1100])).

fof(f1100,plain,
    ( r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0)
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1099,f89])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox/benchmark/relat_1__t127_relat_1.p',d4_xboole_0)).

fof(f1099,plain,
    ( ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1094,f64])).

fof(f1094,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f319,f94])).

fof(f94,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f86,f64])).

fof(f86,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK7(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
                    & r2_hidden(sK7(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t127_relat_1.p',d12_relat_1)).

fof(f319,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f316,f52])).

fof(f316,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f258,f94])).

fof(f258,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(extensionality_resolution,[],[f59,f53])).

fof(f53,plain,(
    k8_relat_1(k3_xboole_0(sK0,sK1),sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t127_relat_1.p',d2_relat_1)).

fof(f41591,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f41590,f11051])).

fof(f11051,plain,
    ( r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f11050,f88])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11050,plain,
    ( r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK1) ),
    inference(subsumption_resolution,[],[f11047,f52])).

fof(f11047,plain,
    ( r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1098,f94])).

fof(f1098,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))
    | r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1093,f64])).

fof(f1093,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f319,f93])).

fof(f93,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f85,f64])).

fof(f85,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f41590,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK1)
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0) ),
    inference(resolution,[],[f11655,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11655,plain,
    ( ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f11654,f11453])).

fof(f11453,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f11452,f52])).

fof(f11452,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f11449])).

fof(f11449,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1132,f93])).

fof(f1132,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))
    | r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1127,f64])).

fof(f1127,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f318,f93])).

fof(f318,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2) ),
    inference(subsumption_resolution,[],[f315,f52])).

fof(f315,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f258,f93])).

fof(f11654,plain,
    ( ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f11653,f88])).

fof(f11653,plain,
    ( ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK1) ),
    inference(subsumption_resolution,[],[f11650,f52])).

fof(f11650,plain,
    ( ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f11649])).

fof(f11649,plain,
    ( ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1203,f92])).

fof(f92,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f84,f64])).

fof(f84,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1203,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1202,f89])).

fof(f1202,plain,
    ( ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1200,f52])).

fof(f1200,plain,
    ( ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f346,f92])).

fof(f346,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f345,f64])).

fof(f345,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK1,sK2))
    | ~ r2_hidden(sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f262,f92])).

fof(f262,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK4(k8_relat_1(k3_xboole_0(sK0,sK1),sK2),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(k3_xboole_0(sK0,sK1),sK2))
    | ~ v1_relat_1(k8_relat_1(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(extensionality_resolution,[],[f60,f53])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
