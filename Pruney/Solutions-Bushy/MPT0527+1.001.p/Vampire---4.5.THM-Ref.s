%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0527+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:08 EST 2020

% Result     : Theorem 3.15s
% Output     : Refutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 709 expanded)
%              Number of leaves         :    7 ( 178 expanded)
%              Depth                    :   21
%              Number of atoms          :  370 (3296 expanded)
%              Number of equality atoms :   41 ( 550 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5136,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5135,f3505])).

fof(f3505,plain,(
    r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f3504,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f3504,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f3503,f60])).

fof(f60,plain,(
    ! [X4] : v1_relat_1(k8_relat_1(X4,sK2)) ),
    inference(resolution,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(k3_xboole_0(sK0,sK1),sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(k3_xboole_0(X0,X1),X2)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(k3_xboole_0(sK0,sK1),sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) != k8_relat_1(k3_xboole_0(X0,X1),X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

fof(f3503,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f3486,f77])).

fof(f77,plain,(
    ! [X17,X18] : v1_relat_1(k8_relat_1(X17,k8_relat_1(X18,sK2))) ),
    inference(resolution,[],[f60,f33])).

fof(f3486,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0)
    | ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f476,f50])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK6(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
                    & r2_hidden(sK6(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(f476,plain,
    ( r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f469,f77])).

fof(f469,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2))) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != X0
      | r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,X0),k3_xboole_0(sK0,sK1))
      | r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,X0),sK6(k3_xboole_0(sK0,sK1),sK2,X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f96,f27])).

fof(f96,plain,(
    ! [X0] :
      ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != X0
      | r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,X0),k3_xboole_0(sK0,sK1))
      | r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,X0),sK6(k3_xboole_0(sK0,sK1),sK2,X0)),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f28,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f28,plain,(
    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != k8_relat_1(k3_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f5135,plain,(
    ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f5119,f3501])).

fof(f3501,plain,(
    r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK1) ),
    inference(subsumption_resolution,[],[f3483,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3483,plain,
    ( r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK1) ),
    inference(resolution,[],[f476,f773])).

fof(f773,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ r2_hidden(k4_tarski(X18,X16),k8_relat_1(X19,k8_relat_1(X17,sK2)))
      | r2_hidden(X16,X17) ) ),
    inference(subsumption_resolution,[],[f121,f77])).

fof(f121,plain,(
    ! [X19,X17,X18,X16] :
      ( r2_hidden(X16,X17)
      | ~ r2_hidden(k4_tarski(X18,X16),k8_relat_1(X19,k8_relat_1(X17,sK2)))
      | ~ v1_relat_1(k8_relat_1(X19,k8_relat_1(X17,sK2))) ) ),
    inference(subsumption_resolution,[],[f109,f60])).

fof(f109,plain,(
    ! [X19,X17,X18,X16] :
      ( r2_hidden(X16,X17)
      | ~ r2_hidden(k4_tarski(X18,X16),k8_relat_1(X19,k8_relat_1(X17,sK2)))
      | ~ v1_relat_1(k8_relat_1(X19,k8_relat_1(X17,sK2)))
      | ~ v1_relat_1(k8_relat_1(X17,sK2)) ) ),
    inference(resolution,[],[f102,f49])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,(
    ! [X24,X23,X25] :
      ( ~ r2_hidden(k4_tarski(X25,X23),k8_relat_1(X24,sK2))
      | r2_hidden(X23,X24) ) ),
    inference(subsumption_resolution,[],[f69,f60])).

fof(f69,plain,(
    ! [X24,X23,X25] :
      ( r2_hidden(X23,X24)
      | ~ r2_hidden(k4_tarski(X25,X23),k8_relat_1(X24,sK2))
      | ~ v1_relat_1(k8_relat_1(X24,sK2)) ) ),
    inference(resolution,[],[f27,f50])).

fof(f5119,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK1)
    | ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0) ),
    inference(resolution,[],[f5089,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5089,plain,(
    ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f5088,f3505])).

fof(f5088,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f5087,f4506])).

fof(f4506,plain,(
    r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2) ),
    inference(subsumption_resolution,[],[f554,f172])).

fof(f172,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ r2_hidden(k4_tarski(X16,X17),k8_relat_1(X18,k8_relat_1(X19,sK2)))
      | r2_hidden(k4_tarski(X16,X17),sK2) ) ),
    inference(subsumption_resolution,[],[f171,f60])).

fof(f171,plain,(
    ! [X19,X17,X18,X16] :
      ( r2_hidden(k4_tarski(X16,X17),sK2)
      | ~ r2_hidden(k4_tarski(X16,X17),k8_relat_1(X18,k8_relat_1(X19,sK2)))
      | ~ v1_relat_1(k8_relat_1(X19,sK2)) ) ),
    inference(subsumption_resolution,[],[f159,f77])).

fof(f159,plain,(
    ! [X19,X17,X18,X16] :
      ( r2_hidden(k4_tarski(X16,X17),sK2)
      | ~ r2_hidden(k4_tarski(X16,X17),k8_relat_1(X18,k8_relat_1(X19,sK2)))
      | ~ v1_relat_1(k8_relat_1(X18,k8_relat_1(X19,sK2)))
      | ~ v1_relat_1(k8_relat_1(X19,sK2)) ) ),
    inference(resolution,[],[f152,f49])).

fof(f152,plain,(
    ! [X21,X22,X20] :
      ( ~ r2_hidden(k4_tarski(X20,X21),k8_relat_1(X22,sK2))
      | r2_hidden(k4_tarski(X20,X21),sK2) ) ),
    inference(subsumption_resolution,[],[f68,f60])).

fof(f68,plain,(
    ! [X21,X22,X20] :
      ( r2_hidden(k4_tarski(X20,X21),sK2)
      | ~ r2_hidden(k4_tarski(X20,X21),k8_relat_1(X22,sK2))
      | ~ v1_relat_1(k8_relat_1(X22,sK2)) ) ),
    inference(resolution,[],[f27,f49])).

fof(f554,plain,
    ( r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f547,f77])).

fof(f547,plain,
    ( r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2))) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X1] :
      ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != X1
      | r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,X1),sK6(k3_xboole_0(sK0,sK1),sK2,X1)),sK2)
      | r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,X1),sK6(k3_xboole_0(sK0,sK1),sK2,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f97,f27])).

fof(f97,plain,(
    ! [X1] :
      ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != X1
      | r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,X1),sK6(k3_xboole_0(sK0,sK1),sK2,X1)),sK2)
      | r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,X1),sK6(k3_xboole_0(sK0,sK1),sK2,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f28,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5087,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f5071,f3501])).

fof(f5071,plain,
    ( ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK1)
    | ~ r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK0) ),
    inference(resolution,[],[f5012,f230])).

fof(f230,plain,(
    ! [X24,X23,X25,X22] :
      ( r2_hidden(k4_tarski(X22,X23),k8_relat_1(X25,k8_relat_1(X24,sK2)))
      | ~ r2_hidden(X23,X24)
      | ~ r2_hidden(k4_tarski(X22,X23),sK2)
      | ~ r2_hidden(X23,X25) ) ),
    inference(subsumption_resolution,[],[f229,f60])).

fof(f229,plain,(
    ! [X24,X23,X25,X22] :
      ( ~ r2_hidden(k4_tarski(X22,X23),sK2)
      | ~ r2_hidden(X23,X24)
      | r2_hidden(k4_tarski(X22,X23),k8_relat_1(X25,k8_relat_1(X24,sK2)))
      | ~ r2_hidden(X23,X25)
      | ~ v1_relat_1(k8_relat_1(X24,sK2)) ) ),
    inference(subsumption_resolution,[],[f218,f77])).

fof(f218,plain,(
    ! [X24,X23,X25,X22] :
      ( ~ r2_hidden(k4_tarski(X22,X23),sK2)
      | ~ r2_hidden(X23,X24)
      | r2_hidden(k4_tarski(X22,X23),k8_relat_1(X25,k8_relat_1(X24,sK2)))
      | ~ r2_hidden(X23,X25)
      | ~ v1_relat_1(k8_relat_1(X25,k8_relat_1(X24,sK2)))
      | ~ v1_relat_1(k8_relat_1(X24,sK2)) ) ),
    inference(resolution,[],[f177,f48])).

fof(f48,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f177,plain,(
    ! [X19,X17,X18] :
      ( r2_hidden(k4_tarski(X17,X18),k8_relat_1(X19,sK2))
      | ~ r2_hidden(k4_tarski(X17,X18),sK2)
      | ~ r2_hidden(X18,X19) ) ),
    inference(subsumption_resolution,[],[f67,f60])).

fof(f67,plain,(
    ! [X19,X17,X18] :
      ( r2_hidden(k4_tarski(X17,X18),k8_relat_1(X19,sK2))
      | ~ r2_hidden(k4_tarski(X17,X18),sK2)
      | ~ r2_hidden(X18,X19)
      | ~ v1_relat_1(k8_relat_1(X19,sK2)) ) ),
    inference(resolution,[],[f27,f48])).

fof(f5012,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f568,f4506])).

fof(f568,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f561,f77])).

fof(f561,plain,
    ( ~ r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),sK2)
    | ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2))),sK6(k3_xboole_0(sK0,sK1),sK2,k8_relat_1(sK0,k8_relat_1(sK1,sK2)))),k8_relat_1(sK0,k8_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k8_relat_1(sK0,k8_relat_1(sK1,sK2))) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2] :
      ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != X2
      | ~ r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,X2),sK6(k3_xboole_0(sK0,sK1),sK2,X2)),sK2)
      | ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,X2),k3_xboole_0(sK0,sK1))
      | ~ r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,X2),sK6(k3_xboole_0(sK0,sK1),sK2,X2)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f98,f27])).

fof(f98,plain,(
    ! [X2] :
      ( k8_relat_1(sK0,k8_relat_1(sK1,sK2)) != X2
      | ~ r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,X2),sK6(k3_xboole_0(sK0,sK1),sK2,X2)),sK2)
      | ~ r2_hidden(sK6(k3_xboole_0(sK0,sK1),sK2,X2),k3_xboole_0(sK0,sK1))
      | ~ r2_hidden(k4_tarski(sK5(k3_xboole_0(sK0,sK1),sK2,X2),sK6(k3_xboole_0(sK0,sK1),sK2,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f28,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
