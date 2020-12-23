%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0694+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:55 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 248 expanded)
%              Number of clauses        :   62 (  71 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  556 (1292 expanded)
%              Number of equality atoms :  104 ( 218 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
        & r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) = X3
        & r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK0(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
                  & r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
                    & r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20,f19,f18])).

fof(f40,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f63,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))
      & v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ r1_tarski(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))
    & v1_funct_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f15,f34])).

fof(f60,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
                | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
                  & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f39,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f38,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f37,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ~ r1_tarski(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_802,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1222,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))
    | sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) != X0
    | k3_xboole_0(k9_relat_1(sK8,sK6),sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_1429,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(sK7,k9_relat_1(sK8,sK6)))
    | r2_hidden(sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))
    | sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) != X0
    | k3_xboole_0(k9_relat_1(sK8,sK6),sK7) != k3_xboole_0(sK7,k9_relat_1(sK8,sK6)) ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_13632,plain,
    ( r2_hidden(sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))
    | ~ r2_hidden(k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)))),k3_xboole_0(sK7,k9_relat_1(sK8,sK6)))
    | sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) != k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))))
    | k3_xboole_0(k9_relat_1(sK8,sK6),sK7) != k3_xboole_0(sK7,k9_relat_1(sK8,sK6)) ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1842,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k9_relat_1(sK8,X2))
    | r2_hidden(X0,k3_xboole_0(X1,k9_relat_1(sK8,X2))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2999,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)))),k9_relat_1(sK8,X0))
    | r2_hidden(k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)))),k3_xboole_0(sK7,k9_relat_1(sK8,X0)))
    | ~ r2_hidden(k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)))),sK7) ),
    inference(instantiation,[status(thm)],[c_1842])).

cnf(c_6896,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)))),k9_relat_1(sK8,sK6))
    | r2_hidden(k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)))),k3_xboole_0(sK7,k9_relat_1(sK8,sK6)))
    | ~ r2_hidden(k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)))),sK7) ),
    inference(instantiation,[status(thm)],[c_2999])).

cnf(c_797,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1788,plain,
    ( X0 != X1
    | sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) != X1
    | sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) = X0 ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_2359,plain,
    ( X0 != sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))
    | sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) = X0
    | sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) != sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_1788])).

cnf(c_3836,plain,
    ( sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) != sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))
    | sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) = k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))))
    | k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)))) != sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_2359])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_429,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_430,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_434,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_25])).

cnf(c_435,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) ),
    inference(renaming,[status(thm)],[c_434])).

cnf(c_1314,plain,
    ( ~ r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),X0)
    | ~ r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)))),k9_relat_1(sK8,X0)) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_3541,plain,
    ( ~ r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),k1_relat_1(sK8))
    | ~ r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),sK6)
    | r2_hidden(k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)))),k9_relat_1(sK8,sK6)) ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1581,plain,
    ( r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),X0)
    | ~ r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2180,plain,
    ( ~ r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))
    | r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),sK6) ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_796,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2098,plain,
    ( sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) = sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1604,plain,
    ( k3_xboole_0(k9_relat_1(sK8,sK6),sK7) = k3_xboole_0(sK7,k9_relat_1(sK8,sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_495,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_496,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(k1_funct_1(sK8,X0),X1)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_500,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),X1)
    | ~ r2_hidden(X0,k10_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_25])).

cnf(c_501,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK8,X1))
    | r2_hidden(k1_funct_1(sK8,X0),X1) ),
    inference(renaming,[status(thm)],[c_500])).

cnf(c_1547,plain,
    ( ~ r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),k10_relat_1(sK8,sK7))
    | r2_hidden(k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)))),sK7) ),
    inference(instantiation,[status(thm)],[c_501])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1227,plain,
    ( r2_hidden(X0,k10_relat_1(sK8,X1))
    | ~ r2_hidden(X0,k3_xboole_0(X2,k10_relat_1(sK8,X1))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1486,plain,
    ( r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),k10_relat_1(sK8,sK7))
    | ~ r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7))) ),
    inference(instantiation,[status(thm)],[c_1227])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_570,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_571,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,sK2(sK8,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_575,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | k1_funct_1(sK8,sK2(sK8,X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_25])).

cnf(c_1287,plain,
    ( ~ r2_hidden(sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)),k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))))
    | k1_funct_1(sK8,sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)))) = sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_552,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_553,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),X1)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_557,plain,
    ( r2_hidden(sK2(sK8,X1,X0),X1)
    | ~ r2_hidden(X0,k9_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_25])).

cnf(c_558,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),X1) ),
    inference(renaming,[status(thm)],[c_557])).

cnf(c_1281,plain,
    ( r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))
    | ~ r2_hidden(sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)),k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))) ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_534,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_535,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),k1_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_539,plain,
    ( r2_hidden(sK2(sK8,X1,X0),k1_relat_1(sK8))
    | ~ r2_hidden(X0,k9_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_25])).

cnf(c_540,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),k1_relat_1(sK8)) ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_1245,plain,
    ( r2_hidden(sK2(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)),sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7))),k1_relat_1(sK8))
    | ~ r2_hidden(sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)),k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))) ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK4(X0,X1),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_289,plain,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))) != X0
    | k3_xboole_0(k9_relat_1(sK8,sK6),sK7) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_290,plain,
    ( ~ r2_hidden(sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK4(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_282,plain,
    ( r2_hidden(sK4(X0,X1),X0)
    | k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))) != X0
    | k3_xboole_0(k9_relat_1(sK8,sK6),sK7) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_283,plain,
    ( r2_hidden(sK4(k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7))),k3_xboole_0(k9_relat_1(sK8,sK6),sK7)),k9_relat_1(sK8,k3_xboole_0(sK6,k10_relat_1(sK8,sK7)))) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13632,c_6896,c_3836,c_3541,c_2180,c_2098,c_1604,c_1547,c_1486,c_1287,c_1281,c_1245,c_290,c_283])).


%------------------------------------------------------------------------------
