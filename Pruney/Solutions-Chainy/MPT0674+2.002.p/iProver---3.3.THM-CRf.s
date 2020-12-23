%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:15 EST 2020

% Result     : Theorem 15.46s
% Output     : CNFRefutation 15.46s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 766 expanded)
%              Number of clauses        :   59 ( 209 expanded)
%              Number of leaves         :   15 ( 167 expanded)
%              Depth                    :   22
%              Number of atoms          :  464 (2970 expanded)
%              Number of equality atoms :  206 (1205 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f66,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f62])).

fof(f67,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f66])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0)
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0)
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0)
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK6,sK5)) != k11_relat_1(sK6,sK5)
      & r2_hidden(sK5,k1_relat_1(sK6))
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k1_tarski(k1_funct_1(sK6,sK5)) != k11_relat_1(sK6,sK5)
    & r2_hidden(sK5,k1_relat_1(sK6))
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f16,f33])).

fof(f56,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
        & r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
              ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK2(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2)
                  & r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
                    & r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f29,f28,f27])).

fof(f48,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f70,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f37,f39])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    k1_tarski(k1_funct_1(sK6,sK5)) != k11_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k11_relat_1(sK6,sK5) ),
    inference(definition_unfolding,[],[f59,f39])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f68,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f58,plain,(
    r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27207,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27193,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_tarski(X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27205,plain,
    ( k9_relat_1(X0,k2_tarski(X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_27649,plain,
    ( k9_relat_1(sK6,k2_tarski(X0,X0)) = k11_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_27193,c_27205])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_27199,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_29490,plain,
    ( r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k11_relat_1(sK6,X1)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_27649,c_27199])).

cnf(c_24,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_25,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30251,plain,
    ( r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k11_relat_1(sK6,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29490,c_24,c_25])).

cnf(c_30261,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k11_relat_1(sK6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27207,c_30251])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | sK0(X0,X1) = X0
    | k2_tarski(X0,X0) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27208,plain,
    ( sK0(X0,X1) = X0
    | k2_tarski(X0,X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_27202,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_18,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27196,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_28062,plain,
    ( k1_funct_1(X0,sK1(X1,X2,X0)) = X1
    | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27202,c_27196])).

cnf(c_35820,plain,
    ( k1_funct_1(sK6,sK1(X0,k2_tarski(X1,X1),sK6)) = X0
    | r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_27649,c_28062])).

cnf(c_36593,plain,
    ( k1_funct_1(sK6,sK1(X0,k2_tarski(X1,X1),sK6)) = X0
    | r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35820,c_24,c_25])).

cnf(c_36601,plain,
    ( k1_funct_1(sK6,sK1(sK0(X0,k11_relat_1(sK6,X1)),k2_tarski(X1,X1),sK6)) = sK0(X0,k11_relat_1(sK6,X1))
    | sK0(X0,k11_relat_1(sK6,X1)) = X0
    | k2_tarski(X0,X0) = k11_relat_1(sK6,X1) ),
    inference(superposition,[status(thm)],[c_27208,c_36593])).

cnf(c_20,negated_conjecture,
    ( k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k11_relat_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_43745,plain,
    ( k1_funct_1(sK6,sK1(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,X0)),k2_tarski(X0,X0),sK6)) = sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,X0))
    | k11_relat_1(sK6,X0) != k11_relat_1(sK6,sK5)
    | sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,X0)) = k1_funct_1(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_36601,c_20])).

cnf(c_45718,plain,
    ( k1_funct_1(sK6,sK1(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k2_tarski(sK5,sK5),sK6)) = sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5))
    | sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
    inference(equality_resolution,[status(thm)],[c_43745])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_27203,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27206,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_27914,plain,
    ( sK1(X0,k2_tarski(X1,X1),X2) = X1
    | r2_hidden(X0,k9_relat_1(X2,k2_tarski(X1,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27203,c_27206])).

cnf(c_28331,plain,
    ( sK1(X0,k2_tarski(X1,X1),sK6) = X1
    | r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_27649,c_27914])).

cnf(c_28375,plain,
    ( r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
    | sK1(X0,k2_tarski(X1,X1),sK6) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28331,c_24])).

cnf(c_28376,plain,
    ( sK1(X0,k2_tarski(X1,X1),sK6) = X1
    | r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_28375])).

cnf(c_28383,plain,
    ( sK1(sK0(X0,k11_relat_1(sK6,X1)),k2_tarski(X1,X1),sK6) = X1
    | sK0(X0,k11_relat_1(sK6,X1)) = X0
    | k2_tarski(X0,X0) = k11_relat_1(sK6,X1) ),
    inference(superposition,[status(thm)],[c_27208,c_28376])).

cnf(c_28821,plain,
    ( sK1(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,X0)),k2_tarski(X0,X0),sK6) = X0
    | k11_relat_1(sK6,X0) != k11_relat_1(sK6,sK5)
    | sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,X0)) = k1_funct_1(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_28383,c_20])).

cnf(c_28993,plain,
    ( sK1(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k2_tarski(sK5,sK5),sK6) = sK5
    | sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
    inference(equality_resolution,[status(thm)],[c_28821])).

cnf(c_43679,plain,
    ( sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) = k1_funct_1(sK6,sK5)
    | k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k11_relat_1(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_28993,c_36601])).

cnf(c_46329,plain,
    ( sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45718,c_20,c_43679])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | sK0(X0,X1) != X0
    | k2_tarski(X0,X0) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_27209,plain,
    ( sK0(X0,X1) != X0
    | k2_tarski(X0,X0) = X1
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_46345,plain,
    ( k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k11_relat_1(sK6,sK5)
    | r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_46329,c_27209])).

cnf(c_46365,plain,
    ( k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k11_relat_1(sK6,sK5)
    | r2_hidden(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_46345,c_46329])).

cnf(c_27393,plain,
    ( ~ r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5))
    | sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
    | k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k11_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_27394,plain,
    ( sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
    | k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k11_relat_1(sK6,sK5)
    | r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27393])).

cnf(c_220,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_217,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_29329,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_220,c_217])).

cnf(c_27793,plain,
    ( r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5))
    | sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
    inference(resolution,[status(thm)],[c_1,c_20])).

cnf(c_31959,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK5),X0)
    | r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),X0)
    | r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5)) ),
    inference(resolution,[status(thm)],[c_29329,c_27793])).

cnf(c_32237,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5))
    | r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5)) ),
    inference(factoring,[status(thm)],[c_31959])).

cnf(c_32238,plain,
    ( r2_hidden(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top
    | r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32237])).

cnf(c_54618,plain,
    ( r2_hidden(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46365,c_20,c_27394,c_32238,c_43679])).

cnf(c_54626,plain,
    ( r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_30261,c_54618])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,k1_relat_1(sK6)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,plain,
    ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54626,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:40:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.46/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.46/2.48  
% 15.46/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.46/2.48  
% 15.46/2.48  ------  iProver source info
% 15.46/2.48  
% 15.46/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.46/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.46/2.48  git: non_committed_changes: false
% 15.46/2.48  git: last_make_outside_of_git: false
% 15.46/2.48  
% 15.46/2.48  ------ 
% 15.46/2.48  ------ Parsing...
% 15.46/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.46/2.48  ------ Proving...
% 15.46/2.48  ------ Problem Properties 
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  clauses                                 24
% 15.46/2.48  conjectures                             4
% 15.46/2.48  EPR                                     2
% 15.46/2.48  Horn                                    20
% 15.46/2.48  unary                                   5
% 15.46/2.48  binary                                  2
% 15.46/2.48  lits                                    80
% 15.46/2.48  lits eq                                 15
% 15.46/2.48  fd_pure                                 0
% 15.46/2.48  fd_pseudo                               0
% 15.46/2.48  fd_cond                                 0
% 15.46/2.48  fd_pseudo_cond                          7
% 15.46/2.48  AC symbols                              0
% 15.46/2.48  
% 15.46/2.48  ------ Input Options Time Limit: Unbounded
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 15.46/2.48  Current options:
% 15.46/2.48  ------ 
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  ------ Proving...
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.46/2.48  
% 15.46/2.48  ------ Proving...
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.46/2.48  
% 15.46/2.48  ------ Proving...
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.46/2.48  
% 15.46/2.48  ------ Proving...
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.46/2.48  
% 15.46/2.48  ------ Proving...
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.46/2.48  
% 15.46/2.48  ------ Proving...
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.46/2.48  
% 15.46/2.48  ------ Proving...
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.46/2.48  
% 15.46/2.48  ------ Proving...
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.46/2.48  
% 15.46/2.48  ------ Proving...
% 15.46/2.48  
% 15.46/2.48  
% 15.46/2.48  % SZS status Theorem for theBenchmark.p
% 15.46/2.48  
% 15.46/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.46/2.48  
% 15.46/2.48  fof(f1,axiom,(
% 15.46/2.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f17,plain,(
% 15.46/2.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 15.46/2.48    inference(nnf_transformation,[],[f1])).
% 15.46/2.48  
% 15.46/2.48  fof(f18,plain,(
% 15.46/2.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 15.46/2.48    inference(rectify,[],[f17])).
% 15.46/2.48  
% 15.46/2.48  fof(f19,plain,(
% 15.46/2.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 15.46/2.48    introduced(choice_axiom,[])).
% 15.46/2.48  
% 15.46/2.48  fof(f20,plain,(
% 15.46/2.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 15.46/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 15.46/2.48  
% 15.46/2.48  fof(f36,plain,(
% 15.46/2.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 15.46/2.48    inference(cnf_transformation,[],[f20])).
% 15.46/2.48  
% 15.46/2.48  fof(f2,axiom,(
% 15.46/2.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f39,plain,(
% 15.46/2.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f2])).
% 15.46/2.48  
% 15.46/2.48  fof(f62,plain,(
% 15.46/2.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 15.46/2.48    inference(definition_unfolding,[],[f36,f39])).
% 15.46/2.48  
% 15.46/2.48  fof(f66,plain,(
% 15.46/2.48    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 15.46/2.48    inference(equality_resolution,[],[f62])).
% 15.46/2.48  
% 15.46/2.48  fof(f67,plain,(
% 15.46/2.48    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 15.46/2.48    inference(equality_resolution,[],[f66])).
% 15.46/2.48  
% 15.46/2.48  fof(f7,conjecture,(
% 15.46/2.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f8,negated_conjecture,(
% 15.46/2.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 15.46/2.48    inference(negated_conjecture,[],[f7])).
% 15.46/2.48  
% 15.46/2.48  fof(f15,plain,(
% 15.46/2.48    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 15.46/2.48    inference(ennf_transformation,[],[f8])).
% 15.46/2.48  
% 15.46/2.48  fof(f16,plain,(
% 15.46/2.48    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 15.46/2.48    inference(flattening,[],[f15])).
% 15.46/2.48  
% 15.46/2.48  fof(f33,plain,(
% 15.46/2.48    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK6,sK5)) != k11_relat_1(sK6,sK5) & r2_hidden(sK5,k1_relat_1(sK6)) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 15.46/2.48    introduced(choice_axiom,[])).
% 15.46/2.48  
% 15.46/2.48  fof(f34,plain,(
% 15.46/2.48    k1_tarski(k1_funct_1(sK6,sK5)) != k11_relat_1(sK6,sK5) & r2_hidden(sK5,k1_relat_1(sK6)) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 15.46/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f16,f33])).
% 15.46/2.48  
% 15.46/2.48  fof(f56,plain,(
% 15.46/2.48    v1_relat_1(sK6)),
% 15.46/2.48    inference(cnf_transformation,[],[f34])).
% 15.46/2.48  
% 15.46/2.48  fof(f3,axiom,(
% 15.46/2.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f9,plain,(
% 15.46/2.48    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 15.46/2.48    inference(ennf_transformation,[],[f3])).
% 15.46/2.48  
% 15.46/2.48  fof(f40,plain,(
% 15.46/2.48    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f9])).
% 15.46/2.48  
% 15.46/2.48  fof(f64,plain,(
% 15.46/2.48    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1)) | ~v1_relat_1(X0)) )),
% 15.46/2.48    inference(definition_unfolding,[],[f40,f39])).
% 15.46/2.48  
% 15.46/2.48  fof(f5,axiom,(
% 15.46/2.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f11,plain,(
% 15.46/2.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.46/2.48    inference(ennf_transformation,[],[f5])).
% 15.46/2.48  
% 15.46/2.48  fof(f12,plain,(
% 15.46/2.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.46/2.48    inference(flattening,[],[f11])).
% 15.46/2.48  
% 15.46/2.48  fof(f25,plain,(
% 15.46/2.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.46/2.48    inference(nnf_transformation,[],[f12])).
% 15.46/2.48  
% 15.46/2.48  fof(f26,plain,(
% 15.46/2.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.46/2.48    inference(rectify,[],[f25])).
% 15.46/2.48  
% 15.46/2.48  fof(f29,plain,(
% 15.46/2.48    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 & r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))))),
% 15.46/2.48    introduced(choice_axiom,[])).
% 15.46/2.48  
% 15.46/2.48  fof(f28,plain,(
% 15.46/2.48    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))))) )),
% 15.46/2.48    introduced(choice_axiom,[])).
% 15.46/2.48  
% 15.46/2.48  fof(f27,plain,(
% 15.46/2.48    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK2(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK2(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 15.46/2.48    introduced(choice_axiom,[])).
% 15.46/2.48  
% 15.46/2.48  fof(f30,plain,(
% 15.46/2.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK2(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X1,X6)) = X6 & r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.46/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f29,f28,f27])).
% 15.46/2.48  
% 15.46/2.48  fof(f48,plain,(
% 15.46/2.48    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f30])).
% 15.46/2.48  
% 15.46/2.48  fof(f69,plain,(
% 15.46/2.48    ( ! [X2,X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),X2) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.46/2.48    inference(equality_resolution,[],[f48])).
% 15.46/2.48  
% 15.46/2.48  fof(f70,plain,(
% 15.46/2.48    ( ! [X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.46/2.48    inference(equality_resolution,[],[f69])).
% 15.46/2.48  
% 15.46/2.48  fof(f57,plain,(
% 15.46/2.48    v1_funct_1(sK6)),
% 15.46/2.48    inference(cnf_transformation,[],[f34])).
% 15.46/2.48  
% 15.46/2.48  fof(f37,plain,(
% 15.46/2.48    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f20])).
% 15.46/2.48  
% 15.46/2.48  fof(f61,plain,(
% 15.46/2.48    ( ! [X0,X1] : (k2_tarski(X0,X0) = X1 | sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)) )),
% 15.46/2.48    inference(definition_unfolding,[],[f37,f39])).
% 15.46/2.48  
% 15.46/2.48  fof(f4,axiom,(
% 15.46/2.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f10,plain,(
% 15.46/2.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 15.46/2.48    inference(ennf_transformation,[],[f4])).
% 15.46/2.48  
% 15.46/2.48  fof(f21,plain,(
% 15.46/2.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 15.46/2.48    inference(nnf_transformation,[],[f10])).
% 15.46/2.48  
% 15.46/2.48  fof(f22,plain,(
% 15.46/2.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 15.46/2.48    inference(rectify,[],[f21])).
% 15.46/2.48  
% 15.46/2.48  fof(f23,plain,(
% 15.46/2.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 15.46/2.48    introduced(choice_axiom,[])).
% 15.46/2.48  
% 15.46/2.48  fof(f24,plain,(
% 15.46/2.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 15.46/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 15.46/2.48  
% 15.46/2.48  fof(f42,plain,(
% 15.46/2.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f24])).
% 15.46/2.48  
% 15.46/2.48  fof(f6,axiom,(
% 15.46/2.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 15.46/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.46/2.48  
% 15.46/2.48  fof(f13,plain,(
% 15.46/2.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 15.46/2.48    inference(ennf_transformation,[],[f6])).
% 15.46/2.48  
% 15.46/2.48  fof(f14,plain,(
% 15.46/2.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 15.46/2.48    inference(flattening,[],[f13])).
% 15.46/2.48  
% 15.46/2.48  fof(f31,plain,(
% 15.46/2.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 15.46/2.48    inference(nnf_transformation,[],[f14])).
% 15.46/2.48  
% 15.46/2.48  fof(f32,plain,(
% 15.46/2.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 15.46/2.48    inference(flattening,[],[f31])).
% 15.46/2.48  
% 15.46/2.48  fof(f54,plain,(
% 15.46/2.48    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f32])).
% 15.46/2.48  
% 15.46/2.48  fof(f59,plain,(
% 15.46/2.48    k1_tarski(k1_funct_1(sK6,sK5)) != k11_relat_1(sK6,sK5)),
% 15.46/2.48    inference(cnf_transformation,[],[f34])).
% 15.46/2.48  
% 15.46/2.48  fof(f65,plain,(
% 15.46/2.48    k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k11_relat_1(sK6,sK5)),
% 15.46/2.48    inference(definition_unfolding,[],[f59,f39])).
% 15.46/2.48  
% 15.46/2.48  fof(f43,plain,(
% 15.46/2.48    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f24])).
% 15.46/2.48  
% 15.46/2.48  fof(f35,plain,(
% 15.46/2.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 15.46/2.48    inference(cnf_transformation,[],[f20])).
% 15.46/2.48  
% 15.46/2.48  fof(f63,plain,(
% 15.46/2.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 15.46/2.48    inference(definition_unfolding,[],[f35,f39])).
% 15.46/2.48  
% 15.46/2.48  fof(f68,plain,(
% 15.46/2.48    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 15.46/2.48    inference(equality_resolution,[],[f63])).
% 15.46/2.48  
% 15.46/2.48  fof(f38,plain,(
% 15.46/2.48    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.46/2.48    inference(cnf_transformation,[],[f20])).
% 15.46/2.48  
% 15.46/2.48  fof(f60,plain,(
% 15.46/2.48    ( ! [X0,X1] : (k2_tarski(X0,X0) = X1 | sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.46/2.48    inference(definition_unfolding,[],[f38,f39])).
% 15.46/2.48  
% 15.46/2.48  fof(f58,plain,(
% 15.46/2.48    r2_hidden(sK5,k1_relat_1(sK6))),
% 15.46/2.48    inference(cnf_transformation,[],[f34])).
% 15.46/2.48  
% 15.46/2.48  cnf(c_2,plain,
% 15.46/2.48      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 15.46/2.48      inference(cnf_transformation,[],[f67]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27207,plain,
% 15.46/2.48      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_23,negated_conjecture,
% 15.46/2.48      ( v1_relat_1(sK6) ),
% 15.46/2.48      inference(cnf_transformation,[],[f56]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27193,plain,
% 15.46/2.48      ( v1_relat_1(sK6) = iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_4,plain,
% 15.46/2.48      ( ~ v1_relat_1(X0)
% 15.46/2.48      | k9_relat_1(X0,k2_tarski(X1,X1)) = k11_relat_1(X0,X1) ),
% 15.46/2.48      inference(cnf_transformation,[],[f64]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27205,plain,
% 15.46/2.48      ( k9_relat_1(X0,k2_tarski(X1,X1)) = k11_relat_1(X0,X1)
% 15.46/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27649,plain,
% 15.46/2.48      ( k9_relat_1(sK6,k2_tarski(X0,X0)) = k11_relat_1(sK6,X0) ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_27193,c_27205]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_13,plain,
% 15.46/2.48      ( ~ r2_hidden(X0,X1)
% 15.46/2.48      | ~ r2_hidden(X0,k1_relat_1(X2))
% 15.46/2.48      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 15.46/2.48      | ~ v1_funct_1(X2)
% 15.46/2.48      | ~ v1_relat_1(X2) ),
% 15.46/2.48      inference(cnf_transformation,[],[f70]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27199,plain,
% 15.46/2.48      ( r2_hidden(X0,X1) != iProver_top
% 15.46/2.48      | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
% 15.46/2.48      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 15.46/2.48      | v1_funct_1(X2) != iProver_top
% 15.46/2.48      | v1_relat_1(X2) != iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_29490,plain,
% 15.46/2.48      ( r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top
% 15.46/2.48      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 15.46/2.48      | r2_hidden(k1_funct_1(sK6,X0),k11_relat_1(sK6,X1)) = iProver_top
% 15.46/2.48      | v1_funct_1(sK6) != iProver_top
% 15.46/2.48      | v1_relat_1(sK6) != iProver_top ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_27649,c_27199]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_24,plain,
% 15.46/2.48      ( v1_relat_1(sK6) = iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_22,negated_conjecture,
% 15.46/2.48      ( v1_funct_1(sK6) ),
% 15.46/2.48      inference(cnf_transformation,[],[f57]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_25,plain,
% 15.46/2.48      ( v1_funct_1(sK6) = iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_30251,plain,
% 15.46/2.48      ( r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top
% 15.46/2.48      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 15.46/2.48      | r2_hidden(k1_funct_1(sK6,X0),k11_relat_1(sK6,X1)) = iProver_top ),
% 15.46/2.48      inference(global_propositional_subsumption,
% 15.46/2.48                [status(thm)],
% 15.46/2.48                [c_29490,c_24,c_25]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_30261,plain,
% 15.46/2.48      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 15.46/2.48      | r2_hidden(k1_funct_1(sK6,X0),k11_relat_1(sK6,X0)) = iProver_top ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_27207,c_30251]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_1,plain,
% 15.46/2.48      ( r2_hidden(sK0(X0,X1),X1)
% 15.46/2.48      | sK0(X0,X1) = X0
% 15.46/2.48      | k2_tarski(X0,X0) = X1 ),
% 15.46/2.48      inference(cnf_transformation,[],[f61]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27208,plain,
% 15.46/2.48      ( sK0(X0,X1) = X0
% 15.46/2.48      | k2_tarski(X0,X0) = X1
% 15.46/2.48      | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_7,plain,
% 15.46/2.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 15.46/2.48      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 15.46/2.48      | ~ v1_relat_1(X1) ),
% 15.46/2.48      inference(cnf_transformation,[],[f42]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27202,plain,
% 15.46/2.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 15.46/2.48      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 15.46/2.48      | v1_relat_1(X1) != iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_18,plain,
% 15.46/2.48      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 15.46/2.48      | ~ v1_funct_1(X2)
% 15.46/2.48      | ~ v1_relat_1(X2)
% 15.46/2.48      | k1_funct_1(X2,X0) = X1 ),
% 15.46/2.48      inference(cnf_transformation,[],[f54]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27196,plain,
% 15.46/2.48      ( k1_funct_1(X0,X1) = X2
% 15.46/2.48      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 15.46/2.48      | v1_funct_1(X0) != iProver_top
% 15.46/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_28062,plain,
% 15.46/2.48      ( k1_funct_1(X0,sK1(X1,X2,X0)) = X1
% 15.46/2.48      | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
% 15.46/2.48      | v1_funct_1(X0) != iProver_top
% 15.46/2.48      | v1_relat_1(X0) != iProver_top ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_27202,c_27196]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_35820,plain,
% 15.46/2.48      ( k1_funct_1(sK6,sK1(X0,k2_tarski(X1,X1),sK6)) = X0
% 15.46/2.48      | r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
% 15.46/2.48      | v1_funct_1(sK6) != iProver_top
% 15.46/2.48      | v1_relat_1(sK6) != iProver_top ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_27649,c_28062]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_36593,plain,
% 15.46/2.48      ( k1_funct_1(sK6,sK1(X0,k2_tarski(X1,X1),sK6)) = X0
% 15.46/2.48      | r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top ),
% 15.46/2.48      inference(global_propositional_subsumption,
% 15.46/2.48                [status(thm)],
% 15.46/2.48                [c_35820,c_24,c_25]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_36601,plain,
% 15.46/2.48      ( k1_funct_1(sK6,sK1(sK0(X0,k11_relat_1(sK6,X1)),k2_tarski(X1,X1),sK6)) = sK0(X0,k11_relat_1(sK6,X1))
% 15.46/2.48      | sK0(X0,k11_relat_1(sK6,X1)) = X0
% 15.46/2.48      | k2_tarski(X0,X0) = k11_relat_1(sK6,X1) ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_27208,c_36593]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_20,negated_conjecture,
% 15.46/2.48      ( k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k11_relat_1(sK6,sK5) ),
% 15.46/2.48      inference(cnf_transformation,[],[f65]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_43745,plain,
% 15.46/2.48      ( k1_funct_1(sK6,sK1(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,X0)),k2_tarski(X0,X0),sK6)) = sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,X0))
% 15.46/2.48      | k11_relat_1(sK6,X0) != k11_relat_1(sK6,sK5)
% 15.46/2.48      | sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,X0)) = k1_funct_1(sK6,sK5) ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_36601,c_20]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_45718,plain,
% 15.46/2.48      ( k1_funct_1(sK6,sK1(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k2_tarski(sK5,sK5),sK6)) = sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5))
% 15.46/2.48      | sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
% 15.46/2.48      inference(equality_resolution,[status(thm)],[c_43745]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_6,plain,
% 15.46/2.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 15.46/2.48      | r2_hidden(sK1(X0,X2,X1),X2)
% 15.46/2.48      | ~ v1_relat_1(X1) ),
% 15.46/2.48      inference(cnf_transformation,[],[f43]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27203,plain,
% 15.46/2.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 15.46/2.48      | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
% 15.46/2.48      | v1_relat_1(X1) != iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_3,plain,
% 15.46/2.48      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 15.46/2.48      inference(cnf_transformation,[],[f68]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27206,plain,
% 15.46/2.48      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 15.46/2.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27914,plain,
% 15.46/2.48      ( sK1(X0,k2_tarski(X1,X1),X2) = X1
% 15.46/2.48      | r2_hidden(X0,k9_relat_1(X2,k2_tarski(X1,X1))) != iProver_top
% 15.46/2.48      | v1_relat_1(X2) != iProver_top ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_27203,c_27206]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_28331,plain,
% 15.46/2.48      ( sK1(X0,k2_tarski(X1,X1),sK6) = X1
% 15.46/2.48      | r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
% 15.46/2.48      | v1_relat_1(sK6) != iProver_top ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_27649,c_27914]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_28375,plain,
% 15.46/2.48      ( r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top
% 15.46/2.48      | sK1(X0,k2_tarski(X1,X1),sK6) = X1 ),
% 15.46/2.48      inference(global_propositional_subsumption,
% 15.46/2.48                [status(thm)],
% 15.46/2.48                [c_28331,c_24]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_28376,plain,
% 15.46/2.48      ( sK1(X0,k2_tarski(X1,X1),sK6) = X1
% 15.46/2.48      | r2_hidden(X0,k11_relat_1(sK6,X1)) != iProver_top ),
% 15.46/2.48      inference(renaming,[status(thm)],[c_28375]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_28383,plain,
% 15.46/2.48      ( sK1(sK0(X0,k11_relat_1(sK6,X1)),k2_tarski(X1,X1),sK6) = X1
% 15.46/2.48      | sK0(X0,k11_relat_1(sK6,X1)) = X0
% 15.46/2.48      | k2_tarski(X0,X0) = k11_relat_1(sK6,X1) ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_27208,c_28376]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_28821,plain,
% 15.46/2.48      ( sK1(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,X0)),k2_tarski(X0,X0),sK6) = X0
% 15.46/2.48      | k11_relat_1(sK6,X0) != k11_relat_1(sK6,sK5)
% 15.46/2.48      | sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,X0)) = k1_funct_1(sK6,sK5) ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_28383,c_20]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_28993,plain,
% 15.46/2.48      ( sK1(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k2_tarski(sK5,sK5),sK6) = sK5
% 15.46/2.48      | sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
% 15.46/2.48      inference(equality_resolution,[status(thm)],[c_28821]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_43679,plain,
% 15.46/2.48      ( sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) = k1_funct_1(sK6,sK5)
% 15.46/2.48      | k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k11_relat_1(sK6,sK5) ),
% 15.46/2.48      inference(superposition,[status(thm)],[c_28993,c_36601]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_46329,plain,
% 15.46/2.48      ( sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
% 15.46/2.48      inference(global_propositional_subsumption,
% 15.46/2.48                [status(thm)],
% 15.46/2.48                [c_45718,c_20,c_43679]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_0,plain,
% 15.46/2.48      ( ~ r2_hidden(sK0(X0,X1),X1)
% 15.46/2.48      | sK0(X0,X1) != X0
% 15.46/2.48      | k2_tarski(X0,X0) = X1 ),
% 15.46/2.48      inference(cnf_transformation,[],[f60]) ).
% 15.46/2.48  
% 15.46/2.48  cnf(c_27209,plain,
% 15.46/2.48      ( sK0(X0,X1) != X0
% 15.46/2.48      | k2_tarski(X0,X0) = X1
% 15.46/2.49      | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
% 15.46/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_46345,plain,
% 15.46/2.49      ( k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k11_relat_1(sK6,sK5)
% 15.46/2.49      | r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5)) != iProver_top ),
% 15.46/2.49      inference(superposition,[status(thm)],[c_46329,c_27209]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_46365,plain,
% 15.46/2.49      ( k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k11_relat_1(sK6,sK5)
% 15.46/2.49      | r2_hidden(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top ),
% 15.46/2.49      inference(light_normalisation,[status(thm)],[c_46345,c_46329]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_27393,plain,
% 15.46/2.49      ( ~ r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5))
% 15.46/2.49      | sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
% 15.46/2.49      | k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k11_relat_1(sK6,sK5) ),
% 15.46/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_27394,plain,
% 15.46/2.49      ( sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
% 15.46/2.49      | k2_tarski(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k11_relat_1(sK6,sK5)
% 15.46/2.49      | r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5)) != iProver_top ),
% 15.46/2.49      inference(predicate_to_equality,[status(thm)],[c_27393]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_220,plain,
% 15.46/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.46/2.49      theory(equality) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_217,plain,( X0 = X0 ),theory(equality) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_29329,plain,
% 15.46/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 15.46/2.49      inference(resolution,[status(thm)],[c_220,c_217]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_27793,plain,
% 15.46/2.49      ( r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5))
% 15.46/2.49      | sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
% 15.46/2.49      inference(resolution,[status(thm)],[c_1,c_20]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_31959,plain,
% 15.46/2.49      ( ~ r2_hidden(k1_funct_1(sK6,sK5),X0)
% 15.46/2.49      | r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),X0)
% 15.46/2.49      | r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5)) ),
% 15.46/2.49      inference(resolution,[status(thm)],[c_29329,c_27793]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_32237,plain,
% 15.46/2.49      ( ~ r2_hidden(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5))
% 15.46/2.49      | r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5)) ),
% 15.46/2.49      inference(factoring,[status(thm)],[c_31959]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_32238,plain,
% 15.46/2.49      ( r2_hidden(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top
% 15.46/2.49      | r2_hidden(sK0(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)),k11_relat_1(sK6,sK5)) = iProver_top ),
% 15.46/2.49      inference(predicate_to_equality,[status(thm)],[c_32237]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_54618,plain,
% 15.46/2.49      ( r2_hidden(k1_funct_1(sK6,sK5),k11_relat_1(sK6,sK5)) != iProver_top ),
% 15.46/2.49      inference(global_propositional_subsumption,
% 15.46/2.49                [status(thm)],
% 15.46/2.49                [c_46365,c_20,c_27394,c_32238,c_43679]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_54626,plain,
% 15.46/2.49      ( r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top ),
% 15.46/2.49      inference(superposition,[status(thm)],[c_30261,c_54618]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_21,negated_conjecture,
% 15.46/2.49      ( r2_hidden(sK5,k1_relat_1(sK6)) ),
% 15.46/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(c_26,plain,
% 15.46/2.49      ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
% 15.46/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.46/2.49  
% 15.46/2.49  cnf(contradiction,plain,
% 15.46/2.49      ( $false ),
% 15.46/2.49      inference(minisat,[status(thm)],[c_54626,c_26]) ).
% 15.46/2.49  
% 15.46/2.49  
% 15.46/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.46/2.49  
% 15.46/2.49  ------                               Statistics
% 15.46/2.49  
% 15.46/2.49  ------ Selected
% 15.46/2.49  
% 15.46/2.49  total_time:                             1.499
% 15.46/2.49  
%------------------------------------------------------------------------------
