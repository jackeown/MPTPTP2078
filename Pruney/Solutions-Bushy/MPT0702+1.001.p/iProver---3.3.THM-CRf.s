%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0702+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:56 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 309 expanded)
%              Number of clauses        :   61 (  79 expanded)
%              Number of leaves         :   12 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  494 (1864 expanded)
%              Number of equality atoms :  108 ( 261 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f25])).

fof(f40,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK6,sK7)
      & v2_funct_1(sK8)
      & r1_tarski(sK6,k1_relat_1(sK8))
      & r1_tarski(k9_relat_1(sK8,sK6),k9_relat_1(sK8,sK7))
      & v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(sK6,sK7)
    & v2_funct_1(sK8)
    & r1_tarski(sK6,k1_relat_1(sK8))
    & r1_tarski(k9_relat_1(sK8,sK6),k9_relat_1(sK8,sK7))
    & v1_funct_1(sK8)
    & v1_relat_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f12,f27])).

fof(f46,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    v2_funct_1(sK8) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
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

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
        & r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) = X3
        & r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).

fof(f30,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f29,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f31,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f32,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f52,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ~ r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    r1_tarski(sK6,k1_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    r1_tarski(k9_relat_1(sK8,sK6),k9_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_918,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1258,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3(sK6,sK7),sK7)
    | sK3(sK6,sK7) != X0
    | sK7 != X1 ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_1337,plain,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(sK3(sK6,sK7),sK7)
    | sK3(sK6,sK7) != X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_5957,plain,
    ( ~ r2_hidden(sK2(sK8,sK7,k1_funct_1(sK8,sK3(sK6,sK7))),sK7)
    | r2_hidden(sK3(sK6,sK7),sK7)
    | sK3(sK6,sK7) != sK2(sK8,sK7,k1_funct_1(sK8,sK3(sK6,sK7)))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_608,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_609,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | ~ v2_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | X1 = X0
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,X1) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK8) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_433,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_434,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_funct_1(sK8)
    | X1 = X0
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,X1) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_438,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | X1 = X0
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_21,c_20])).

cnf(c_611,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | X1 = X0
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_21,c_20,c_434])).

cnf(c_1694,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(sK3(sK6,sK7),k1_relat_1(sK8))
    | sK3(sK6,sK7) = X0
    | k1_funct_1(sK8,X0) != k1_funct_1(sK8,sK3(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_5889,plain,
    ( ~ r2_hidden(sK2(sK8,sK7,k1_funct_1(sK8,sK3(sK6,sK7))),k1_relat_1(sK8))
    | ~ r2_hidden(sK3(sK6,sK7),k1_relat_1(sK8))
    | sK3(sK6,sK7) = sK2(sK8,sK7,k1_funct_1(sK8,sK3(sK6,sK7)))
    | k1_funct_1(sK8,sK2(sK8,sK7,k1_funct_1(sK8,sK3(sK6,sK7)))) != k1_funct_1(sK8,sK3(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_646,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_647,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),X1)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_651,plain,
    ( r2_hidden(sK2(sK8,X1,X0),X1)
    | ~ r2_hidden(X0,k9_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_21])).

cnf(c_652,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),X1) ),
    inference(renaming,[status(thm)],[c_651])).

cnf(c_2214,plain,
    ( r2_hidden(sK2(sK8,X0,k1_funct_1(sK8,sK3(sK6,sK7))),X0)
    | ~ r2_hidden(k1_funct_1(sK8,sK3(sK6,sK7)),k9_relat_1(sK8,X0)) ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_3131,plain,
    ( r2_hidden(sK2(sK8,sK7,k1_funct_1(sK8,sK3(sK6,sK7))),sK7)
    | ~ r2_hidden(k1_funct_1(sK8,sK3(sK6,sK7)),k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_628,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_629,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),k1_relat_1(sK8))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_633,plain,
    ( r2_hidden(sK2(sK8,X1,X0),k1_relat_1(sK8))
    | ~ r2_hidden(X0,k9_relat_1(sK8,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_21])).

cnf(c_634,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | r2_hidden(sK2(sK8,X1,X0),k1_relat_1(sK8)) ),
    inference(renaming,[status(thm)],[c_633])).

cnf(c_2215,plain,
    ( r2_hidden(sK2(sK8,X0,k1_funct_1(sK8,sK3(sK6,sK7))),k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,sK3(sK6,sK7)),k9_relat_1(sK8,X0)) ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_3037,plain,
    ( r2_hidden(sK2(sK8,sK7,k1_funct_1(sK8,sK3(sK6,sK7))),k1_relat_1(sK8))
    | ~ r2_hidden(k1_funct_1(sK8,sK3(sK6,sK7)),k9_relat_1(sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_2215])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_664,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_665,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,sK2(sK8,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_669,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK8,X1))
    | k1_funct_1(sK8,sK2(sK8,X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_21])).

cnf(c_2213,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK3(sK6,sK7)),k9_relat_1(sK8,X0))
    | k1_funct_1(sK8,sK2(sK8,X0,k1_funct_1(sK8,sK3(sK6,sK7)))) = k1_funct_1(sK8,sK3(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_3029,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK3(sK6,sK7)),k9_relat_1(sK8,sK7))
    | k1_funct_1(sK8,sK2(sK8,sK7,k1_funct_1(sK8,sK3(sK6,sK7)))) = k1_funct_1(sK8,sK3(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1724,plain,
    ( ~ r1_tarski(k9_relat_1(sK8,sK6),X0)
    | r2_hidden(k1_funct_1(sK8,sK3(sK6,sK7)),X0)
    | ~ r2_hidden(k1_funct_1(sK8,sK3(sK6,sK7)),k9_relat_1(sK8,sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2515,plain,
    ( ~ r1_tarski(k9_relat_1(sK8,sK6),k9_relat_1(sK8,sK7))
    | r2_hidden(k1_funct_1(sK8,sK3(sK6,sK7)),k9_relat_1(sK8,sK7))
    | ~ r2_hidden(k1_funct_1(sK8,sK3(sK6,sK7)),k9_relat_1(sK8,sK6)) ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_560,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_561,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_565,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_561,c_21])).

cnf(c_566,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) ),
    inference(renaming,[status(thm)],[c_565])).

cnf(c_1389,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),X0)
    | ~ r2_hidden(sK3(sK6,sK7),k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,sK3(sK6,sK7)),k9_relat_1(sK8,X0)) ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_1472,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),k1_relat_1(sK8))
    | ~ r2_hidden(sK3(sK6,sK7),sK6)
    | r2_hidden(k1_funct_1(sK8,sK3(sK6,sK7)),k9_relat_1(sK8,sK6)) ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_913,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1330,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_1237,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,k1_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1274,plain,
    ( ~ r1_tarski(sK6,k1_relat_1(sK8))
    | r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_1300,plain,
    ( ~ r1_tarski(sK6,k1_relat_1(sK8))
    | r2_hidden(sK3(sK6,sK7),k1_relat_1(sK8))
    | ~ r2_hidden(sK3(sK6,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_264,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_265,plain,
    ( ~ r2_hidden(sK3(sK6,sK7),sK7) ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_257,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_258,plain,
    ( r2_hidden(sK3(sK6,sK7),sK6) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK6,k1_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK8,sK6),k9_relat_1(sK8,sK7)) ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5957,c_5889,c_3131,c_3037,c_3029,c_2515,c_1472,c_1330,c_1300,c_265,c_258,c_18,c_19])).


%------------------------------------------------------------------------------
