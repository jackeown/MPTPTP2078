%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0622+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:44 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 323 expanded)
%              Number of clauses        :   52 (  78 expanded)
%              Number of leaves         :   15 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          :  433 (2225 expanded)
%              Number of equality atoms :  233 (1156 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k1_tarski(X0) = k2_relat_1(X2)
              & k1_tarski(X0) = k2_relat_1(X1)
              & k1_relat_1(X1) = k1_relat_1(X2) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k1_tarski(X0) = k2_relat_1(X2)
                & k1_tarski(X0) = k2_relat_1(X1)
                & k1_relat_1(X1) = k1_relat_1(X2) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( sK7 != X1
        & k1_tarski(X0) = k2_relat_1(sK7)
        & k1_tarski(X0) = k2_relat_1(X1)
        & k1_relat_1(sK7) = k1_relat_1(X1)
        & v1_funct_1(sK7)
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k1_tarski(X0) = k2_relat_1(X2)
            & k1_tarski(X0) = k2_relat_1(X1)
            & k1_relat_1(X1) = k1_relat_1(X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( sK6 != X2
          & k1_tarski(sK5) = k2_relat_1(X2)
          & k1_tarski(sK5) = k2_relat_1(sK6)
          & k1_relat_1(sK6) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( sK6 != sK7
    & k1_tarski(sK5) = k2_relat_1(sK7)
    & k1_tarski(sK5) = k2_relat_1(sK6)
    & k1_relat_1(sK6) = k1_relat_1(sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f11,f25,f24])).

fof(f43,plain,(
    k1_relat_1(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    sK6 != sK7 ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f28])).

fof(f48,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f47])).

fof(f44,plain,(
    k1_tarski(sK5) = k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f20,f19,f18])).

fof(f33,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f51,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    k1_tarski(sK5) = k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_185,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_668,plain,
    ( k1_funct_1(sK7,sK4(sK7,sK6)) != X0
    | k1_funct_1(sK6,sK4(sK7,sK6)) != X0
    | k1_funct_1(sK6,sK4(sK7,sK6)) = k1_funct_1(sK7,sK4(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_5981,plain,
    ( k1_funct_1(sK7,sK4(sK7,sK6)) != sK5
    | k1_funct_1(sK6,sK4(sK7,sK6)) = k1_funct_1(sK7,sK4(sK7,sK6))
    | k1_funct_1(sK6,sK4(sK7,sK6)) != sK5 ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_15,negated_conjecture,
    ( k1_relat_1(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_11,plain,
    ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_471,plain,
    ( X0 = X1
    | k1_relat_1(X0) != k1_relat_1(X1)
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_956,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK6)
    | sK7 = X0
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_471])).

cnf(c_965,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK6)
    | sK7 = X0
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_956,c_15])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_22,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_23,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1561,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != k1_relat_1(sK6)
    | sK7 = X0
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_965,c_22,c_23])).

cnf(c_1562,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK6)
    | sK7 = X0
    | r2_hidden(sK4(sK7,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1561])).

cnf(c_1573,plain,
    ( sK7 = sK6
    | r2_hidden(sK4(sK7,sK6),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1562])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_21,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,negated_conjecture,
    ( sK6 != sK7 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_49,plain,
    ( ~ r2_hidden(sK6,k1_tarski(sK6))
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_52,plain,
    ( r2_hidden(sK6,k1_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_190,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_197,plain,
    ( k1_relat_1(sK6) = k1_relat_1(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_641,plain,
    ( sK7 != X0
    | sK6 != X0
    | sK6 = sK7 ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_642,plain,
    ( sK7 != sK6
    | sK6 = sK7
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_991,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK6)
    | sK7 = sK6
    | r2_hidden(sK4(sK7,sK6),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_1622,plain,
    ( r2_hidden(sK4(sK7,sK6),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1573,c_20,c_21,c_22,c_23,c_12,c_49,c_52,c_197,c_642,c_991])).

cnf(c_14,negated_conjecture,
    ( k1_tarski(sK5) = k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_475,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2280,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k1_tarski(sK5)) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_475])).

cnf(c_2419,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k1_tarski(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2280,c_20,c_21])).

cnf(c_479,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2427,plain,
    ( k1_funct_1(sK6,X0) = sK5
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2419,c_479])).

cnf(c_2679,plain,
    ( k1_funct_1(sK6,sK4(sK7,sK6)) = sK5 ),
    inference(superposition,[status(thm)],[c_1622,c_2427])).

cnf(c_773,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK4(sK7,sK6)),k1_tarski(X0))
    | k1_funct_1(sK7,sK4(sK7,sK6)) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2247,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK4(sK7,sK6)),k1_tarski(sK5))
    | k1_funct_1(sK7,sK4(sK7,sK6)) = sK5 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_184,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1203,plain,
    ( k1_funct_1(sK7,sK4(sK7,sK6)) = k1_funct_1(sK7,sK4(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_187,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_753,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k1_funct_1(sK7,sK4(sK7,sK6)),k2_relat_1(sK7))
    | X0 != k1_funct_1(sK7,sK4(sK7,sK6))
    | X1 != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_940,plain,
    ( r2_hidden(X0,k1_tarski(sK5))
    | ~ r2_hidden(k1_funct_1(sK7,sK4(sK7,sK6)),k2_relat_1(sK7))
    | X0 != k1_funct_1(sK7,sK4(sK7,sK6))
    | k1_tarski(sK5) != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_1202,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK4(sK7,sK6)),k2_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,sK4(sK7,sK6)),k1_tarski(sK5))
    | k1_funct_1(sK7,sK4(sK7,sK6)) != k1_funct_1(sK7,sK4(sK7,sK6))
    | k1_tarski(sK5) != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_660,plain,
    ( ~ r2_hidden(sK4(sK7,sK6),k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,sK4(sK7,sK6)),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0
    | k1_funct_1(X1,sK4(X0,X1)) != k1_funct_1(X0,sK4(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_653,plain,
    ( ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | k1_funct_1(sK6,sK4(sK7,sK6)) != k1_funct_1(sK7,sK4(sK7,sK6))
    | k1_relat_1(sK6) != k1_relat_1(sK7)
    | sK6 = sK7 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_650,plain,
    ( r2_hidden(sK4(sK7,sK6),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | k1_relat_1(sK6) != k1_relat_1(sK7)
    | sK6 = sK7 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_13,negated_conjecture,
    ( k1_tarski(sK5) = k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5981,c_2679,c_2247,c_1203,c_1202,c_660,c_653,c_650,c_12,c_13,c_15,c_16,c_17,c_18,c_19])).


%------------------------------------------------------------------------------
