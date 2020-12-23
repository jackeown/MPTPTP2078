%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:13 EST 2020

% Result     : Theorem 27.15s
% Output     : CNFRefutation 27.15s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 423 expanded)
%              Number of clauses        :   38 (  90 expanded)
%              Number of leaves         :   10 ( 117 expanded)
%              Depth                    :   21
%              Number of atoms          :  379 (2702 expanded)
%              Number of equality atoms :  196 (1289 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k2_relat_1(X0) = k1_relat_1(X1) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k6_relat_1(k1_relat_1(sK5)) != sK5
        & k5_relat_1(X0,sK5) = X0
        & k2_relat_1(X0) = k1_relat_1(sK5)
        & v1_funct_1(sK5)
        & v1_relat_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X1)) != X1
            & k5_relat_1(X0,X1) = X0
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(sK4,X1) = sK4
          & k2_relat_1(sK4) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k6_relat_1(k1_relat_1(sK5)) != sK5
    & k5_relat_1(sK4,sK5) = sK4
    & k2_relat_1(sK4) = k1_relat_1(sK5)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f13,f26,f25])).

fof(f41,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    k2_relat_1(sK4) = k1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1)
            & r2_hidden(sK3(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f37])).

fof(f42,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    k6_relat_1(k1_relat_1(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

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

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).

fof(f28,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f39,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    k5_relat_1(sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) != sK3(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f38])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_398,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,negated_conjecture,
    ( k2_relat_1(sK4) = k1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( r2_hidden(sK3(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_402,plain,
    ( k6_relat_1(k1_relat_1(X0)) = X0
    | r2_hidden(sK3(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_799,plain,
    ( k6_relat_1(k1_relat_1(sK5)) = sK5
    | r2_hidden(sK3(k2_relat_1(sK4),sK5),k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_402])).

cnf(c_818,plain,
    ( k6_relat_1(k2_relat_1(sK4)) = sK5
    | r2_hidden(sK3(k2_relat_1(sK4),sK5),k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_799,c_13])).

cnf(c_20,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,negated_conjecture,
    ( k6_relat_1(k1_relat_1(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_423,plain,
    ( k6_relat_1(k2_relat_1(sK4)) != sK5 ),
    inference(light_normalisation,[status(thm)],[c_11,c_13])).

cnf(c_1067,plain,
    ( r2_hidden(sK3(k2_relat_1(sK4),sK5),k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_818,c_20,c_21,c_423])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_405,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_404,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1287,plain,
    ( k1_funct_1(X0,k1_funct_1(X1,sK2(X1,X2))) = k1_funct_1(k5_relat_1(X1,X0),sK2(X1,X2))
    | r2_hidden(X2,k2_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_405,c_404])).

cnf(c_4659,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1067,c_1287])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_406,plain,
    ( k1_funct_1(X0,sK2(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1073,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = sK3(k2_relat_1(sK4),sK5)
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1067,c_406])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2225,plain,
    ( k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = sK3(k2_relat_1(sK4),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1073,c_18,c_19])).

cnf(c_4723,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,sK3(k2_relat_1(sK4),sK5))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4659,c_2225])).

cnf(c_112600,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,sK3(k2_relat_1(sK4),sK5))
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4723,c_18,c_19])).

cnf(c_112601,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,sK3(k2_relat_1(sK4),sK5))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_112600])).

cnf(c_112609,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5))
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_398,c_112601])).

cnf(c_12,negated_conjecture,
    ( k5_relat_1(sK4,sK5) = sK4 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_112617,plain,
    ( k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) = sK3(k2_relat_1(sK4),sK5)
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_112609,c_12,c_2225])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(X0,sK3(k1_relat_1(X0),X0)) != sK3(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_403,plain,
    ( k1_funct_1(X0,sK3(k1_relat_1(X0),X0)) != sK3(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_969,plain,
    ( k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) != sK3(k1_relat_1(sK5),sK5)
    | k6_relat_1(k1_relat_1(sK5)) = sK5
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_403])).

cnf(c_970,plain,
    ( k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) != sK3(k2_relat_1(sK4),sK5)
    | k6_relat_1(k2_relat_1(sK4)) = sK5
    | v1_relat_1(sK5) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_969,c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_112617,c_970,c_423,c_21,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:53:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 27.15/4.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.15/4.01  
% 27.15/4.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.15/4.01  
% 27.15/4.01  ------  iProver source info
% 27.15/4.01  
% 27.15/4.01  git: date: 2020-06-30 10:37:57 +0100
% 27.15/4.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.15/4.01  git: non_committed_changes: false
% 27.15/4.01  git: last_make_outside_of_git: false
% 27.15/4.01  
% 27.15/4.01  ------ 
% 27.15/4.01  
% 27.15/4.01  ------ Input Options
% 27.15/4.01  
% 27.15/4.01  --out_options                           all
% 27.15/4.01  --tptp_safe_out                         true
% 27.15/4.01  --problem_path                          ""
% 27.15/4.01  --include_path                          ""
% 27.15/4.01  --clausifier                            res/vclausify_rel
% 27.15/4.01  --clausifier_options                    --mode clausify
% 27.15/4.01  --stdin                                 false
% 27.15/4.01  --stats_out                             sel
% 27.15/4.01  
% 27.15/4.01  ------ General Options
% 27.15/4.01  
% 27.15/4.01  --fof                                   false
% 27.15/4.01  --time_out_real                         604.99
% 27.15/4.01  --time_out_virtual                      -1.
% 27.15/4.01  --symbol_type_check                     false
% 27.15/4.01  --clausify_out                          false
% 27.15/4.01  --sig_cnt_out                           false
% 27.15/4.01  --trig_cnt_out                          false
% 27.15/4.01  --trig_cnt_out_tolerance                1.
% 27.15/4.01  --trig_cnt_out_sk_spl                   false
% 27.15/4.01  --abstr_cl_out                          false
% 27.15/4.01  
% 27.15/4.01  ------ Global Options
% 27.15/4.01  
% 27.15/4.01  --schedule                              none
% 27.15/4.01  --add_important_lit                     false
% 27.15/4.01  --prop_solver_per_cl                    1000
% 27.15/4.01  --min_unsat_core                        false
% 27.15/4.01  --soft_assumptions                      false
% 27.15/4.01  --soft_lemma_size                       3
% 27.15/4.01  --prop_impl_unit_size                   0
% 27.15/4.01  --prop_impl_unit                        []
% 27.15/4.01  --share_sel_clauses                     true
% 27.15/4.01  --reset_solvers                         false
% 27.15/4.01  --bc_imp_inh                            [conj_cone]
% 27.15/4.01  --conj_cone_tolerance                   3.
% 27.15/4.01  --extra_neg_conj                        none
% 27.15/4.01  --large_theory_mode                     true
% 27.15/4.01  --prolific_symb_bound                   200
% 27.15/4.01  --lt_threshold                          2000
% 27.15/4.01  --clause_weak_htbl                      true
% 27.15/4.01  --gc_record_bc_elim                     false
% 27.15/4.01  
% 27.15/4.01  ------ Preprocessing Options
% 27.15/4.01  
% 27.15/4.01  --preprocessing_flag                    true
% 27.15/4.01  --time_out_prep_mult                    0.1
% 27.15/4.01  --splitting_mode                        input
% 27.15/4.01  --splitting_grd                         true
% 27.15/4.01  --splitting_cvd                         false
% 27.15/4.01  --splitting_cvd_svl                     false
% 27.15/4.01  --splitting_nvd                         32
% 27.15/4.01  --sub_typing                            true
% 27.15/4.01  --prep_gs_sim                           false
% 27.15/4.01  --prep_unflatten                        true
% 27.15/4.01  --prep_res_sim                          true
% 27.15/4.01  --prep_upred                            true
% 27.15/4.01  --prep_sem_filter                       exhaustive
% 27.15/4.01  --prep_sem_filter_out                   false
% 27.15/4.01  --pred_elim                             false
% 27.15/4.01  --res_sim_input                         true
% 27.15/4.01  --eq_ax_congr_red                       true
% 27.15/4.01  --pure_diseq_elim                       true
% 27.15/4.01  --brand_transform                       false
% 27.15/4.01  --non_eq_to_eq                          false
% 27.15/4.01  --prep_def_merge                        true
% 27.15/4.01  --prep_def_merge_prop_impl              false
% 27.15/4.01  --prep_def_merge_mbd                    true
% 27.15/4.01  --prep_def_merge_tr_red                 false
% 27.15/4.01  --prep_def_merge_tr_cl                  false
% 27.15/4.01  --smt_preprocessing                     true
% 27.15/4.01  --smt_ac_axioms                         fast
% 27.15/4.01  --preprocessed_out                      false
% 27.15/4.01  --preprocessed_stats                    false
% 27.15/4.01  
% 27.15/4.01  ------ Abstraction refinement Options
% 27.15/4.01  
% 27.15/4.01  --abstr_ref                             []
% 27.15/4.01  --abstr_ref_prep                        false
% 27.15/4.01  --abstr_ref_until_sat                   false
% 27.15/4.01  --abstr_ref_sig_restrict                funpre
% 27.15/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 27.15/4.01  --abstr_ref_under                       []
% 27.15/4.01  
% 27.15/4.01  ------ SAT Options
% 27.15/4.01  
% 27.15/4.01  --sat_mode                              false
% 27.15/4.01  --sat_fm_restart_options                ""
% 27.15/4.01  --sat_gr_def                            false
% 27.15/4.01  --sat_epr_types                         true
% 27.15/4.01  --sat_non_cyclic_types                  false
% 27.15/4.01  --sat_finite_models                     false
% 27.15/4.01  --sat_fm_lemmas                         false
% 27.15/4.01  --sat_fm_prep                           false
% 27.15/4.01  --sat_fm_uc_incr                        true
% 27.15/4.01  --sat_out_model                         small
% 27.15/4.01  --sat_out_clauses                       false
% 27.15/4.01  
% 27.15/4.01  ------ QBF Options
% 27.15/4.01  
% 27.15/4.01  --qbf_mode                              false
% 27.15/4.01  --qbf_elim_univ                         false
% 27.15/4.01  --qbf_dom_inst                          none
% 27.15/4.01  --qbf_dom_pre_inst                      false
% 27.15/4.01  --qbf_sk_in                             false
% 27.15/4.01  --qbf_pred_elim                         true
% 27.15/4.01  --qbf_split                             512
% 27.15/4.01  
% 27.15/4.01  ------ BMC1 Options
% 27.15/4.01  
% 27.15/4.01  --bmc1_incremental                      false
% 27.15/4.01  --bmc1_axioms                           reachable_all
% 27.15/4.01  --bmc1_min_bound                        0
% 27.15/4.01  --bmc1_max_bound                        -1
% 27.15/4.01  --bmc1_max_bound_default                -1
% 27.15/4.01  --bmc1_symbol_reachability              true
% 27.15/4.01  --bmc1_property_lemmas                  false
% 27.15/4.01  --bmc1_k_induction                      false
% 27.15/4.01  --bmc1_non_equiv_states                 false
% 27.15/4.01  --bmc1_deadlock                         false
% 27.15/4.01  --bmc1_ucm                              false
% 27.15/4.01  --bmc1_add_unsat_core                   none
% 27.15/4.01  --bmc1_unsat_core_children              false
% 27.15/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 27.15/4.01  --bmc1_out_stat                         full
% 27.15/4.01  --bmc1_ground_init                      false
% 27.15/4.01  --bmc1_pre_inst_next_state              false
% 27.15/4.01  --bmc1_pre_inst_state                   false
% 27.15/4.01  --bmc1_pre_inst_reach_state             false
% 27.15/4.01  --bmc1_out_unsat_core                   false
% 27.15/4.01  --bmc1_aig_witness_out                  false
% 27.15/4.01  --bmc1_verbose                          false
% 27.15/4.01  --bmc1_dump_clauses_tptp                false
% 27.15/4.01  --bmc1_dump_unsat_core_tptp             false
% 27.15/4.01  --bmc1_dump_file                        -
% 27.15/4.01  --bmc1_ucm_expand_uc_limit              128
% 27.15/4.01  --bmc1_ucm_n_expand_iterations          6
% 27.15/4.01  --bmc1_ucm_extend_mode                  1
% 27.15/4.01  --bmc1_ucm_init_mode                    2
% 27.15/4.01  --bmc1_ucm_cone_mode                    none
% 27.15/4.01  --bmc1_ucm_reduced_relation_type        0
% 27.15/4.01  --bmc1_ucm_relax_model                  4
% 27.15/4.01  --bmc1_ucm_full_tr_after_sat            true
% 27.15/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 27.15/4.01  --bmc1_ucm_layered_model                none
% 27.15/4.01  --bmc1_ucm_max_lemma_size               10
% 27.15/4.01  
% 27.15/4.01  ------ AIG Options
% 27.15/4.01  
% 27.15/4.01  --aig_mode                              false
% 27.15/4.01  
% 27.15/4.01  ------ Instantiation Options
% 27.15/4.01  
% 27.15/4.01  --instantiation_flag                    true
% 27.15/4.01  --inst_sos_flag                         false
% 27.15/4.01  --inst_sos_phase                        true
% 27.15/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.15/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.15/4.01  --inst_lit_sel_side                     num_symb
% 27.15/4.01  --inst_solver_per_active                1400
% 27.15/4.01  --inst_solver_calls_frac                1.
% 27.15/4.01  --inst_passive_queue_type               priority_queues
% 27.15/4.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.15/4.01  --inst_passive_queues_freq              [25;2]
% 27.15/4.01  --inst_dismatching                      true
% 27.15/4.01  --inst_eager_unprocessed_to_passive     true
% 27.15/4.01  --inst_prop_sim_given                   true
% 27.15/4.01  --inst_prop_sim_new                     false
% 27.15/4.01  --inst_subs_new                         false
% 27.15/4.01  --inst_eq_res_simp                      false
% 27.15/4.01  --inst_subs_given                       false
% 27.15/4.01  --inst_orphan_elimination               true
% 27.15/4.01  --inst_learning_loop_flag               true
% 27.15/4.01  --inst_learning_start                   3000
% 27.15/4.01  --inst_learning_factor                  2
% 27.15/4.01  --inst_start_prop_sim_after_learn       3
% 27.15/4.01  --inst_sel_renew                        solver
% 27.15/4.01  --inst_lit_activity_flag                true
% 27.15/4.01  --inst_restr_to_given                   false
% 27.15/4.01  --inst_activity_threshold               500
% 27.15/4.01  --inst_out_proof                        true
% 27.15/4.01  
% 27.15/4.01  ------ Resolution Options
% 27.15/4.01  
% 27.15/4.01  --resolution_flag                       true
% 27.15/4.01  --res_lit_sel                           adaptive
% 27.15/4.01  --res_lit_sel_side                      none
% 27.15/4.01  --res_ordering                          kbo
% 27.15/4.01  --res_to_prop_solver                    active
% 27.15/4.01  --res_prop_simpl_new                    false
% 27.15/4.01  --res_prop_simpl_given                  true
% 27.15/4.01  --res_passive_queue_type                priority_queues
% 27.15/4.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.15/4.01  --res_passive_queues_freq               [15;5]
% 27.15/4.01  --res_forward_subs                      full
% 27.15/4.01  --res_backward_subs                     full
% 27.15/4.01  --res_forward_subs_resolution           true
% 27.15/4.01  --res_backward_subs_resolution          true
% 27.15/4.01  --res_orphan_elimination                true
% 27.15/4.01  --res_time_limit                        2.
% 27.15/4.01  --res_out_proof                         true
% 27.15/4.01  
% 27.15/4.01  ------ Superposition Options
% 27.15/4.01  
% 27.15/4.01  --superposition_flag                    true
% 27.15/4.01  --sup_passive_queue_type                priority_queues
% 27.15/4.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.15/4.01  --sup_passive_queues_freq               [1;4]
% 27.15/4.01  --demod_completeness_check              fast
% 27.15/4.01  --demod_use_ground                      true
% 27.15/4.01  --sup_to_prop_solver                    passive
% 27.15/4.01  --sup_prop_simpl_new                    true
% 27.15/4.01  --sup_prop_simpl_given                  true
% 27.15/4.01  --sup_fun_splitting                     false
% 27.15/4.01  --sup_smt_interval                      50000
% 27.15/4.01  
% 27.15/4.01  ------ Superposition Simplification Setup
% 27.15/4.01  
% 27.15/4.01  --sup_indices_passive                   []
% 27.15/4.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.15/4.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.15/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.15/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 27.15/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.15/4.01  --sup_full_bw                           [BwDemod]
% 27.15/4.01  --sup_immed_triv                        [TrivRules]
% 27.15/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.15/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.15/4.01  --sup_immed_bw_main                     []
% 27.15/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.15/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 27.15/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.15/4.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.15/4.01  
% 27.15/4.01  ------ Combination Options
% 27.15/4.01  
% 27.15/4.01  --comb_res_mult                         3
% 27.15/4.01  --comb_sup_mult                         2
% 27.15/4.01  --comb_inst_mult                        10
% 27.15/4.01  
% 27.15/4.01  ------ Debug Options
% 27.15/4.01  
% 27.15/4.01  --dbg_backtrace                         false
% 27.15/4.01  --dbg_dump_prop_clauses                 false
% 27.15/4.01  --dbg_dump_prop_clauses_file            -
% 27.15/4.01  --dbg_out_stat                          false
% 27.15/4.01  ------ Parsing...
% 27.15/4.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.15/4.01  
% 27.15/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 27.15/4.01  
% 27.15/4.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.15/4.01  
% 27.15/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.15/4.01  ------ Proving...
% 27.15/4.01  ------ Problem Properties 
% 27.15/4.01  
% 27.15/4.01  
% 27.15/4.01  clauses                                 18
% 27.15/4.01  conjectures                             7
% 27.15/4.01  EPR                                     4
% 27.15/4.01  Horn                                    15
% 27.15/4.01  unary                                   7
% 27.15/4.01  binary                                  0
% 27.15/4.01  lits                                    56
% 27.15/4.01  lits eq                                 15
% 27.15/4.01  fd_pure                                 0
% 27.15/4.01  fd_pseudo                               0
% 27.15/4.01  fd_cond                                 0
% 27.15/4.01  fd_pseudo_cond                          3
% 27.15/4.01  AC symbols                              0
% 27.15/4.01  
% 27.15/4.01  ------ Input Options Time Limit: Unbounded
% 27.15/4.01  
% 27.15/4.01  
% 27.15/4.01  ------ 
% 27.15/4.01  Current options:
% 27.15/4.01  ------ 
% 27.15/4.01  
% 27.15/4.01  ------ Input Options
% 27.15/4.01  
% 27.15/4.01  --out_options                           all
% 27.15/4.01  --tptp_safe_out                         true
% 27.15/4.01  --problem_path                          ""
% 27.15/4.01  --include_path                          ""
% 27.15/4.01  --clausifier                            res/vclausify_rel
% 27.15/4.01  --clausifier_options                    --mode clausify
% 27.15/4.01  --stdin                                 false
% 27.15/4.01  --stats_out                             sel
% 27.15/4.01  
% 27.15/4.01  ------ General Options
% 27.15/4.01  
% 27.15/4.01  --fof                                   false
% 27.15/4.01  --time_out_real                         604.99
% 27.15/4.01  --time_out_virtual                      -1.
% 27.15/4.01  --symbol_type_check                     false
% 27.15/4.01  --clausify_out                          false
% 27.15/4.01  --sig_cnt_out                           false
% 27.15/4.01  --trig_cnt_out                          false
% 27.15/4.01  --trig_cnt_out_tolerance                1.
% 27.15/4.01  --trig_cnt_out_sk_spl                   false
% 27.15/4.01  --abstr_cl_out                          false
% 27.15/4.01  
% 27.15/4.01  ------ Global Options
% 27.15/4.01  
% 27.15/4.01  --schedule                              none
% 27.15/4.01  --add_important_lit                     false
% 27.15/4.01  --prop_solver_per_cl                    1000
% 27.15/4.01  --min_unsat_core                        false
% 27.15/4.01  --soft_assumptions                      false
% 27.15/4.01  --soft_lemma_size                       3
% 27.15/4.01  --prop_impl_unit_size                   0
% 27.15/4.01  --prop_impl_unit                        []
% 27.15/4.01  --share_sel_clauses                     true
% 27.15/4.01  --reset_solvers                         false
% 27.15/4.01  --bc_imp_inh                            [conj_cone]
% 27.15/4.01  --conj_cone_tolerance                   3.
% 27.15/4.01  --extra_neg_conj                        none
% 27.15/4.01  --large_theory_mode                     true
% 27.15/4.01  --prolific_symb_bound                   200
% 27.15/4.01  --lt_threshold                          2000
% 27.15/4.01  --clause_weak_htbl                      true
% 27.15/4.01  --gc_record_bc_elim                     false
% 27.15/4.01  
% 27.15/4.01  ------ Preprocessing Options
% 27.15/4.01  
% 27.15/4.01  --preprocessing_flag                    true
% 27.15/4.01  --time_out_prep_mult                    0.1
% 27.15/4.01  --splitting_mode                        input
% 27.15/4.01  --splitting_grd                         true
% 27.15/4.01  --splitting_cvd                         false
% 27.15/4.01  --splitting_cvd_svl                     false
% 27.15/4.01  --splitting_nvd                         32
% 27.15/4.01  --sub_typing                            true
% 27.15/4.01  --prep_gs_sim                           false
% 27.15/4.01  --prep_unflatten                        true
% 27.15/4.01  --prep_res_sim                          true
% 27.15/4.01  --prep_upred                            true
% 27.15/4.01  --prep_sem_filter                       exhaustive
% 27.15/4.01  --prep_sem_filter_out                   false
% 27.15/4.01  --pred_elim                             false
% 27.15/4.01  --res_sim_input                         true
% 27.15/4.01  --eq_ax_congr_red                       true
% 27.15/4.01  --pure_diseq_elim                       true
% 27.15/4.01  --brand_transform                       false
% 27.15/4.01  --non_eq_to_eq                          false
% 27.15/4.01  --prep_def_merge                        true
% 27.15/4.01  --prep_def_merge_prop_impl              false
% 27.15/4.01  --prep_def_merge_mbd                    true
% 27.15/4.01  --prep_def_merge_tr_red                 false
% 27.15/4.01  --prep_def_merge_tr_cl                  false
% 27.15/4.01  --smt_preprocessing                     true
% 27.15/4.01  --smt_ac_axioms                         fast
% 27.15/4.01  --preprocessed_out                      false
% 27.15/4.01  --preprocessed_stats                    false
% 27.15/4.01  
% 27.15/4.01  ------ Abstraction refinement Options
% 27.15/4.01  
% 27.15/4.01  --abstr_ref                             []
% 27.15/4.01  --abstr_ref_prep                        false
% 27.15/4.01  --abstr_ref_until_sat                   false
% 27.15/4.01  --abstr_ref_sig_restrict                funpre
% 27.15/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 27.15/4.01  --abstr_ref_under                       []
% 27.15/4.01  
% 27.15/4.01  ------ SAT Options
% 27.15/4.01  
% 27.15/4.01  --sat_mode                              false
% 27.15/4.01  --sat_fm_restart_options                ""
% 27.15/4.01  --sat_gr_def                            false
% 27.15/4.01  --sat_epr_types                         true
% 27.15/4.01  --sat_non_cyclic_types                  false
% 27.15/4.01  --sat_finite_models                     false
% 27.15/4.01  --sat_fm_lemmas                         false
% 27.15/4.01  --sat_fm_prep                           false
% 27.15/4.01  --sat_fm_uc_incr                        true
% 27.15/4.01  --sat_out_model                         small
% 27.15/4.01  --sat_out_clauses                       false
% 27.15/4.01  
% 27.15/4.01  ------ QBF Options
% 27.15/4.01  
% 27.15/4.01  --qbf_mode                              false
% 27.15/4.01  --qbf_elim_univ                         false
% 27.15/4.01  --qbf_dom_inst                          none
% 27.15/4.01  --qbf_dom_pre_inst                      false
% 27.15/4.01  --qbf_sk_in                             false
% 27.15/4.01  --qbf_pred_elim                         true
% 27.15/4.01  --qbf_split                             512
% 27.15/4.01  
% 27.15/4.01  ------ BMC1 Options
% 27.15/4.01  
% 27.15/4.01  --bmc1_incremental                      false
% 27.15/4.01  --bmc1_axioms                           reachable_all
% 27.15/4.01  --bmc1_min_bound                        0
% 27.15/4.01  --bmc1_max_bound                        -1
% 27.15/4.01  --bmc1_max_bound_default                -1
% 27.15/4.01  --bmc1_symbol_reachability              true
% 27.15/4.01  --bmc1_property_lemmas                  false
% 27.15/4.01  --bmc1_k_induction                      false
% 27.15/4.01  --bmc1_non_equiv_states                 false
% 27.15/4.01  --bmc1_deadlock                         false
% 27.15/4.01  --bmc1_ucm                              false
% 27.15/4.01  --bmc1_add_unsat_core                   none
% 27.15/4.01  --bmc1_unsat_core_children              false
% 27.15/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 27.15/4.01  --bmc1_out_stat                         full
% 27.15/4.01  --bmc1_ground_init                      false
% 27.15/4.01  --bmc1_pre_inst_next_state              false
% 27.15/4.01  --bmc1_pre_inst_state                   false
% 27.15/4.01  --bmc1_pre_inst_reach_state             false
% 27.15/4.01  --bmc1_out_unsat_core                   false
% 27.15/4.01  --bmc1_aig_witness_out                  false
% 27.15/4.01  --bmc1_verbose                          false
% 27.15/4.01  --bmc1_dump_clauses_tptp                false
% 27.15/4.01  --bmc1_dump_unsat_core_tptp             false
% 27.15/4.01  --bmc1_dump_file                        -
% 27.15/4.01  --bmc1_ucm_expand_uc_limit              128
% 27.15/4.01  --bmc1_ucm_n_expand_iterations          6
% 27.15/4.01  --bmc1_ucm_extend_mode                  1
% 27.15/4.01  --bmc1_ucm_init_mode                    2
% 27.15/4.01  --bmc1_ucm_cone_mode                    none
% 27.15/4.01  --bmc1_ucm_reduced_relation_type        0
% 27.15/4.01  --bmc1_ucm_relax_model                  4
% 27.15/4.01  --bmc1_ucm_full_tr_after_sat            true
% 27.15/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 27.15/4.01  --bmc1_ucm_layered_model                none
% 27.15/4.01  --bmc1_ucm_max_lemma_size               10
% 27.15/4.01  
% 27.15/4.01  ------ AIG Options
% 27.15/4.01  
% 27.15/4.01  --aig_mode                              false
% 27.15/4.01  
% 27.15/4.01  ------ Instantiation Options
% 27.15/4.01  
% 27.15/4.01  --instantiation_flag                    true
% 27.15/4.01  --inst_sos_flag                         false
% 27.15/4.01  --inst_sos_phase                        true
% 27.15/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.15/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.15/4.01  --inst_lit_sel_side                     num_symb
% 27.15/4.01  --inst_solver_per_active                1400
% 27.15/4.01  --inst_solver_calls_frac                1.
% 27.15/4.01  --inst_passive_queue_type               priority_queues
% 27.15/4.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.15/4.01  --inst_passive_queues_freq              [25;2]
% 27.15/4.01  --inst_dismatching                      true
% 27.15/4.01  --inst_eager_unprocessed_to_passive     true
% 27.15/4.01  --inst_prop_sim_given                   true
% 27.15/4.01  --inst_prop_sim_new                     false
% 27.15/4.01  --inst_subs_new                         false
% 27.15/4.01  --inst_eq_res_simp                      false
% 27.15/4.01  --inst_subs_given                       false
% 27.15/4.01  --inst_orphan_elimination               true
% 27.15/4.01  --inst_learning_loop_flag               true
% 27.15/4.01  --inst_learning_start                   3000
% 27.15/4.01  --inst_learning_factor                  2
% 27.15/4.01  --inst_start_prop_sim_after_learn       3
% 27.15/4.01  --inst_sel_renew                        solver
% 27.15/4.01  --inst_lit_activity_flag                true
% 27.15/4.01  --inst_restr_to_given                   false
% 27.15/4.01  --inst_activity_threshold               500
% 27.15/4.01  --inst_out_proof                        true
% 27.15/4.01  
% 27.15/4.01  ------ Resolution Options
% 27.15/4.01  
% 27.15/4.01  --resolution_flag                       true
% 27.15/4.01  --res_lit_sel                           adaptive
% 27.15/4.01  --res_lit_sel_side                      none
% 27.15/4.01  --res_ordering                          kbo
% 27.15/4.01  --res_to_prop_solver                    active
% 27.15/4.01  --res_prop_simpl_new                    false
% 27.15/4.01  --res_prop_simpl_given                  true
% 27.15/4.01  --res_passive_queue_type                priority_queues
% 27.15/4.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.15/4.01  --res_passive_queues_freq               [15;5]
% 27.15/4.01  --res_forward_subs                      full
% 27.15/4.01  --res_backward_subs                     full
% 27.15/4.01  --res_forward_subs_resolution           true
% 27.15/4.01  --res_backward_subs_resolution          true
% 27.15/4.01  --res_orphan_elimination                true
% 27.15/4.01  --res_time_limit                        2.
% 27.15/4.01  --res_out_proof                         true
% 27.15/4.01  
% 27.15/4.01  ------ Superposition Options
% 27.15/4.01  
% 27.15/4.01  --superposition_flag                    true
% 27.15/4.01  --sup_passive_queue_type                priority_queues
% 27.15/4.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.15/4.01  --sup_passive_queues_freq               [1;4]
% 27.15/4.01  --demod_completeness_check              fast
% 27.15/4.01  --demod_use_ground                      true
% 27.15/4.01  --sup_to_prop_solver                    passive
% 27.15/4.01  --sup_prop_simpl_new                    true
% 27.15/4.01  --sup_prop_simpl_given                  true
% 27.15/4.01  --sup_fun_splitting                     false
% 27.15/4.01  --sup_smt_interval                      50000
% 27.15/4.01  
% 27.15/4.01  ------ Superposition Simplification Setup
% 27.15/4.01  
% 27.15/4.01  --sup_indices_passive                   []
% 27.15/4.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.15/4.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.15/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.15/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 27.15/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.15/4.01  --sup_full_bw                           [BwDemod]
% 27.15/4.01  --sup_immed_triv                        [TrivRules]
% 27.15/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.15/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.15/4.01  --sup_immed_bw_main                     []
% 27.15/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.15/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 27.15/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.15/4.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.15/4.01  
% 27.15/4.01  ------ Combination Options
% 27.15/4.01  
% 27.15/4.01  --comb_res_mult                         3
% 27.15/4.01  --comb_sup_mult                         2
% 27.15/4.01  --comb_inst_mult                        10
% 27.15/4.01  
% 27.15/4.01  ------ Debug Options
% 27.15/4.01  
% 27.15/4.01  --dbg_backtrace                         false
% 27.15/4.01  --dbg_dump_prop_clauses                 false
% 27.15/4.01  --dbg_dump_prop_clauses_file            -
% 27.15/4.01  --dbg_out_stat                          false
% 27.15/4.01  
% 27.15/4.01  
% 27.15/4.01  
% 27.15/4.01  
% 27.15/4.01  ------ Proving...
% 27.15/4.01  
% 27.15/4.01  
% 27.15/4.01  % SZS status Theorem for theBenchmark.p
% 27.15/4.01  
% 27.15/4.01  % SZS output start CNFRefutation for theBenchmark.p
% 27.15/4.01  
% 27.15/4.01  fof(f4,conjecture,(
% 27.15/4.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 27.15/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.15/4.01  
% 27.15/4.01  fof(f5,negated_conjecture,(
% 27.15/4.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 27.15/4.01    inference(negated_conjecture,[],[f4])).
% 27.15/4.01  
% 27.15/4.01  fof(f12,plain,(
% 27.15/4.01    ? [X0] : (? [X1] : ((k6_relat_1(k1_relat_1(X1)) != X1 & (k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 27.15/4.01    inference(ennf_transformation,[],[f5])).
% 27.15/4.01  
% 27.15/4.01  fof(f13,plain,(
% 27.15/4.01    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 27.15/4.01    inference(flattening,[],[f12])).
% 27.15/4.01  
% 27.15/4.01  fof(f26,plain,(
% 27.15/4.01    ( ! [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(k1_relat_1(sK5)) != sK5 & k5_relat_1(X0,sK5) = X0 & k2_relat_1(X0) = k1_relat_1(sK5) & v1_funct_1(sK5) & v1_relat_1(sK5))) )),
% 27.15/4.01    introduced(choice_axiom,[])).
% 27.15/4.01  
% 27.15/4.01  fof(f25,plain,(
% 27.15/4.01    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(sK4,X1) = sK4 & k2_relat_1(sK4) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 27.15/4.01    introduced(choice_axiom,[])).
% 27.15/4.01  
% 27.15/4.01  fof(f27,plain,(
% 27.15/4.01    (k6_relat_1(k1_relat_1(sK5)) != sK5 & k5_relat_1(sK4,sK5) = sK4 & k2_relat_1(sK4) = k1_relat_1(sK5) & v1_funct_1(sK5) & v1_relat_1(sK5)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 27.15/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f13,f26,f25])).
% 27.15/4.01  
% 27.15/4.01  fof(f41,plain,(
% 27.15/4.01    v1_relat_1(sK5)),
% 27.15/4.01    inference(cnf_transformation,[],[f27])).
% 27.15/4.01  
% 27.15/4.01  fof(f43,plain,(
% 27.15/4.01    k2_relat_1(sK4) = k1_relat_1(sK5)),
% 27.15/4.01    inference(cnf_transformation,[],[f27])).
% 27.15/4.01  
% 27.15/4.01  fof(f3,axiom,(
% 27.15/4.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 27.15/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.15/4.01  
% 27.15/4.01  fof(f10,plain,(
% 27.15/4.01    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 27.15/4.01    inference(ennf_transformation,[],[f3])).
% 27.15/4.01  
% 27.15/4.01  fof(f11,plain,(
% 27.15/4.01    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 27.15/4.01    inference(flattening,[],[f10])).
% 27.15/4.01  
% 27.15/4.01  fof(f20,plain,(
% 27.15/4.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 27.15/4.01    inference(nnf_transformation,[],[f11])).
% 27.15/4.01  
% 27.15/4.01  fof(f21,plain,(
% 27.15/4.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 27.15/4.01    inference(flattening,[],[f20])).
% 27.15/4.01  
% 27.15/4.01  fof(f22,plain,(
% 27.15/4.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 27.15/4.01    inference(rectify,[],[f21])).
% 27.15/4.01  
% 27.15/4.01  fof(f23,plain,(
% 27.15/4.01    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1) & r2_hidden(sK3(X0,X1),X0)))),
% 27.15/4.01    introduced(choice_axiom,[])).
% 27.15/4.01  
% 27.15/4.01  fof(f24,plain,(
% 27.15/4.01    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1) & r2_hidden(sK3(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 27.15/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 27.15/4.01  
% 27.15/4.01  fof(f37,plain,(
% 27.15/4.01    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.15/4.01    inference(cnf_transformation,[],[f24])).
% 27.15/4.01  
% 27.15/4.01  fof(f51,plain,(
% 27.15/4.01    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.15/4.01    inference(equality_resolution,[],[f37])).
% 27.15/4.01  
% 27.15/4.01  fof(f42,plain,(
% 27.15/4.01    v1_funct_1(sK5)),
% 27.15/4.01    inference(cnf_transformation,[],[f27])).
% 27.15/4.01  
% 27.15/4.01  fof(f45,plain,(
% 27.15/4.01    k6_relat_1(k1_relat_1(sK5)) != sK5),
% 27.15/4.01    inference(cnf_transformation,[],[f27])).
% 27.15/4.01  
% 27.15/4.01  fof(f1,axiom,(
% 27.15/4.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 27.15/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.15/4.01  
% 27.15/4.01  fof(f6,plain,(
% 27.15/4.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.15/4.01    inference(ennf_transformation,[],[f1])).
% 27.15/4.01  
% 27.15/4.01  fof(f7,plain,(
% 27.15/4.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.15/4.01    inference(flattening,[],[f6])).
% 27.15/4.01  
% 27.15/4.01  fof(f14,plain,(
% 27.15/4.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.15/4.01    inference(nnf_transformation,[],[f7])).
% 27.15/4.01  
% 27.15/4.01  fof(f15,plain,(
% 27.15/4.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.15/4.01    inference(rectify,[],[f14])).
% 27.15/4.01  
% 27.15/4.01  fof(f18,plain,(
% 27.15/4.01    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 27.15/4.01    introduced(choice_axiom,[])).
% 27.15/4.01  
% 27.15/4.01  fof(f17,plain,(
% 27.15/4.01    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 27.15/4.01    introduced(choice_axiom,[])).
% 27.15/4.01  
% 27.15/4.01  fof(f16,plain,(
% 27.15/4.01    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 27.15/4.01    introduced(choice_axiom,[])).
% 27.15/4.01  
% 27.15/4.01  fof(f19,plain,(
% 27.15/4.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.15/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).
% 27.15/4.01  
% 27.15/4.01  fof(f28,plain,(
% 27.15/4.01    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.15/4.01    inference(cnf_transformation,[],[f19])).
% 27.15/4.01  
% 27.15/4.01  fof(f49,plain,(
% 27.15/4.01    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.15/4.01    inference(equality_resolution,[],[f28])).
% 27.15/4.01  
% 27.15/4.01  fof(f2,axiom,(
% 27.15/4.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 27.15/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.15/4.01  
% 27.15/4.01  fof(f8,plain,(
% 27.15/4.01    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 27.15/4.01    inference(ennf_transformation,[],[f2])).
% 27.15/4.01  
% 27.15/4.01  fof(f9,plain,(
% 27.15/4.01    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 27.15/4.01    inference(flattening,[],[f8])).
% 27.15/4.01  
% 27.15/4.01  fof(f34,plain,(
% 27.15/4.01    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.15/4.01    inference(cnf_transformation,[],[f9])).
% 27.15/4.01  
% 27.15/4.01  fof(f29,plain,(
% 27.15/4.01    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.15/4.01    inference(cnf_transformation,[],[f19])).
% 27.15/4.01  
% 27.15/4.01  fof(f48,plain,(
% 27.15/4.01    ( ! [X0,X5] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.15/4.01    inference(equality_resolution,[],[f29])).
% 27.15/4.01  
% 27.15/4.01  fof(f39,plain,(
% 27.15/4.01    v1_relat_1(sK4)),
% 27.15/4.01    inference(cnf_transformation,[],[f27])).
% 27.15/4.01  
% 27.15/4.01  fof(f40,plain,(
% 27.15/4.01    v1_funct_1(sK4)),
% 27.15/4.01    inference(cnf_transformation,[],[f27])).
% 27.15/4.01  
% 27.15/4.01  fof(f44,plain,(
% 27.15/4.01    k5_relat_1(sK4,sK5) = sK4),
% 27.15/4.01    inference(cnf_transformation,[],[f27])).
% 27.15/4.01  
% 27.15/4.01  fof(f38,plain,(
% 27.15/4.01    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | k1_funct_1(X1,sK3(X0,X1)) != sK3(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.15/4.01    inference(cnf_transformation,[],[f24])).
% 27.15/4.01  
% 27.15/4.01  fof(f50,plain,(
% 27.15/4.01    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) != sK3(k1_relat_1(X1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 27.15/4.01    inference(equality_resolution,[],[f38])).
% 27.15/4.01  
% 27.15/4.01  cnf(c_15,negated_conjecture,
% 27.15/4.01      ( v1_relat_1(sK5) ),
% 27.15/4.01      inference(cnf_transformation,[],[f41]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_398,plain,
% 27.15/4.01      ( v1_relat_1(sK5) = iProver_top ),
% 27.15/4.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_13,negated_conjecture,
% 27.15/4.01      ( k2_relat_1(sK4) = k1_relat_1(sK5) ),
% 27.15/4.01      inference(cnf_transformation,[],[f43]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_8,plain,
% 27.15/4.01      ( r2_hidden(sK3(k1_relat_1(X0),X0),k1_relat_1(X0))
% 27.15/4.01      | ~ v1_relat_1(X0)
% 27.15/4.01      | ~ v1_funct_1(X0)
% 27.15/4.01      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 27.15/4.01      inference(cnf_transformation,[],[f51]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_402,plain,
% 27.15/4.01      ( k6_relat_1(k1_relat_1(X0)) = X0
% 27.15/4.01      | r2_hidden(sK3(k1_relat_1(X0),X0),k1_relat_1(X0)) = iProver_top
% 27.15/4.01      | v1_relat_1(X0) != iProver_top
% 27.15/4.01      | v1_funct_1(X0) != iProver_top ),
% 27.15/4.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_799,plain,
% 27.15/4.01      ( k6_relat_1(k1_relat_1(sK5)) = sK5
% 27.15/4.01      | r2_hidden(sK3(k2_relat_1(sK4),sK5),k2_relat_1(sK4)) = iProver_top
% 27.15/4.01      | v1_relat_1(sK5) != iProver_top
% 27.15/4.01      | v1_funct_1(sK5) != iProver_top ),
% 27.15/4.01      inference(superposition,[status(thm)],[c_13,c_402]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_818,plain,
% 27.15/4.01      ( k6_relat_1(k2_relat_1(sK4)) = sK5
% 27.15/4.01      | r2_hidden(sK3(k2_relat_1(sK4),sK5),k2_relat_1(sK4)) = iProver_top
% 27.15/4.01      | v1_relat_1(sK5) != iProver_top
% 27.15/4.01      | v1_funct_1(sK5) != iProver_top ),
% 27.15/4.01      inference(light_normalisation,[status(thm)],[c_799,c_13]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_20,plain,
% 27.15/4.01      ( v1_relat_1(sK5) = iProver_top ),
% 27.15/4.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_14,negated_conjecture,
% 27.15/4.01      ( v1_funct_1(sK5) ),
% 27.15/4.01      inference(cnf_transformation,[],[f42]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_21,plain,
% 27.15/4.01      ( v1_funct_1(sK5) = iProver_top ),
% 27.15/4.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_11,negated_conjecture,
% 27.15/4.01      ( k6_relat_1(k1_relat_1(sK5)) != sK5 ),
% 27.15/4.01      inference(cnf_transformation,[],[f45]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_423,plain,
% 27.15/4.01      ( k6_relat_1(k2_relat_1(sK4)) != sK5 ),
% 27.15/4.01      inference(light_normalisation,[status(thm)],[c_11,c_13]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_1067,plain,
% 27.15/4.01      ( r2_hidden(sK3(k2_relat_1(sK4),sK5),k2_relat_1(sK4)) = iProver_top ),
% 27.15/4.01      inference(global_propositional_subsumption,
% 27.15/4.01                [status(thm)],
% 27.15/4.01                [c_818,c_20,c_21,c_423]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_5,plain,
% 27.15/4.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 27.15/4.01      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 27.15/4.01      | ~ v1_relat_1(X1)
% 27.15/4.01      | ~ v1_funct_1(X1) ),
% 27.15/4.01      inference(cnf_transformation,[],[f49]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_405,plain,
% 27.15/4.01      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 27.15/4.01      | r2_hidden(sK2(X1,X0),k1_relat_1(X1)) = iProver_top
% 27.15/4.01      | v1_relat_1(X1) != iProver_top
% 27.15/4.01      | v1_funct_1(X1) != iProver_top ),
% 27.15/4.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_6,plain,
% 27.15/4.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 27.15/4.01      | ~ v1_relat_1(X1)
% 27.15/4.01      | ~ v1_relat_1(X2)
% 27.15/4.01      | ~ v1_funct_1(X1)
% 27.15/4.01      | ~ v1_funct_1(X2)
% 27.15/4.01      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 27.15/4.01      inference(cnf_transformation,[],[f34]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_404,plain,
% 27.15/4.01      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 27.15/4.01      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 27.15/4.01      | v1_relat_1(X0) != iProver_top
% 27.15/4.01      | v1_relat_1(X1) != iProver_top
% 27.15/4.01      | v1_funct_1(X0) != iProver_top
% 27.15/4.01      | v1_funct_1(X1) != iProver_top ),
% 27.15/4.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_1287,plain,
% 27.15/4.01      ( k1_funct_1(X0,k1_funct_1(X1,sK2(X1,X2))) = k1_funct_1(k5_relat_1(X1,X0),sK2(X1,X2))
% 27.15/4.01      | r2_hidden(X2,k2_relat_1(X1)) != iProver_top
% 27.15/4.01      | v1_relat_1(X1) != iProver_top
% 27.15/4.01      | v1_relat_1(X0) != iProver_top
% 27.15/4.01      | v1_funct_1(X1) != iProver_top
% 27.15/4.01      | v1_funct_1(X0) != iProver_top ),
% 27.15/4.01      inference(superposition,[status(thm)],[c_405,c_404]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_4659,plain,
% 27.15/4.01      ( k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))))
% 27.15/4.01      | v1_relat_1(X0) != iProver_top
% 27.15/4.01      | v1_relat_1(sK4) != iProver_top
% 27.15/4.01      | v1_funct_1(X0) != iProver_top
% 27.15/4.01      | v1_funct_1(sK4) != iProver_top ),
% 27.15/4.01      inference(superposition,[status(thm)],[c_1067,c_1287]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_4,plain,
% 27.15/4.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 27.15/4.01      | ~ v1_relat_1(X1)
% 27.15/4.01      | ~ v1_funct_1(X1)
% 27.15/4.01      | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
% 27.15/4.01      inference(cnf_transformation,[],[f48]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_406,plain,
% 27.15/4.01      ( k1_funct_1(X0,sK2(X0,X1)) = X1
% 27.15/4.01      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 27.15/4.01      | v1_relat_1(X0) != iProver_top
% 27.15/4.01      | v1_funct_1(X0) != iProver_top ),
% 27.15/4.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_1073,plain,
% 27.15/4.01      ( k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = sK3(k2_relat_1(sK4),sK5)
% 27.15/4.01      | v1_relat_1(sK4) != iProver_top
% 27.15/4.01      | v1_funct_1(sK4) != iProver_top ),
% 27.15/4.01      inference(superposition,[status(thm)],[c_1067,c_406]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_17,negated_conjecture,
% 27.15/4.01      ( v1_relat_1(sK4) ),
% 27.15/4.01      inference(cnf_transformation,[],[f39]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_18,plain,
% 27.15/4.01      ( v1_relat_1(sK4) = iProver_top ),
% 27.15/4.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_16,negated_conjecture,
% 27.15/4.01      ( v1_funct_1(sK4) ),
% 27.15/4.01      inference(cnf_transformation,[],[f40]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_19,plain,
% 27.15/4.01      ( v1_funct_1(sK4) = iProver_top ),
% 27.15/4.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_2225,plain,
% 27.15/4.01      ( k1_funct_1(sK4,sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = sK3(k2_relat_1(sK4),sK5) ),
% 27.15/4.01      inference(global_propositional_subsumption,
% 27.15/4.01                [status(thm)],
% 27.15/4.01                [c_1073,c_18,c_19]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_4723,plain,
% 27.15/4.01      ( k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,sK3(k2_relat_1(sK4),sK5))
% 27.15/4.01      | v1_relat_1(X0) != iProver_top
% 27.15/4.01      | v1_relat_1(sK4) != iProver_top
% 27.15/4.01      | v1_funct_1(X0) != iProver_top
% 27.15/4.01      | v1_funct_1(sK4) != iProver_top ),
% 27.15/4.01      inference(light_normalisation,[status(thm)],[c_4659,c_2225]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_112600,plain,
% 27.15/4.01      ( v1_funct_1(X0) != iProver_top
% 27.15/4.01      | k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,sK3(k2_relat_1(sK4),sK5))
% 27.15/4.01      | v1_relat_1(X0) != iProver_top ),
% 27.15/4.01      inference(global_propositional_subsumption,
% 27.15/4.01                [status(thm)],
% 27.15/4.01                [c_4723,c_18,c_19]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_112601,plain,
% 27.15/4.01      ( k1_funct_1(k5_relat_1(sK4,X0),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(X0,sK3(k2_relat_1(sK4),sK5))
% 27.15/4.01      | v1_relat_1(X0) != iProver_top
% 27.15/4.01      | v1_funct_1(X0) != iProver_top ),
% 27.15/4.01      inference(renaming,[status(thm)],[c_112600]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_112609,plain,
% 27.15/4.01      ( k1_funct_1(k5_relat_1(sK4,sK5),sK2(sK4,sK3(k2_relat_1(sK4),sK5))) = k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5))
% 27.15/4.01      | v1_funct_1(sK5) != iProver_top ),
% 27.15/4.01      inference(superposition,[status(thm)],[c_398,c_112601]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_12,negated_conjecture,
% 27.15/4.01      ( k5_relat_1(sK4,sK5) = sK4 ),
% 27.15/4.01      inference(cnf_transformation,[],[f44]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_112617,plain,
% 27.15/4.01      ( k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) = sK3(k2_relat_1(sK4),sK5)
% 27.15/4.01      | v1_funct_1(sK5) != iProver_top ),
% 27.15/4.01      inference(light_normalisation,[status(thm)],[c_112609,c_12,c_2225]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_7,plain,
% 27.15/4.01      ( ~ v1_relat_1(X0)
% 27.15/4.01      | ~ v1_funct_1(X0)
% 27.15/4.01      | k1_funct_1(X0,sK3(k1_relat_1(X0),X0)) != sK3(k1_relat_1(X0),X0)
% 27.15/4.01      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 27.15/4.01      inference(cnf_transformation,[],[f50]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_403,plain,
% 27.15/4.01      ( k1_funct_1(X0,sK3(k1_relat_1(X0),X0)) != sK3(k1_relat_1(X0),X0)
% 27.15/4.01      | k6_relat_1(k1_relat_1(X0)) = X0
% 27.15/4.01      | v1_relat_1(X0) != iProver_top
% 27.15/4.01      | v1_funct_1(X0) != iProver_top ),
% 27.15/4.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_969,plain,
% 27.15/4.01      ( k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) != sK3(k1_relat_1(sK5),sK5)
% 27.15/4.01      | k6_relat_1(k1_relat_1(sK5)) = sK5
% 27.15/4.01      | v1_relat_1(sK5) != iProver_top
% 27.15/4.01      | v1_funct_1(sK5) != iProver_top ),
% 27.15/4.01      inference(superposition,[status(thm)],[c_13,c_403]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(c_970,plain,
% 27.15/4.01      ( k1_funct_1(sK5,sK3(k2_relat_1(sK4),sK5)) != sK3(k2_relat_1(sK4),sK5)
% 27.15/4.01      | k6_relat_1(k2_relat_1(sK4)) = sK5
% 27.15/4.01      | v1_relat_1(sK5) != iProver_top
% 27.15/4.01      | v1_funct_1(sK5) != iProver_top ),
% 27.15/4.01      inference(light_normalisation,[status(thm)],[c_969,c_13]) ).
% 27.15/4.01  
% 27.15/4.01  cnf(contradiction,plain,
% 27.15/4.01      ( $false ),
% 27.15/4.01      inference(minisat,[status(thm)],[c_112617,c_970,c_423,c_21,c_20]) ).
% 27.15/4.01  
% 27.15/4.01  
% 27.15/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 27.15/4.01  
% 27.15/4.01  ------                               Statistics
% 27.15/4.01  
% 27.15/4.01  ------ Selected
% 27.15/4.01  
% 27.15/4.01  total_time:                             3.113
% 27.15/4.01  
%------------------------------------------------------------------------------
