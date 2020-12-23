%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:22 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  144 (1331 expanded)
%              Number of clauses        :   80 ( 342 expanded)
%              Number of leaves         :   17 ( 303 expanded)
%              Depth                    :   21
%              Number of atoms          :  547 (6596 expanded)
%              Number of equality atoms :  179 (1754 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
          | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
        & r2_hidden(X0,k2_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK9),sK9),sK8) != sK8
        | k1_funct_1(sK9,k1_funct_1(k2_funct_1(sK9),sK8)) != sK8 )
      & r2_hidden(sK8,k2_relat_1(sK9))
      & v2_funct_1(sK9)
      & v1_funct_1(sK9)
      & v1_relat_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( k1_funct_1(k5_relat_1(k2_funct_1(sK9),sK9),sK8) != sK8
      | k1_funct_1(sK9,k1_funct_1(k2_funct_1(sK9),sK8)) != sK8 )
    & r2_hidden(sK8,k2_relat_1(sK9))
    & v2_funct_1(sK9)
    & v1_funct_1(sK9)
    & v1_relat_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f22,f41])).

fof(f64,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    r2_hidden(sK8,k2_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f36,f37])).

fof(f52,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f56,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    v2_funct_1(sK9) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f58,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f67,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK9),sK9),sK8) != sK8
    | k1_funct_1(sK9,k1_funct_1(k2_funct_1(sK9),sK8)) != sK8 ),
    inference(cnf_transformation,[],[f42])).

fof(f51,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_793,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK8,k2_relat_1(sK9)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_794,plain,
    ( r2_hidden(sK8,k2_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_805,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_18,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_795,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1417,plain,
    ( k1_funct_1(X0,sK5(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_795])).

cnf(c_5767,plain,
    ( k1_funct_1(sK9,sK5(sK9,sK8)) = sK8
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_794,c_1417])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK9) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_999,plain,
    ( r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9)
    | ~ r2_hidden(sK8,k2_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1021,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | k1_funct_1(sK9,sK5(sK9,sK8)) = sK8 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6009,plain,
    ( k1_funct_1(sK9,sK5(sK9,sK8)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5767,c_24,c_23,c_21,c_999,c_1021])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_796,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6012,plain,
    ( r2_hidden(sK5(sK9,sK8),k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9) = iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6009,c_796])).

cnf(c_28,plain,
    ( r2_hidden(sK8,k2_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1000,plain,
    ( r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9) = iProver_top
    | r2_hidden(sK8,k2_relat_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_999])).

cnf(c_6518,plain,
    ( r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6012,c_28,c_1000])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_802,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k4_relat_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_800,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_910,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_802,c_800])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_810,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2059,plain,
    ( r2_hidden(X0,k1_relat_1(k4_relat_1(X1))) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_810])).

cnf(c_6525,plain,
    ( r2_hidden(sK8,k1_relat_1(k4_relat_1(sK9))) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6518,c_2059])).

cnf(c_25,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_50,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_52,plain,
    ( v1_relat_1(k4_relat_1(sK9)) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_1022,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9)
    | r2_hidden(k4_tarski(sK8,sK5(sK9,sK8)),k4_relat_1(sK9))
    | ~ v1_relat_1(k4_relat_1(sK9))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1023,plain,
    ( r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9) != iProver_top
    | r2_hidden(k4_tarski(sK8,sK5(sK9,sK8)),k4_relat_1(sK9)) = iProver_top
    | v1_relat_1(k4_relat_1(sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_1114,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK5(sK9,sK8)),k4_relat_1(sK9))
    | r2_hidden(sK8,k1_relat_1(k4_relat_1(sK9))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1115,plain,
    ( r2_hidden(k4_tarski(sK8,sK5(sK9,sK8)),k4_relat_1(sK9)) != iProver_top
    | r2_hidden(sK8,k1_relat_1(k4_relat_1(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1114])).

cnf(c_7506,plain,
    ( r2_hidden(sK8,k1_relat_1(k4_relat_1(sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6525,c_25,c_28,c_52,c_1000,c_1023,c_1115])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_797,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7511,plain,
    ( k1_funct_1(X0,k1_funct_1(k4_relat_1(sK9),sK8)) = k1_funct_1(k5_relat_1(k4_relat_1(sK9),X0),sK8)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK9)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7506,c_797])).

cnf(c_26,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK9) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_274,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_275,plain,
    ( ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | k2_funct_1(sK9) = k4_relat_1(sK9) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_48,plain,
    ( ~ v1_funct_1(sK9)
    | ~ v2_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | k2_funct_1(sK9) = k4_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_277,plain,
    ( k2_funct_1(sK9) = k4_relat_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_24,c_23,c_22,c_48])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_799,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1410,plain,
    ( v1_funct_1(k4_relat_1(sK9)) = iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_277,c_799])).

cnf(c_12164,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,k1_funct_1(k4_relat_1(sK9),sK8)) = k1_funct_1(k5_relat_1(k4_relat_1(sK9),X0),sK8)
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7511,c_25,c_26,c_52,c_1410])).

cnf(c_12165,plain,
    ( k1_funct_1(X0,k1_funct_1(k4_relat_1(sK9),sK8)) = k1_funct_1(k5_relat_1(k4_relat_1(sK9),X0),sK8)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12164])).

cnf(c_12174,plain,
    ( k1_funct_1(sK9,k1_funct_1(k4_relat_1(sK9),sK8)) = k1_funct_1(k5_relat_1(k4_relat_1(sK9),sK9),sK8)
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_12165])).

cnf(c_7524,plain,
    ( k1_funct_1(sK9,k1_funct_1(k4_relat_1(sK9),sK8)) = k1_funct_1(k5_relat_1(k4_relat_1(sK9),sK9),sK8)
    | v1_funct_1(k4_relat_1(sK9)) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(k4_relat_1(sK9)) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7511])).

cnf(c_12297,plain,
    ( k1_funct_1(sK9,k1_funct_1(k4_relat_1(sK9),sK8)) = k1_funct_1(k5_relat_1(k4_relat_1(sK9),sK9),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12174,c_25,c_26,c_52,c_1410,c_7524])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_809,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1538,plain,
    ( k1_funct_1(X0,X1) = sK2(X0,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_795])).

cnf(c_7652,plain,
    ( k1_funct_1(k4_relat_1(sK9),sK8) = sK2(k4_relat_1(sK9),sK8)
    | v1_funct_1(k4_relat_1(sK9)) != iProver_top
    | v1_relat_1(k4_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7506,c_1538])).

cnf(c_51,plain,
    ( v1_relat_1(k4_relat_1(sK9))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1411,plain,
    ( v1_funct_1(k4_relat_1(sK9))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1410])).

cnf(c_1139,plain,
    ( r2_hidden(k4_tarski(sK8,sK2(X0,sK8)),X0)
    | ~ r2_hidden(sK8,k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1467,plain,
    ( r2_hidden(k4_tarski(sK8,sK2(k4_relat_1(sK9),sK8)),k4_relat_1(sK9))
    | ~ r2_hidden(sK8,k1_relat_1(k4_relat_1(sK9))) ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_2238,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK2(X0,sK8)),X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK8) = sK2(X0,sK8) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6159,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK2(k4_relat_1(sK9),sK8)),k4_relat_1(sK9))
    | ~ v1_funct_1(k4_relat_1(sK9))
    | ~ v1_relat_1(k4_relat_1(sK9))
    | k1_funct_1(k4_relat_1(sK9),sK8) = sK2(k4_relat_1(sK9),sK8) ),
    inference(instantiation,[status(thm)],[c_2238])).

cnf(c_9223,plain,
    ( k1_funct_1(k4_relat_1(sK9),sK8) = sK2(k4_relat_1(sK9),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7652,c_24,c_23,c_21,c_51,c_999,c_1022,c_1114,c_1411,c_1467,c_6159])).

cnf(c_20,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK9),sK9),sK8) != sK8
    | k1_funct_1(sK9,k1_funct_1(k2_funct_1(sK9),sK8)) != sK8 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_853,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK9),sK9),sK8) != sK8
    | k1_funct_1(sK9,k1_funct_1(k4_relat_1(sK9),sK8)) != sK8 ),
    inference(light_normalisation,[status(thm)],[c_20,c_277])).

cnf(c_9228,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK9),sK9),sK8) != sK8
    | k1_funct_1(sK9,sK2(k4_relat_1(sK9),sK8)) != sK8 ),
    inference(demodulation,[status(thm)],[c_9223,c_853])).

cnf(c_1138,plain,
    ( r2_hidden(k4_tarski(sK8,k1_funct_1(X0,sK8)),X0)
    | ~ r2_hidden(sK8,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2162,plain,
    ( r2_hidden(k4_tarski(sK8,k1_funct_1(k4_relat_1(X0),sK8)),k4_relat_1(X0))
    | ~ r2_hidden(sK8,k1_relat_1(k4_relat_1(X0)))
    | ~ v1_funct_1(k4_relat_1(X0))
    | ~ v1_relat_1(k4_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_2165,plain,
    ( r2_hidden(k4_tarski(sK8,k1_funct_1(k4_relat_1(sK9),sK8)),k4_relat_1(sK9))
    | ~ r2_hidden(sK8,k1_relat_1(k4_relat_1(sK9)))
    | ~ v1_funct_1(k4_relat_1(sK9))
    | ~ v1_relat_1(k4_relat_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_2162])).

cnf(c_11,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k4_relat_1(X2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2163,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(X0),sK8),sK8),X0)
    | ~ r2_hidden(k4_tarski(sK8,k1_funct_1(k4_relat_1(X0),sK8)),k4_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k4_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2169,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(sK9),sK8),sK8),sK9)
    | ~ r2_hidden(k4_tarski(sK8,k1_funct_1(k4_relat_1(sK9),sK8)),k4_relat_1(sK9))
    | ~ v1_relat_1(k4_relat_1(sK9))
    | ~ v1_relat_1(sK9) ),
    inference(instantiation,[status(thm)],[c_2163])).

cnf(c_6134,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(X0),sK8),sK8),X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,k1_funct_1(k4_relat_1(X0),sK8)) = sK8 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6141,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(sK9),sK8),sK8),sK9)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | k1_funct_1(sK9,k1_funct_1(k4_relat_1(sK9),sK8)) = sK8 ),
    inference(instantiation,[status(thm)],[c_6134])).

cnf(c_9552,plain,
    ( k1_funct_1(k5_relat_1(k4_relat_1(sK9),sK9),sK8) != sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9228,c_24,c_23,c_21,c_51,c_853,c_999,c_1022,c_1114,c_1411,c_2165,c_2169,c_6141])).

cnf(c_12300,plain,
    ( k1_funct_1(sK9,k1_funct_1(k4_relat_1(sK9),sK8)) != sK8 ),
    inference(demodulation,[status(thm)],[c_12297,c_9552])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12300,c_6141,c_2169,c_2165,c_1411,c_1114,c_1022,c_999,c_51,c_21,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.66/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.04  
% 1.66/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.66/1.04  
% 1.66/1.04  ------  iProver source info
% 1.66/1.04  
% 1.66/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.66/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.66/1.04  git: non_committed_changes: false
% 1.66/1.04  git: last_make_outside_of_git: false
% 1.66/1.04  
% 1.66/1.04  ------ 
% 1.66/1.04  
% 1.66/1.04  ------ Input Options
% 1.66/1.04  
% 1.66/1.04  --out_options                           all
% 1.66/1.04  --tptp_safe_out                         true
% 1.66/1.04  --problem_path                          ""
% 1.66/1.04  --include_path                          ""
% 1.66/1.04  --clausifier                            res/vclausify_rel
% 1.66/1.04  --clausifier_options                    --mode clausify
% 1.66/1.04  --stdin                                 false
% 1.66/1.04  --stats_out                             all
% 1.66/1.04  
% 1.66/1.04  ------ General Options
% 1.66/1.04  
% 1.66/1.04  --fof                                   false
% 1.66/1.04  --time_out_real                         305.
% 1.66/1.04  --time_out_virtual                      -1.
% 1.66/1.04  --symbol_type_check                     false
% 1.66/1.04  --clausify_out                          false
% 1.66/1.04  --sig_cnt_out                           false
% 1.66/1.04  --trig_cnt_out                          false
% 1.66/1.04  --trig_cnt_out_tolerance                1.
% 1.66/1.04  --trig_cnt_out_sk_spl                   false
% 1.66/1.04  --abstr_cl_out                          false
% 1.66/1.04  
% 1.66/1.04  ------ Global Options
% 1.66/1.04  
% 1.66/1.04  --schedule                              default
% 1.66/1.04  --add_important_lit                     false
% 1.66/1.04  --prop_solver_per_cl                    1000
% 1.66/1.04  --min_unsat_core                        false
% 1.66/1.04  --soft_assumptions                      false
% 1.66/1.04  --soft_lemma_size                       3
% 1.66/1.04  --prop_impl_unit_size                   0
% 1.66/1.04  --prop_impl_unit                        []
% 1.66/1.04  --share_sel_clauses                     true
% 1.66/1.04  --reset_solvers                         false
% 1.66/1.04  --bc_imp_inh                            [conj_cone]
% 1.66/1.04  --conj_cone_tolerance                   3.
% 1.66/1.04  --extra_neg_conj                        none
% 1.66/1.04  --large_theory_mode                     true
% 1.66/1.04  --prolific_symb_bound                   200
% 1.66/1.04  --lt_threshold                          2000
% 1.66/1.04  --clause_weak_htbl                      true
% 1.66/1.04  --gc_record_bc_elim                     false
% 1.66/1.04  
% 1.66/1.04  ------ Preprocessing Options
% 1.66/1.04  
% 1.66/1.04  --preprocessing_flag                    true
% 1.66/1.04  --time_out_prep_mult                    0.1
% 1.66/1.04  --splitting_mode                        input
% 1.66/1.04  --splitting_grd                         true
% 1.66/1.04  --splitting_cvd                         false
% 1.66/1.04  --splitting_cvd_svl                     false
% 1.66/1.04  --splitting_nvd                         32
% 1.66/1.04  --sub_typing                            true
% 1.66/1.04  --prep_gs_sim                           true
% 1.66/1.04  --prep_unflatten                        true
% 1.66/1.04  --prep_res_sim                          true
% 1.66/1.04  --prep_upred                            true
% 1.66/1.04  --prep_sem_filter                       exhaustive
% 1.66/1.04  --prep_sem_filter_out                   false
% 1.66/1.04  --pred_elim                             true
% 1.66/1.04  --res_sim_input                         true
% 1.66/1.04  --eq_ax_congr_red                       true
% 1.66/1.04  --pure_diseq_elim                       true
% 1.66/1.04  --brand_transform                       false
% 1.66/1.04  --non_eq_to_eq                          false
% 1.66/1.04  --prep_def_merge                        true
% 1.66/1.04  --prep_def_merge_prop_impl              false
% 1.66/1.04  --prep_def_merge_mbd                    true
% 1.66/1.04  --prep_def_merge_tr_red                 false
% 1.66/1.04  --prep_def_merge_tr_cl                  false
% 1.66/1.04  --smt_preprocessing                     true
% 1.66/1.04  --smt_ac_axioms                         fast
% 1.66/1.04  --preprocessed_out                      false
% 1.66/1.04  --preprocessed_stats                    false
% 1.66/1.04  
% 1.66/1.04  ------ Abstraction refinement Options
% 1.66/1.04  
% 1.66/1.04  --abstr_ref                             []
% 1.66/1.04  --abstr_ref_prep                        false
% 1.66/1.04  --abstr_ref_until_sat                   false
% 1.66/1.04  --abstr_ref_sig_restrict                funpre
% 1.66/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.66/1.04  --abstr_ref_under                       []
% 1.66/1.04  
% 1.66/1.04  ------ SAT Options
% 1.66/1.04  
% 1.66/1.04  --sat_mode                              false
% 1.66/1.04  --sat_fm_restart_options                ""
% 1.66/1.04  --sat_gr_def                            false
% 1.66/1.04  --sat_epr_types                         true
% 1.66/1.04  --sat_non_cyclic_types                  false
% 1.66/1.04  --sat_finite_models                     false
% 1.66/1.04  --sat_fm_lemmas                         false
% 1.66/1.04  --sat_fm_prep                           false
% 1.66/1.04  --sat_fm_uc_incr                        true
% 1.66/1.04  --sat_out_model                         small
% 1.66/1.04  --sat_out_clauses                       false
% 1.66/1.04  
% 1.66/1.04  ------ QBF Options
% 1.66/1.04  
% 1.66/1.04  --qbf_mode                              false
% 1.66/1.04  --qbf_elim_univ                         false
% 1.66/1.04  --qbf_dom_inst                          none
% 1.66/1.04  --qbf_dom_pre_inst                      false
% 1.66/1.04  --qbf_sk_in                             false
% 1.66/1.04  --qbf_pred_elim                         true
% 1.66/1.04  --qbf_split                             512
% 1.66/1.04  
% 1.66/1.04  ------ BMC1 Options
% 1.66/1.04  
% 1.66/1.04  --bmc1_incremental                      false
% 1.66/1.04  --bmc1_axioms                           reachable_all
% 1.66/1.04  --bmc1_min_bound                        0
% 1.66/1.04  --bmc1_max_bound                        -1
% 1.66/1.04  --bmc1_max_bound_default                -1
% 1.66/1.04  --bmc1_symbol_reachability              true
% 1.66/1.04  --bmc1_property_lemmas                  false
% 1.66/1.04  --bmc1_k_induction                      false
% 1.66/1.04  --bmc1_non_equiv_states                 false
% 1.66/1.04  --bmc1_deadlock                         false
% 1.66/1.04  --bmc1_ucm                              false
% 1.66/1.04  --bmc1_add_unsat_core                   none
% 1.66/1.04  --bmc1_unsat_core_children              false
% 1.66/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.66/1.04  --bmc1_out_stat                         full
% 1.66/1.04  --bmc1_ground_init                      false
% 1.66/1.04  --bmc1_pre_inst_next_state              false
% 1.66/1.04  --bmc1_pre_inst_state                   false
% 1.66/1.04  --bmc1_pre_inst_reach_state             false
% 1.66/1.04  --bmc1_out_unsat_core                   false
% 1.66/1.04  --bmc1_aig_witness_out                  false
% 1.66/1.04  --bmc1_verbose                          false
% 1.66/1.04  --bmc1_dump_clauses_tptp                false
% 1.66/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.66/1.04  --bmc1_dump_file                        -
% 1.66/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.66/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.66/1.04  --bmc1_ucm_extend_mode                  1
% 1.66/1.04  --bmc1_ucm_init_mode                    2
% 1.66/1.04  --bmc1_ucm_cone_mode                    none
% 1.66/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.66/1.04  --bmc1_ucm_relax_model                  4
% 1.66/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.66/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.66/1.04  --bmc1_ucm_layered_model                none
% 1.66/1.04  --bmc1_ucm_max_lemma_size               10
% 1.66/1.04  
% 1.66/1.04  ------ AIG Options
% 1.66/1.04  
% 1.66/1.04  --aig_mode                              false
% 1.66/1.04  
% 1.66/1.04  ------ Instantiation Options
% 1.66/1.04  
% 1.66/1.04  --instantiation_flag                    true
% 1.66/1.04  --inst_sos_flag                         false
% 1.66/1.04  --inst_sos_phase                        true
% 1.66/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.66/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.66/1.04  --inst_lit_sel_side                     num_symb
% 1.66/1.04  --inst_solver_per_active                1400
% 1.66/1.04  --inst_solver_calls_frac                1.
% 1.66/1.04  --inst_passive_queue_type               priority_queues
% 1.66/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.66/1.04  --inst_passive_queues_freq              [25;2]
% 1.66/1.04  --inst_dismatching                      true
% 1.66/1.04  --inst_eager_unprocessed_to_passive     true
% 1.66/1.04  --inst_prop_sim_given                   true
% 1.66/1.04  --inst_prop_sim_new                     false
% 1.66/1.04  --inst_subs_new                         false
% 1.66/1.04  --inst_eq_res_simp                      false
% 1.66/1.04  --inst_subs_given                       false
% 1.66/1.04  --inst_orphan_elimination               true
% 1.66/1.04  --inst_learning_loop_flag               true
% 1.66/1.04  --inst_learning_start                   3000
% 1.66/1.04  --inst_learning_factor                  2
% 1.66/1.04  --inst_start_prop_sim_after_learn       3
% 1.66/1.04  --inst_sel_renew                        solver
% 1.66/1.04  --inst_lit_activity_flag                true
% 1.66/1.04  --inst_restr_to_given                   false
% 1.66/1.04  --inst_activity_threshold               500
% 1.66/1.04  --inst_out_proof                        true
% 1.66/1.04  
% 1.66/1.04  ------ Resolution Options
% 1.66/1.04  
% 1.66/1.04  --resolution_flag                       true
% 1.66/1.04  --res_lit_sel                           adaptive
% 1.66/1.04  --res_lit_sel_side                      none
% 1.66/1.04  --res_ordering                          kbo
% 1.66/1.04  --res_to_prop_solver                    active
% 1.66/1.04  --res_prop_simpl_new                    false
% 1.66/1.04  --res_prop_simpl_given                  true
% 1.66/1.04  --res_passive_queue_type                priority_queues
% 1.66/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.66/1.04  --res_passive_queues_freq               [15;5]
% 1.66/1.04  --res_forward_subs                      full
% 1.66/1.04  --res_backward_subs                     full
% 1.66/1.04  --res_forward_subs_resolution           true
% 1.66/1.04  --res_backward_subs_resolution          true
% 1.66/1.04  --res_orphan_elimination                true
% 1.66/1.04  --res_time_limit                        2.
% 1.66/1.04  --res_out_proof                         true
% 1.66/1.04  
% 1.66/1.04  ------ Superposition Options
% 1.66/1.04  
% 1.66/1.04  --superposition_flag                    true
% 1.66/1.04  --sup_passive_queue_type                priority_queues
% 1.66/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.66/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.66/1.04  --demod_completeness_check              fast
% 1.66/1.04  --demod_use_ground                      true
% 1.66/1.04  --sup_to_prop_solver                    passive
% 1.66/1.04  --sup_prop_simpl_new                    true
% 1.66/1.04  --sup_prop_simpl_given                  true
% 1.66/1.04  --sup_fun_splitting                     false
% 1.66/1.04  --sup_smt_interval                      50000
% 1.66/1.04  
% 1.66/1.04  ------ Superposition Simplification Setup
% 1.66/1.04  
% 1.66/1.04  --sup_indices_passive                   []
% 1.66/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.66/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.04  --sup_full_bw                           [BwDemod]
% 1.66/1.04  --sup_immed_triv                        [TrivRules]
% 1.66/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.66/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.04  --sup_immed_bw_main                     []
% 1.66/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.66/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.04  
% 1.66/1.04  ------ Combination Options
% 1.66/1.04  
% 1.66/1.04  --comb_res_mult                         3
% 1.66/1.04  --comb_sup_mult                         2
% 1.66/1.04  --comb_inst_mult                        10
% 1.66/1.04  
% 1.66/1.04  ------ Debug Options
% 1.66/1.04  
% 1.66/1.04  --dbg_backtrace                         false
% 1.66/1.04  --dbg_dump_prop_clauses                 false
% 1.66/1.04  --dbg_dump_prop_clauses_file            -
% 1.66/1.04  --dbg_out_stat                          false
% 1.66/1.04  ------ Parsing...
% 1.66/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.66/1.04  
% 1.66/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.66/1.04  
% 1.66/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.66/1.04  
% 1.66/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.66/1.04  ------ Proving...
% 1.66/1.04  ------ Problem Properties 
% 1.66/1.04  
% 1.66/1.04  
% 1.66/1.04  clauses                                 23
% 1.66/1.04  conjectures                             4
% 1.66/1.04  EPR                                     2
% 1.66/1.04  Horn                                    20
% 1.66/1.04  unary                                   4
% 1.66/1.04  binary                                  6
% 1.66/1.04  lits                                    66
% 1.66/1.04  lits eq                                 11
% 1.66/1.04  fd_pure                                 0
% 1.66/1.04  fd_pseudo                               0
% 1.66/1.04  fd_cond                                 0
% 1.66/1.04  fd_pseudo_cond                          7
% 1.66/1.04  AC symbols                              0
% 1.66/1.04  
% 1.66/1.04  ------ Schedule dynamic 5 is on 
% 1.66/1.04  
% 1.66/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.66/1.04  
% 1.66/1.04  
% 1.66/1.04  ------ 
% 1.66/1.04  Current options:
% 1.66/1.04  ------ 
% 1.66/1.04  
% 1.66/1.04  ------ Input Options
% 1.66/1.04  
% 1.66/1.04  --out_options                           all
% 1.66/1.04  --tptp_safe_out                         true
% 1.66/1.04  --problem_path                          ""
% 1.66/1.04  --include_path                          ""
% 1.66/1.04  --clausifier                            res/vclausify_rel
% 1.66/1.04  --clausifier_options                    --mode clausify
% 1.66/1.04  --stdin                                 false
% 1.66/1.04  --stats_out                             all
% 1.66/1.04  
% 1.66/1.04  ------ General Options
% 1.66/1.04  
% 1.66/1.04  --fof                                   false
% 1.66/1.04  --time_out_real                         305.
% 1.66/1.04  --time_out_virtual                      -1.
% 1.66/1.04  --symbol_type_check                     false
% 1.66/1.04  --clausify_out                          false
% 1.66/1.04  --sig_cnt_out                           false
% 1.66/1.04  --trig_cnt_out                          false
% 1.66/1.04  --trig_cnt_out_tolerance                1.
% 1.66/1.04  --trig_cnt_out_sk_spl                   false
% 1.66/1.04  --abstr_cl_out                          false
% 1.66/1.04  
% 1.66/1.04  ------ Global Options
% 1.66/1.04  
% 1.66/1.04  --schedule                              default
% 1.66/1.04  --add_important_lit                     false
% 1.66/1.04  --prop_solver_per_cl                    1000
% 1.66/1.04  --min_unsat_core                        false
% 1.66/1.04  --soft_assumptions                      false
% 1.66/1.04  --soft_lemma_size                       3
% 1.66/1.04  --prop_impl_unit_size                   0
% 1.66/1.04  --prop_impl_unit                        []
% 1.66/1.04  --share_sel_clauses                     true
% 1.66/1.04  --reset_solvers                         false
% 1.66/1.04  --bc_imp_inh                            [conj_cone]
% 1.66/1.04  --conj_cone_tolerance                   3.
% 1.66/1.04  --extra_neg_conj                        none
% 1.66/1.04  --large_theory_mode                     true
% 1.66/1.04  --prolific_symb_bound                   200
% 1.66/1.04  --lt_threshold                          2000
% 1.66/1.04  --clause_weak_htbl                      true
% 1.66/1.04  --gc_record_bc_elim                     false
% 1.66/1.04  
% 1.66/1.04  ------ Preprocessing Options
% 1.66/1.04  
% 1.66/1.04  --preprocessing_flag                    true
% 1.66/1.04  --time_out_prep_mult                    0.1
% 1.66/1.04  --splitting_mode                        input
% 1.66/1.04  --splitting_grd                         true
% 1.66/1.04  --splitting_cvd                         false
% 1.66/1.04  --splitting_cvd_svl                     false
% 1.66/1.04  --splitting_nvd                         32
% 1.66/1.04  --sub_typing                            true
% 1.66/1.04  --prep_gs_sim                           true
% 1.66/1.04  --prep_unflatten                        true
% 1.66/1.04  --prep_res_sim                          true
% 1.66/1.04  --prep_upred                            true
% 1.66/1.04  --prep_sem_filter                       exhaustive
% 1.66/1.04  --prep_sem_filter_out                   false
% 1.66/1.04  --pred_elim                             true
% 1.66/1.04  --res_sim_input                         true
% 1.66/1.04  --eq_ax_congr_red                       true
% 1.66/1.04  --pure_diseq_elim                       true
% 1.66/1.04  --brand_transform                       false
% 1.66/1.04  --non_eq_to_eq                          false
% 1.66/1.04  --prep_def_merge                        true
% 1.66/1.04  --prep_def_merge_prop_impl              false
% 1.66/1.04  --prep_def_merge_mbd                    true
% 1.66/1.04  --prep_def_merge_tr_red                 false
% 1.66/1.04  --prep_def_merge_tr_cl                  false
% 1.66/1.04  --smt_preprocessing                     true
% 1.66/1.04  --smt_ac_axioms                         fast
% 1.66/1.04  --preprocessed_out                      false
% 1.66/1.04  --preprocessed_stats                    false
% 1.66/1.04  
% 1.66/1.04  ------ Abstraction refinement Options
% 1.66/1.04  
% 1.66/1.04  --abstr_ref                             []
% 1.66/1.04  --abstr_ref_prep                        false
% 1.66/1.04  --abstr_ref_until_sat                   false
% 1.66/1.04  --abstr_ref_sig_restrict                funpre
% 1.66/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.66/1.04  --abstr_ref_under                       []
% 1.66/1.04  
% 1.66/1.04  ------ SAT Options
% 1.66/1.04  
% 1.66/1.04  --sat_mode                              false
% 1.66/1.04  --sat_fm_restart_options                ""
% 1.66/1.04  --sat_gr_def                            false
% 1.66/1.04  --sat_epr_types                         true
% 1.66/1.04  --sat_non_cyclic_types                  false
% 1.66/1.04  --sat_finite_models                     false
% 1.66/1.04  --sat_fm_lemmas                         false
% 1.66/1.04  --sat_fm_prep                           false
% 1.66/1.04  --sat_fm_uc_incr                        true
% 1.66/1.04  --sat_out_model                         small
% 1.66/1.04  --sat_out_clauses                       false
% 1.66/1.04  
% 1.66/1.04  ------ QBF Options
% 1.66/1.04  
% 1.66/1.04  --qbf_mode                              false
% 1.66/1.04  --qbf_elim_univ                         false
% 1.66/1.04  --qbf_dom_inst                          none
% 1.66/1.04  --qbf_dom_pre_inst                      false
% 1.66/1.04  --qbf_sk_in                             false
% 1.66/1.04  --qbf_pred_elim                         true
% 1.66/1.04  --qbf_split                             512
% 1.66/1.04  
% 1.66/1.04  ------ BMC1 Options
% 1.66/1.04  
% 1.66/1.04  --bmc1_incremental                      false
% 1.66/1.04  --bmc1_axioms                           reachable_all
% 1.66/1.04  --bmc1_min_bound                        0
% 1.66/1.04  --bmc1_max_bound                        -1
% 1.66/1.04  --bmc1_max_bound_default                -1
% 1.66/1.04  --bmc1_symbol_reachability              true
% 1.66/1.04  --bmc1_property_lemmas                  false
% 1.66/1.04  --bmc1_k_induction                      false
% 1.66/1.04  --bmc1_non_equiv_states                 false
% 1.66/1.04  --bmc1_deadlock                         false
% 1.66/1.04  --bmc1_ucm                              false
% 1.66/1.04  --bmc1_add_unsat_core                   none
% 1.66/1.04  --bmc1_unsat_core_children              false
% 1.66/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.66/1.04  --bmc1_out_stat                         full
% 1.66/1.04  --bmc1_ground_init                      false
% 1.66/1.04  --bmc1_pre_inst_next_state              false
% 1.66/1.04  --bmc1_pre_inst_state                   false
% 1.66/1.04  --bmc1_pre_inst_reach_state             false
% 1.66/1.04  --bmc1_out_unsat_core                   false
% 1.66/1.04  --bmc1_aig_witness_out                  false
% 1.66/1.04  --bmc1_verbose                          false
% 1.66/1.04  --bmc1_dump_clauses_tptp                false
% 1.66/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.66/1.04  --bmc1_dump_file                        -
% 1.66/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.66/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.66/1.04  --bmc1_ucm_extend_mode                  1
% 1.66/1.04  --bmc1_ucm_init_mode                    2
% 1.66/1.04  --bmc1_ucm_cone_mode                    none
% 1.66/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.66/1.04  --bmc1_ucm_relax_model                  4
% 1.66/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.66/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.66/1.04  --bmc1_ucm_layered_model                none
% 1.66/1.04  --bmc1_ucm_max_lemma_size               10
% 1.66/1.04  
% 1.66/1.04  ------ AIG Options
% 1.66/1.04  
% 1.66/1.04  --aig_mode                              false
% 1.66/1.04  
% 1.66/1.04  ------ Instantiation Options
% 1.66/1.04  
% 1.66/1.04  --instantiation_flag                    true
% 1.66/1.04  --inst_sos_flag                         false
% 1.66/1.04  --inst_sos_phase                        true
% 1.66/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.66/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.66/1.04  --inst_lit_sel_side                     none
% 1.66/1.04  --inst_solver_per_active                1400
% 1.66/1.04  --inst_solver_calls_frac                1.
% 1.66/1.04  --inst_passive_queue_type               priority_queues
% 1.66/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.66/1.04  --inst_passive_queues_freq              [25;2]
% 1.66/1.04  --inst_dismatching                      true
% 1.66/1.04  --inst_eager_unprocessed_to_passive     true
% 1.66/1.04  --inst_prop_sim_given                   true
% 1.66/1.04  --inst_prop_sim_new                     false
% 1.66/1.04  --inst_subs_new                         false
% 1.66/1.04  --inst_eq_res_simp                      false
% 1.66/1.04  --inst_subs_given                       false
% 1.66/1.04  --inst_orphan_elimination               true
% 1.66/1.04  --inst_learning_loop_flag               true
% 1.66/1.04  --inst_learning_start                   3000
% 1.66/1.04  --inst_learning_factor                  2
% 1.66/1.04  --inst_start_prop_sim_after_learn       3
% 1.66/1.04  --inst_sel_renew                        solver
% 1.66/1.04  --inst_lit_activity_flag                true
% 1.66/1.04  --inst_restr_to_given                   false
% 1.66/1.04  --inst_activity_threshold               500
% 1.66/1.04  --inst_out_proof                        true
% 1.66/1.04  
% 1.66/1.04  ------ Resolution Options
% 1.66/1.04  
% 1.66/1.04  --resolution_flag                       false
% 1.66/1.04  --res_lit_sel                           adaptive
% 1.66/1.04  --res_lit_sel_side                      none
% 1.66/1.04  --res_ordering                          kbo
% 1.66/1.04  --res_to_prop_solver                    active
% 1.66/1.04  --res_prop_simpl_new                    false
% 1.66/1.04  --res_prop_simpl_given                  true
% 1.66/1.04  --res_passive_queue_type                priority_queues
% 1.66/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.66/1.04  --res_passive_queues_freq               [15;5]
% 1.66/1.04  --res_forward_subs                      full
% 1.66/1.04  --res_backward_subs                     full
% 1.66/1.04  --res_forward_subs_resolution           true
% 1.66/1.04  --res_backward_subs_resolution          true
% 1.66/1.04  --res_orphan_elimination                true
% 1.66/1.04  --res_time_limit                        2.
% 1.66/1.04  --res_out_proof                         true
% 1.66/1.04  
% 1.66/1.04  ------ Superposition Options
% 1.66/1.04  
% 1.66/1.04  --superposition_flag                    true
% 1.66/1.04  --sup_passive_queue_type                priority_queues
% 1.66/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.66/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.66/1.04  --demod_completeness_check              fast
% 1.66/1.04  --demod_use_ground                      true
% 1.66/1.04  --sup_to_prop_solver                    passive
% 1.66/1.04  --sup_prop_simpl_new                    true
% 1.66/1.04  --sup_prop_simpl_given                  true
% 1.66/1.04  --sup_fun_splitting                     false
% 1.66/1.04  --sup_smt_interval                      50000
% 1.66/1.04  
% 1.66/1.04  ------ Superposition Simplification Setup
% 1.66/1.04  
% 1.66/1.04  --sup_indices_passive                   []
% 1.66/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.66/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.04  --sup_full_bw                           [BwDemod]
% 1.66/1.04  --sup_immed_triv                        [TrivRules]
% 1.66/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.66/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.04  --sup_immed_bw_main                     []
% 1.66/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.66/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.04  
% 1.66/1.04  ------ Combination Options
% 1.66/1.04  
% 1.66/1.04  --comb_res_mult                         3
% 1.66/1.04  --comb_sup_mult                         2
% 1.66/1.04  --comb_inst_mult                        10
% 1.66/1.04  
% 1.66/1.04  ------ Debug Options
% 1.66/1.04  
% 1.66/1.04  --dbg_backtrace                         false
% 1.66/1.04  --dbg_dump_prop_clauses                 false
% 1.66/1.04  --dbg_dump_prop_clauses_file            -
% 1.66/1.04  --dbg_out_stat                          false
% 1.66/1.04  
% 1.66/1.04  
% 1.66/1.04  
% 1.66/1.04  
% 1.66/1.04  ------ Proving...
% 1.66/1.04  
% 1.66/1.04  
% 1.66/1.04  % SZS status Theorem for theBenchmark.p
% 1.66/1.04  
% 1.66/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 1.66/1.04  
% 1.66/1.04  fof(f9,conjecture,(
% 1.66/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 1.66/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/1.04  
% 1.66/1.04  fof(f10,negated_conjecture,(
% 1.66/1.04    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 1.66/1.04    inference(negated_conjecture,[],[f9])).
% 1.66/1.04  
% 1.66/1.04  fof(f21,plain,(
% 1.66/1.04    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.66/1.04    inference(ennf_transformation,[],[f10])).
% 1.66/1.04  
% 1.66/1.04  fof(f22,plain,(
% 1.66/1.04    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.66/1.04    inference(flattening,[],[f21])).
% 1.66/1.04  
% 1.66/1.04  fof(f41,plain,(
% 1.66/1.04    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_funct_1(k5_relat_1(k2_funct_1(sK9),sK9),sK8) != sK8 | k1_funct_1(sK9,k1_funct_1(k2_funct_1(sK9),sK8)) != sK8) & r2_hidden(sK8,k2_relat_1(sK9)) & v2_funct_1(sK9) & v1_funct_1(sK9) & v1_relat_1(sK9))),
% 1.66/1.04    introduced(choice_axiom,[])).
% 1.66/1.04  
% 1.66/1.04  fof(f42,plain,(
% 1.66/1.04    (k1_funct_1(k5_relat_1(k2_funct_1(sK9),sK9),sK8) != sK8 | k1_funct_1(sK9,k1_funct_1(k2_funct_1(sK9),sK8)) != sK8) & r2_hidden(sK8,k2_relat_1(sK9)) & v2_funct_1(sK9) & v1_funct_1(sK9) & v1_relat_1(sK9)),
% 1.66/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f22,f41])).
% 1.66/1.04  
% 1.66/1.04  fof(f64,plain,(
% 1.66/1.04    v1_funct_1(sK9)),
% 1.66/1.04    inference(cnf_transformation,[],[f42])).
% 1.66/1.04  
% 1.66/1.04  fof(f66,plain,(
% 1.66/1.04    r2_hidden(sK8,k2_relat_1(sK9))),
% 1.66/1.04    inference(cnf_transformation,[],[f42])).
% 1.66/1.04  
% 1.66/1.04  fof(f2,axiom,(
% 1.66/1.04    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.66/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/1.04  
% 1.66/1.04  fof(f29,plain,(
% 1.66/1.04    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.66/1.04    inference(nnf_transformation,[],[f2])).
% 1.66/1.04  
% 1.66/1.04  fof(f30,plain,(
% 1.66/1.04    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.66/1.04    inference(rectify,[],[f29])).
% 1.66/1.04  
% 1.66/1.04  fof(f33,plain,(
% 1.66/1.04    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 1.66/1.04    introduced(choice_axiom,[])).
% 1.66/1.04  
% 1.66/1.04  fof(f32,plain,(
% 1.66/1.04    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0))) )),
% 1.66/1.04    introduced(choice_axiom,[])).
% 1.66/1.04  
% 1.66/1.04  fof(f31,plain,(
% 1.66/1.04    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.66/1.04    introduced(choice_axiom,[])).
% 1.66/1.04  
% 1.66/1.04  fof(f34,plain,(
% 1.66/1.04    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.66/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 1.66/1.04  
% 1.66/1.04  fof(f47,plain,(
% 1.66/1.04    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.66/1.04    inference(cnf_transformation,[],[f34])).
% 1.66/1.04  
% 1.66/1.04  fof(f71,plain,(
% 1.66/1.04    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.66/1.04    inference(equality_resolution,[],[f47])).
% 1.66/1.04  
% 1.66/1.04  fof(f8,axiom,(
% 1.66/1.04    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.66/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/1.04  
% 1.66/1.04  fof(f19,plain,(
% 1.66/1.04    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.66/1.04    inference(ennf_transformation,[],[f8])).
% 1.66/1.04  
% 1.66/1.04  fof(f20,plain,(
% 1.66/1.04    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.66/1.04    inference(flattening,[],[f19])).
% 1.66/1.04  
% 1.66/1.04  fof(f39,plain,(
% 1.66/1.04    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.66/1.04    inference(nnf_transformation,[],[f20])).
% 1.66/1.04  
% 1.66/1.04  fof(f40,plain,(
% 1.66/1.04    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.66/1.04    inference(flattening,[],[f39])).
% 1.66/1.04  
% 1.66/1.04  fof(f61,plain,(
% 1.66/1.04    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.66/1.04    inference(cnf_transformation,[],[f40])).
% 1.66/1.04  
% 1.66/1.04  fof(f63,plain,(
% 1.66/1.04    v1_relat_1(sK9)),
% 1.66/1.04    inference(cnf_transformation,[],[f42])).
% 1.66/1.04  
% 1.66/1.04  fof(f62,plain,(
% 1.66/1.04    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.66/1.04    inference(cnf_transformation,[],[f40])).
% 1.66/1.04  
% 1.66/1.04  fof(f74,plain,(
% 1.66/1.04    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.66/1.04    inference(equality_resolution,[],[f62])).
% 1.66/1.04  
% 1.66/1.04  fof(f3,axiom,(
% 1.66/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 1.66/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/1.04  
% 1.66/1.04  fof(f11,plain,(
% 1.66/1.04    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/1.04    inference(ennf_transformation,[],[f3])).
% 1.66/1.04  
% 1.66/1.04  fof(f35,plain,(
% 1.66/1.04    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/1.04    inference(nnf_transformation,[],[f11])).
% 1.66/1.04  
% 1.66/1.04  fof(f36,plain,(
% 1.66/1.04    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/1.04    inference(rectify,[],[f35])).
% 1.66/1.04  
% 1.66/1.04  fof(f37,plain,(
% 1.66/1.04    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1))))),
% 1.66/1.04    introduced(choice_axiom,[])).
% 1.66/1.04  
% 1.66/1.04  fof(f38,plain,(
% 1.66/1.04    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ((~r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f36,f37])).
% 1.66/1.04  
% 1.66/1.04  fof(f52,plain,(
% 1.66/1.04    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0) | k4_relat_1(X0) != X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.66/1.04    inference(cnf_transformation,[],[f38])).
% 1.66/1.04  
% 1.66/1.04  fof(f72,plain,(
% 1.66/1.04    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.66/1.04    inference(equality_resolution,[],[f52])).
% 1.66/1.04  
% 1.66/1.04  fof(f4,axiom,(
% 1.66/1.04    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.66/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/1.04  
% 1.66/1.04  fof(f12,plain,(
% 1.66/1.04    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.66/1.04    inference(ennf_transformation,[],[f4])).
% 1.66/1.04  
% 1.66/1.04  fof(f55,plain,(
% 1.66/1.04    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.66/1.04    inference(cnf_transformation,[],[f12])).
% 1.66/1.04  
% 1.66/1.04  fof(f1,axiom,(
% 1.66/1.04    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.66/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/1.04  
% 1.66/1.04  fof(f23,plain,(
% 1.66/1.04    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.66/1.04    inference(nnf_transformation,[],[f1])).
% 1.66/1.04  
% 1.66/1.04  fof(f24,plain,(
% 1.66/1.04    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.66/1.04    inference(rectify,[],[f23])).
% 1.66/1.04  
% 1.66/1.04  fof(f27,plain,(
% 1.66/1.04    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0))),
% 1.66/1.04    introduced(choice_axiom,[])).
% 1.66/1.04  
% 1.66/1.04  fof(f26,plain,(
% 1.66/1.04    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0))) )),
% 1.66/1.04    introduced(choice_axiom,[])).
% 1.66/1.04  
% 1.66/1.04  fof(f25,plain,(
% 1.66/1.04    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 1.66/1.04    introduced(choice_axiom,[])).
% 1.66/1.04  
% 1.66/1.04  fof(f28,plain,(
% 1.66/1.04    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.66/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 1.66/1.04  
% 1.66/1.04  fof(f44,plain,(
% 1.66/1.04    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.66/1.04    inference(cnf_transformation,[],[f28])).
% 1.66/1.04  
% 1.66/1.04  fof(f68,plain,(
% 1.66/1.04    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 1.66/1.04    inference(equality_resolution,[],[f44])).
% 1.66/1.04  
% 1.66/1.04  fof(f7,axiom,(
% 1.66/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 1.66/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/1.04  
% 1.66/1.04  fof(f17,plain,(
% 1.66/1.04    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.66/1.04    inference(ennf_transformation,[],[f7])).
% 1.66/1.04  
% 1.66/1.04  fof(f18,plain,(
% 1.66/1.04    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.66/1.04    inference(flattening,[],[f17])).
% 1.66/1.04  
% 1.66/1.04  fof(f59,plain,(
% 1.66/1.04    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.66/1.04    inference(cnf_transformation,[],[f18])).
% 1.66/1.04  
% 1.66/1.04  fof(f5,axiom,(
% 1.66/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.66/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/1.04  
% 1.66/1.04  fof(f13,plain,(
% 1.66/1.04    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.66/1.04    inference(ennf_transformation,[],[f5])).
% 1.66/1.04  
% 1.66/1.04  fof(f14,plain,(
% 1.66/1.04    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.66/1.04    inference(flattening,[],[f13])).
% 1.66/1.04  
% 1.66/1.04  fof(f56,plain,(
% 1.66/1.04    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.66/1.04    inference(cnf_transformation,[],[f14])).
% 1.66/1.04  
% 1.66/1.04  fof(f65,plain,(
% 1.66/1.04    v2_funct_1(sK9)),
% 1.66/1.04    inference(cnf_transformation,[],[f42])).
% 1.66/1.04  
% 1.66/1.04  fof(f6,axiom,(
% 1.66/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.66/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.66/1.04  
% 1.66/1.04  fof(f15,plain,(
% 1.66/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.66/1.04    inference(ennf_transformation,[],[f6])).
% 1.66/1.04  
% 1.66/1.04  fof(f16,plain,(
% 1.66/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.66/1.04    inference(flattening,[],[f15])).
% 1.66/1.04  
% 1.66/1.04  fof(f58,plain,(
% 1.66/1.04    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.66/1.04    inference(cnf_transformation,[],[f16])).
% 1.66/1.04  
% 1.66/1.04  fof(f43,plain,(
% 1.66/1.04    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.66/1.04    inference(cnf_transformation,[],[f28])).
% 1.66/1.04  
% 1.66/1.04  fof(f69,plain,(
% 1.66/1.04    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 1.66/1.04    inference(equality_resolution,[],[f43])).
% 1.66/1.04  
% 1.66/1.04  fof(f67,plain,(
% 1.66/1.04    k1_funct_1(k5_relat_1(k2_funct_1(sK9),sK9),sK8) != sK8 | k1_funct_1(sK9,k1_funct_1(k2_funct_1(sK9),sK8)) != sK8),
% 1.66/1.04    inference(cnf_transformation,[],[f42])).
% 1.66/1.04  
% 1.66/1.04  fof(f51,plain,(
% 1.66/1.04    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1) | k4_relat_1(X0) != X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.66/1.04    inference(cnf_transformation,[],[f38])).
% 1.66/1.04  
% 1.66/1.04  fof(f73,plain,(
% 1.66/1.04    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.66/1.04    inference(equality_resolution,[],[f51])).
% 1.66/1.04  
% 1.66/1.04  cnf(c_23,negated_conjecture,
% 1.66/1.04      ( v1_funct_1(sK9) ),
% 1.66/1.04      inference(cnf_transformation,[],[f64]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_793,plain,
% 1.66/1.04      ( v1_funct_1(sK9) = iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_21,negated_conjecture,
% 1.66/1.04      ( r2_hidden(sK8,k2_relat_1(sK9)) ),
% 1.66/1.04      inference(cnf_transformation,[],[f66]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_794,plain,
% 1.66/1.04      ( r2_hidden(sK8,k2_relat_1(sK9)) = iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_7,plain,
% 1.66/1.04      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 1.66/1.04      | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
% 1.66/1.04      inference(cnf_transformation,[],[f71]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_805,plain,
% 1.66/1.04      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 1.66/1.04      | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) = iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_18,plain,
% 1.66/1.04      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 1.66/1.04      | ~ v1_funct_1(X2)
% 1.66/1.04      | ~ v1_relat_1(X2)
% 1.66/1.04      | k1_funct_1(X2,X0) = X1 ),
% 1.66/1.04      inference(cnf_transformation,[],[f61]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_795,plain,
% 1.66/1.04      ( k1_funct_1(X0,X1) = X2
% 1.66/1.04      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 1.66/1.04      | v1_funct_1(X0) != iProver_top
% 1.66/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1417,plain,
% 1.66/1.04      ( k1_funct_1(X0,sK5(X0,X1)) = X1
% 1.66/1.04      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 1.66/1.04      | v1_funct_1(X0) != iProver_top
% 1.66/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.66/1.04      inference(superposition,[status(thm)],[c_805,c_795]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_5767,plain,
% 1.66/1.04      ( k1_funct_1(sK9,sK5(sK9,sK8)) = sK8
% 1.66/1.04      | v1_funct_1(sK9) != iProver_top
% 1.66/1.04      | v1_relat_1(sK9) != iProver_top ),
% 1.66/1.04      inference(superposition,[status(thm)],[c_794,c_1417]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_24,negated_conjecture,
% 1.66/1.04      ( v1_relat_1(sK9) ),
% 1.66/1.04      inference(cnf_transformation,[],[f63]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_999,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9)
% 1.66/1.04      | ~ r2_hidden(sK8,k2_relat_1(sK9)) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_7]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1021,plain,
% 1.66/1.04      ( ~ r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9)
% 1.66/1.04      | ~ v1_funct_1(sK9)
% 1.66/1.04      | ~ v1_relat_1(sK9)
% 1.66/1.04      | k1_funct_1(sK9,sK5(sK9,sK8)) = sK8 ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_18]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_6009,plain,
% 1.66/1.04      ( k1_funct_1(sK9,sK5(sK9,sK8)) = sK8 ),
% 1.66/1.04      inference(global_propositional_subsumption,
% 1.66/1.04                [status(thm)],
% 1.66/1.04                [c_5767,c_24,c_23,c_21,c_999,c_1021]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_17,plain,
% 1.66/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.66/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 1.66/1.04      | ~ v1_funct_1(X1)
% 1.66/1.04      | ~ v1_relat_1(X1) ),
% 1.66/1.04      inference(cnf_transformation,[],[f74]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_796,plain,
% 1.66/1.04      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 1.66/1.04      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 1.66/1.04      | v1_funct_1(X1) != iProver_top
% 1.66/1.04      | v1_relat_1(X1) != iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_6012,plain,
% 1.66/1.04      ( r2_hidden(sK5(sK9,sK8),k1_relat_1(sK9)) != iProver_top
% 1.66/1.04      | r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9) = iProver_top
% 1.66/1.04      | v1_funct_1(sK9) != iProver_top
% 1.66/1.04      | v1_relat_1(sK9) != iProver_top ),
% 1.66/1.04      inference(superposition,[status(thm)],[c_6009,c_796]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_28,plain,
% 1.66/1.04      ( r2_hidden(sK8,k2_relat_1(sK9)) = iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1000,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9) = iProver_top
% 1.66/1.04      | r2_hidden(sK8,k2_relat_1(sK9)) != iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_999]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_6518,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9) = iProver_top ),
% 1.66/1.04      inference(global_propositional_subsumption,
% 1.66/1.04                [status(thm)],
% 1.66/1.04                [c_6012,c_28,c_1000]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_10,plain,
% 1.66/1.04      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 1.66/1.04      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
% 1.66/1.04      | ~ v1_relat_1(X2)
% 1.66/1.04      | ~ v1_relat_1(k4_relat_1(X2)) ),
% 1.66/1.04      inference(cnf_transformation,[],[f72]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_802,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 1.66/1.04      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) = iProver_top
% 1.66/1.04      | v1_relat_1(X2) != iProver_top
% 1.66/1.04      | v1_relat_1(k4_relat_1(X2)) != iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_12,plain,
% 1.66/1.04      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 1.66/1.04      inference(cnf_transformation,[],[f55]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_800,plain,
% 1.66/1.04      ( v1_relat_1(X0) != iProver_top
% 1.66/1.04      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_910,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 1.66/1.04      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2)) = iProver_top
% 1.66/1.04      | v1_relat_1(X2) != iProver_top ),
% 1.66/1.04      inference(forward_subsumption_resolution,
% 1.66/1.04                [status(thm)],
% 1.66/1.04                [c_802,c_800]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_2,plain,
% 1.66/1.04      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 1.66/1.04      inference(cnf_transformation,[],[f68]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_810,plain,
% 1.66/1.04      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 1.66/1.04      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_2059,plain,
% 1.66/1.04      ( r2_hidden(X0,k1_relat_1(k4_relat_1(X1))) = iProver_top
% 1.66/1.04      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 1.66/1.04      | v1_relat_1(X1) != iProver_top ),
% 1.66/1.04      inference(superposition,[status(thm)],[c_910,c_810]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_6525,plain,
% 1.66/1.04      ( r2_hidden(sK8,k1_relat_1(k4_relat_1(sK9))) = iProver_top
% 1.66/1.04      | v1_relat_1(sK9) != iProver_top ),
% 1.66/1.04      inference(superposition,[status(thm)],[c_6518,c_2059]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_25,plain,
% 1.66/1.04      ( v1_relat_1(sK9) = iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_50,plain,
% 1.66/1.04      ( v1_relat_1(X0) != iProver_top
% 1.66/1.04      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_52,plain,
% 1.66/1.04      ( v1_relat_1(k4_relat_1(sK9)) = iProver_top
% 1.66/1.04      | v1_relat_1(sK9) != iProver_top ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_50]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1022,plain,
% 1.66/1.04      ( ~ r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9)
% 1.66/1.04      | r2_hidden(k4_tarski(sK8,sK5(sK9,sK8)),k4_relat_1(sK9))
% 1.66/1.04      | ~ v1_relat_1(k4_relat_1(sK9))
% 1.66/1.04      | ~ v1_relat_1(sK9) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_10]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1023,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(sK5(sK9,sK8),sK8),sK9) != iProver_top
% 1.66/1.04      | r2_hidden(k4_tarski(sK8,sK5(sK9,sK8)),k4_relat_1(sK9)) = iProver_top
% 1.66/1.04      | v1_relat_1(k4_relat_1(sK9)) != iProver_top
% 1.66/1.04      | v1_relat_1(sK9) != iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_1022]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1114,plain,
% 1.66/1.04      ( ~ r2_hidden(k4_tarski(sK8,sK5(sK9,sK8)),k4_relat_1(sK9))
% 1.66/1.04      | r2_hidden(sK8,k1_relat_1(k4_relat_1(sK9))) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_2]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1115,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(sK8,sK5(sK9,sK8)),k4_relat_1(sK9)) != iProver_top
% 1.66/1.04      | r2_hidden(sK8,k1_relat_1(k4_relat_1(sK9))) = iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_1114]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_7506,plain,
% 1.66/1.04      ( r2_hidden(sK8,k1_relat_1(k4_relat_1(sK9))) = iProver_top ),
% 1.66/1.04      inference(global_propositional_subsumption,
% 1.66/1.04                [status(thm)],
% 1.66/1.04                [c_6525,c_25,c_28,c_52,c_1000,c_1023,c_1115]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_16,plain,
% 1.66/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.66/1.04      | ~ v1_funct_1(X2)
% 1.66/1.04      | ~ v1_funct_1(X1)
% 1.66/1.04      | ~ v1_relat_1(X1)
% 1.66/1.04      | ~ v1_relat_1(X2)
% 1.66/1.04      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 1.66/1.04      inference(cnf_transformation,[],[f59]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_797,plain,
% 1.66/1.04      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 1.66/1.04      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 1.66/1.04      | v1_funct_1(X0) != iProver_top
% 1.66/1.04      | v1_funct_1(X1) != iProver_top
% 1.66/1.04      | v1_relat_1(X0) != iProver_top
% 1.66/1.04      | v1_relat_1(X1) != iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_7511,plain,
% 1.66/1.04      ( k1_funct_1(X0,k1_funct_1(k4_relat_1(sK9),sK8)) = k1_funct_1(k5_relat_1(k4_relat_1(sK9),X0),sK8)
% 1.66/1.04      | v1_funct_1(X0) != iProver_top
% 1.66/1.04      | v1_funct_1(k4_relat_1(sK9)) != iProver_top
% 1.66/1.04      | v1_relat_1(X0) != iProver_top
% 1.66/1.04      | v1_relat_1(k4_relat_1(sK9)) != iProver_top ),
% 1.66/1.04      inference(superposition,[status(thm)],[c_7506,c_797]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_26,plain,
% 1.66/1.04      ( v1_funct_1(sK9) = iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_13,plain,
% 1.66/1.04      ( ~ v1_funct_1(X0)
% 1.66/1.04      | ~ v2_funct_1(X0)
% 1.66/1.04      | ~ v1_relat_1(X0)
% 1.66/1.04      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 1.66/1.04      inference(cnf_transformation,[],[f56]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_22,negated_conjecture,
% 1.66/1.04      ( v2_funct_1(sK9) ),
% 1.66/1.04      inference(cnf_transformation,[],[f65]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_274,plain,
% 1.66/1.04      ( ~ v1_funct_1(X0)
% 1.66/1.04      | ~ v1_relat_1(X0)
% 1.66/1.04      | k2_funct_1(X0) = k4_relat_1(X0)
% 1.66/1.04      | sK9 != X0 ),
% 1.66/1.04      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_275,plain,
% 1.66/1.04      ( ~ v1_funct_1(sK9)
% 1.66/1.04      | ~ v1_relat_1(sK9)
% 1.66/1.04      | k2_funct_1(sK9) = k4_relat_1(sK9) ),
% 1.66/1.04      inference(unflattening,[status(thm)],[c_274]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_48,plain,
% 1.66/1.04      ( ~ v1_funct_1(sK9)
% 1.66/1.04      | ~ v2_funct_1(sK9)
% 1.66/1.04      | ~ v1_relat_1(sK9)
% 1.66/1.04      | k2_funct_1(sK9) = k4_relat_1(sK9) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_13]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_277,plain,
% 1.66/1.04      ( k2_funct_1(sK9) = k4_relat_1(sK9) ),
% 1.66/1.04      inference(global_propositional_subsumption,
% 1.66/1.04                [status(thm)],
% 1.66/1.04                [c_275,c_24,c_23,c_22,c_48]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_14,plain,
% 1.66/1.04      ( ~ v1_funct_1(X0)
% 1.66/1.04      | v1_funct_1(k2_funct_1(X0))
% 1.66/1.04      | ~ v1_relat_1(X0) ),
% 1.66/1.04      inference(cnf_transformation,[],[f58]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_799,plain,
% 1.66/1.04      ( v1_funct_1(X0) != iProver_top
% 1.66/1.04      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 1.66/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1410,plain,
% 1.66/1.04      ( v1_funct_1(k4_relat_1(sK9)) = iProver_top
% 1.66/1.04      | v1_funct_1(sK9) != iProver_top
% 1.66/1.04      | v1_relat_1(sK9) != iProver_top ),
% 1.66/1.04      inference(superposition,[status(thm)],[c_277,c_799]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_12164,plain,
% 1.66/1.04      ( v1_relat_1(X0) != iProver_top
% 1.66/1.04      | k1_funct_1(X0,k1_funct_1(k4_relat_1(sK9),sK8)) = k1_funct_1(k5_relat_1(k4_relat_1(sK9),X0),sK8)
% 1.66/1.04      | v1_funct_1(X0) != iProver_top ),
% 1.66/1.04      inference(global_propositional_subsumption,
% 1.66/1.04                [status(thm)],
% 1.66/1.04                [c_7511,c_25,c_26,c_52,c_1410]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_12165,plain,
% 1.66/1.04      ( k1_funct_1(X0,k1_funct_1(k4_relat_1(sK9),sK8)) = k1_funct_1(k5_relat_1(k4_relat_1(sK9),X0),sK8)
% 1.66/1.04      | v1_funct_1(X0) != iProver_top
% 1.66/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.66/1.04      inference(renaming,[status(thm)],[c_12164]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_12174,plain,
% 1.66/1.04      ( k1_funct_1(sK9,k1_funct_1(k4_relat_1(sK9),sK8)) = k1_funct_1(k5_relat_1(k4_relat_1(sK9),sK9),sK8)
% 1.66/1.04      | v1_relat_1(sK9) != iProver_top ),
% 1.66/1.04      inference(superposition,[status(thm)],[c_793,c_12165]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_7524,plain,
% 1.66/1.04      ( k1_funct_1(sK9,k1_funct_1(k4_relat_1(sK9),sK8)) = k1_funct_1(k5_relat_1(k4_relat_1(sK9),sK9),sK8)
% 1.66/1.04      | v1_funct_1(k4_relat_1(sK9)) != iProver_top
% 1.66/1.04      | v1_funct_1(sK9) != iProver_top
% 1.66/1.04      | v1_relat_1(k4_relat_1(sK9)) != iProver_top
% 1.66/1.04      | v1_relat_1(sK9) != iProver_top ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_7511]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_12297,plain,
% 1.66/1.04      ( k1_funct_1(sK9,k1_funct_1(k4_relat_1(sK9),sK8)) = k1_funct_1(k5_relat_1(k4_relat_1(sK9),sK9),sK8) ),
% 1.66/1.04      inference(global_propositional_subsumption,
% 1.66/1.04                [status(thm)],
% 1.66/1.04                [c_12174,c_25,c_26,c_52,c_1410,c_7524]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_3,plain,
% 1.66/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.66/1.04      | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
% 1.66/1.04      inference(cnf_transformation,[],[f69]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_809,plain,
% 1.66/1.04      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 1.66/1.04      | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) = iProver_top ),
% 1.66/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1538,plain,
% 1.66/1.04      ( k1_funct_1(X0,X1) = sK2(X0,X1)
% 1.66/1.04      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 1.66/1.04      | v1_funct_1(X0) != iProver_top
% 1.66/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.66/1.04      inference(superposition,[status(thm)],[c_809,c_795]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_7652,plain,
% 1.66/1.04      ( k1_funct_1(k4_relat_1(sK9),sK8) = sK2(k4_relat_1(sK9),sK8)
% 1.66/1.04      | v1_funct_1(k4_relat_1(sK9)) != iProver_top
% 1.66/1.04      | v1_relat_1(k4_relat_1(sK9)) != iProver_top ),
% 1.66/1.04      inference(superposition,[status(thm)],[c_7506,c_1538]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_51,plain,
% 1.66/1.04      ( v1_relat_1(k4_relat_1(sK9)) | ~ v1_relat_1(sK9) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1411,plain,
% 1.66/1.04      ( v1_funct_1(k4_relat_1(sK9))
% 1.66/1.04      | ~ v1_funct_1(sK9)
% 1.66/1.04      | ~ v1_relat_1(sK9) ),
% 1.66/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_1410]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1139,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(sK8,sK2(X0,sK8)),X0)
% 1.66/1.04      | ~ r2_hidden(sK8,k1_relat_1(X0)) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1467,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(sK8,sK2(k4_relat_1(sK9),sK8)),k4_relat_1(sK9))
% 1.66/1.04      | ~ r2_hidden(sK8,k1_relat_1(k4_relat_1(sK9))) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_1139]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_2238,plain,
% 1.66/1.04      ( ~ r2_hidden(k4_tarski(sK8,sK2(X0,sK8)),X0)
% 1.66/1.04      | ~ v1_funct_1(X0)
% 1.66/1.04      | ~ v1_relat_1(X0)
% 1.66/1.04      | k1_funct_1(X0,sK8) = sK2(X0,sK8) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_18]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_6159,plain,
% 1.66/1.04      ( ~ r2_hidden(k4_tarski(sK8,sK2(k4_relat_1(sK9),sK8)),k4_relat_1(sK9))
% 1.66/1.04      | ~ v1_funct_1(k4_relat_1(sK9))
% 1.66/1.04      | ~ v1_relat_1(k4_relat_1(sK9))
% 1.66/1.04      | k1_funct_1(k4_relat_1(sK9),sK8) = sK2(k4_relat_1(sK9),sK8) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_2238]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_9223,plain,
% 1.66/1.04      ( k1_funct_1(k4_relat_1(sK9),sK8) = sK2(k4_relat_1(sK9),sK8) ),
% 1.66/1.04      inference(global_propositional_subsumption,
% 1.66/1.04                [status(thm)],
% 1.66/1.04                [c_7652,c_24,c_23,c_21,c_51,c_999,c_1022,c_1114,c_1411,
% 1.66/1.04                 c_1467,c_6159]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_20,negated_conjecture,
% 1.66/1.04      ( k1_funct_1(k5_relat_1(k2_funct_1(sK9),sK9),sK8) != sK8
% 1.66/1.04      | k1_funct_1(sK9,k1_funct_1(k2_funct_1(sK9),sK8)) != sK8 ),
% 1.66/1.04      inference(cnf_transformation,[],[f67]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_853,plain,
% 1.66/1.04      ( k1_funct_1(k5_relat_1(k4_relat_1(sK9),sK9),sK8) != sK8
% 1.66/1.04      | k1_funct_1(sK9,k1_funct_1(k4_relat_1(sK9),sK8)) != sK8 ),
% 1.66/1.04      inference(light_normalisation,[status(thm)],[c_20,c_277]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_9228,plain,
% 1.66/1.04      ( k1_funct_1(k5_relat_1(k4_relat_1(sK9),sK9),sK8) != sK8
% 1.66/1.04      | k1_funct_1(sK9,sK2(k4_relat_1(sK9),sK8)) != sK8 ),
% 1.66/1.04      inference(demodulation,[status(thm)],[c_9223,c_853]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_1138,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(sK8,k1_funct_1(X0,sK8)),X0)
% 1.66/1.04      | ~ r2_hidden(sK8,k1_relat_1(X0))
% 1.66/1.04      | ~ v1_funct_1(X0)
% 1.66/1.04      | ~ v1_relat_1(X0) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_17]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_2162,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(sK8,k1_funct_1(k4_relat_1(X0),sK8)),k4_relat_1(X0))
% 1.66/1.04      | ~ r2_hidden(sK8,k1_relat_1(k4_relat_1(X0)))
% 1.66/1.04      | ~ v1_funct_1(k4_relat_1(X0))
% 1.66/1.04      | ~ v1_relat_1(k4_relat_1(X0)) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_1138]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_2165,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(sK8,k1_funct_1(k4_relat_1(sK9),sK8)),k4_relat_1(sK9))
% 1.66/1.04      | ~ r2_hidden(sK8,k1_relat_1(k4_relat_1(sK9)))
% 1.66/1.04      | ~ v1_funct_1(k4_relat_1(sK9))
% 1.66/1.04      | ~ v1_relat_1(k4_relat_1(sK9)) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_2162]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_11,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(X0,X1),X2)
% 1.66/1.04      | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(X2))
% 1.66/1.04      | ~ v1_relat_1(X2)
% 1.66/1.04      | ~ v1_relat_1(k4_relat_1(X2)) ),
% 1.66/1.04      inference(cnf_transformation,[],[f73]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_2163,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(X0),sK8),sK8),X0)
% 1.66/1.04      | ~ r2_hidden(k4_tarski(sK8,k1_funct_1(k4_relat_1(X0),sK8)),k4_relat_1(X0))
% 1.66/1.04      | ~ v1_relat_1(X0)
% 1.66/1.04      | ~ v1_relat_1(k4_relat_1(X0)) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_11]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_2169,plain,
% 1.66/1.04      ( r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(sK9),sK8),sK8),sK9)
% 1.66/1.04      | ~ r2_hidden(k4_tarski(sK8,k1_funct_1(k4_relat_1(sK9),sK8)),k4_relat_1(sK9))
% 1.66/1.04      | ~ v1_relat_1(k4_relat_1(sK9))
% 1.66/1.04      | ~ v1_relat_1(sK9) ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_2163]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_6134,plain,
% 1.66/1.04      ( ~ r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(X0),sK8),sK8),X0)
% 1.66/1.04      | ~ v1_funct_1(X0)
% 1.66/1.04      | ~ v1_relat_1(X0)
% 1.66/1.04      | k1_funct_1(X0,k1_funct_1(k4_relat_1(X0),sK8)) = sK8 ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_18]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_6141,plain,
% 1.66/1.04      ( ~ r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(sK9),sK8),sK8),sK9)
% 1.66/1.04      | ~ v1_funct_1(sK9)
% 1.66/1.04      | ~ v1_relat_1(sK9)
% 1.66/1.04      | k1_funct_1(sK9,k1_funct_1(k4_relat_1(sK9),sK8)) = sK8 ),
% 1.66/1.04      inference(instantiation,[status(thm)],[c_6134]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_9552,plain,
% 1.66/1.04      ( k1_funct_1(k5_relat_1(k4_relat_1(sK9),sK9),sK8) != sK8 ),
% 1.66/1.04      inference(global_propositional_subsumption,
% 1.66/1.04                [status(thm)],
% 1.66/1.04                [c_9228,c_24,c_23,c_21,c_51,c_853,c_999,c_1022,c_1114,
% 1.66/1.04                 c_1411,c_2165,c_2169,c_6141]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(c_12300,plain,
% 1.66/1.04      ( k1_funct_1(sK9,k1_funct_1(k4_relat_1(sK9),sK8)) != sK8 ),
% 1.66/1.04      inference(demodulation,[status(thm)],[c_12297,c_9552]) ).
% 1.66/1.04  
% 1.66/1.04  cnf(contradiction,plain,
% 1.66/1.04      ( $false ),
% 1.66/1.04      inference(minisat,
% 1.66/1.04                [status(thm)],
% 1.66/1.04                [c_12300,c_6141,c_2169,c_2165,c_1411,c_1114,c_1022,c_999,
% 1.66/1.04                 c_51,c_21,c_23,c_24]) ).
% 1.66/1.04  
% 1.66/1.04  
% 1.66/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.66/1.04  
% 1.66/1.04  ------                               Statistics
% 1.66/1.04  
% 1.66/1.04  ------ General
% 1.66/1.04  
% 1.66/1.04  abstr_ref_over_cycles:                  0
% 1.66/1.04  abstr_ref_under_cycles:                 0
% 1.66/1.04  gc_basic_clause_elim:                   0
% 1.66/1.04  forced_gc_time:                         0
% 1.66/1.04  parsing_time:                           0.015
% 1.66/1.04  unif_index_cands_time:                  0.
% 1.66/1.04  unif_index_add_time:                    0.
% 1.66/1.04  orderings_time:                         0.
% 1.66/1.04  out_proof_time:                         0.01
% 1.66/1.04  total_time:                             0.411
% 1.66/1.04  num_of_symbols:                         52
% 1.66/1.04  num_of_terms:                           14768
% 1.66/1.04  
% 1.66/1.04  ------ Preprocessing
% 1.66/1.04  
% 1.66/1.04  num_of_splits:                          0
% 1.66/1.04  num_of_split_atoms:                     0
% 1.66/1.04  num_of_reused_defs:                     0
% 1.66/1.04  num_eq_ax_congr_red:                    52
% 1.66/1.04  num_of_sem_filtered_clauses:            1
% 1.66/1.04  num_of_subtypes:                        0
% 1.66/1.04  monotx_restored_types:                  0
% 1.66/1.04  sat_num_of_epr_types:                   0
% 1.66/1.04  sat_num_of_non_cyclic_types:            0
% 1.66/1.04  sat_guarded_non_collapsed_types:        0
% 1.66/1.04  num_pure_diseq_elim:                    0
% 1.66/1.04  simp_replaced_by:                       0
% 1.66/1.04  res_preprocessed:                       116
% 1.66/1.04  prep_upred:                             0
% 1.66/1.04  prep_unflattend:                        1
% 1.66/1.04  smt_new_axioms:                         0
% 1.66/1.04  pred_elim_cands:                        3
% 1.66/1.04  pred_elim:                              1
% 1.66/1.04  pred_elim_cl:                           1
% 1.66/1.04  pred_elim_cycles:                       3
% 1.66/1.04  merged_defs:                            0
% 1.66/1.04  merged_defs_ncl:                        0
% 1.66/1.04  bin_hyper_res:                          0
% 1.66/1.04  prep_cycles:                            4
% 1.66/1.04  pred_elim_time:                         0.002
% 1.66/1.04  splitting_time:                         0.
% 1.66/1.04  sem_filter_time:                        0.
% 1.66/1.04  monotx_time:                            0.
% 1.66/1.04  subtype_inf_time:                       0.
% 1.66/1.04  
% 1.66/1.04  ------ Problem properties
% 1.66/1.04  
% 1.66/1.04  clauses:                                23
% 1.66/1.04  conjectures:                            4
% 1.66/1.04  epr:                                    2
% 1.66/1.04  horn:                                   20
% 1.66/1.04  ground:                                 5
% 1.66/1.04  unary:                                  4
% 1.66/1.04  binary:                                 6
% 1.66/1.04  lits:                                   66
% 1.66/1.04  lits_eq:                                11
% 1.66/1.04  fd_pure:                                0
% 1.66/1.04  fd_pseudo:                              0
% 1.66/1.04  fd_cond:                                0
% 1.66/1.04  fd_pseudo_cond:                         7
% 1.66/1.04  ac_symbols:                             0
% 1.66/1.04  
% 1.66/1.04  ------ Propositional Solver
% 1.66/1.04  
% 1.66/1.04  prop_solver_calls:                      27
% 1.66/1.04  prop_fast_solver_calls:                 984
% 1.66/1.04  smt_solver_calls:                       0
% 1.66/1.04  smt_fast_solver_calls:                  0
% 1.66/1.04  prop_num_of_clauses:                    4857
% 1.66/1.04  prop_preprocess_simplified:             9189
% 1.66/1.04  prop_fo_subsumed:                       37
% 1.66/1.04  prop_solver_time:                       0.
% 1.66/1.04  smt_solver_time:                        0.
% 1.66/1.04  smt_fast_solver_time:                   0.
% 1.66/1.04  prop_fast_solver_time:                  0.
% 1.66/1.04  prop_unsat_core_time:                   0.
% 1.66/1.04  
% 1.66/1.04  ------ QBF
% 1.66/1.04  
% 1.66/1.04  qbf_q_res:                              0
% 1.66/1.04  qbf_num_tautologies:                    0
% 1.66/1.04  qbf_prep_cycles:                        0
% 1.66/1.04  
% 1.66/1.04  ------ BMC1
% 1.66/1.04  
% 1.66/1.04  bmc1_current_bound:                     -1
% 1.66/1.04  bmc1_last_solved_bound:                 -1
% 1.66/1.04  bmc1_unsat_core_size:                   -1
% 1.66/1.04  bmc1_unsat_core_parents_size:           -1
% 1.66/1.04  bmc1_merge_next_fun:                    0
% 1.66/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.66/1.04  
% 1.66/1.04  ------ Instantiation
% 1.66/1.04  
% 1.66/1.04  inst_num_of_clauses:                    1102
% 1.66/1.04  inst_num_in_passive:                    235
% 1.66/1.04  inst_num_in_active:                     426
% 1.66/1.04  inst_num_in_unprocessed:                441
% 1.66/1.04  inst_num_of_loops:                      480
% 1.66/1.04  inst_num_of_learning_restarts:          0
% 1.66/1.04  inst_num_moves_active_passive:          52
% 1.66/1.04  inst_lit_activity:                      0
% 1.66/1.04  inst_lit_activity_moves:                0
% 1.66/1.04  inst_num_tautologies:                   0
% 1.66/1.04  inst_num_prop_implied:                  0
% 1.66/1.04  inst_num_existing_simplified:           0
% 1.66/1.04  inst_num_eq_res_simplified:             0
% 1.66/1.04  inst_num_child_elim:                    0
% 1.66/1.04  inst_num_of_dismatching_blockings:      411
% 1.66/1.04  inst_num_of_non_proper_insts:           924
% 1.66/1.04  inst_num_of_duplicates:                 0
% 1.66/1.04  inst_inst_num_from_inst_to_res:         0
% 1.66/1.04  inst_dismatching_checking_time:         0.
% 1.66/1.04  
% 1.66/1.04  ------ Resolution
% 1.66/1.04  
% 1.66/1.04  res_num_of_clauses:                     0
% 1.66/1.04  res_num_in_passive:                     0
% 1.66/1.04  res_num_in_active:                      0
% 1.66/1.04  res_num_of_loops:                       120
% 1.66/1.04  res_forward_subset_subsumed:            32
% 1.66/1.04  res_backward_subset_subsumed:           0
% 1.66/1.04  res_forward_subsumed:                   0
% 1.66/1.04  res_backward_subsumed:                  0
% 1.66/1.04  res_forward_subsumption_resolution:     0
% 1.66/1.04  res_backward_subsumption_resolution:    0
% 1.66/1.04  res_clause_to_clause_subsumption:       1238
% 1.66/1.04  res_orphan_elimination:                 0
% 1.66/1.04  res_tautology_del:                      53
% 1.66/1.04  res_num_eq_res_simplified:              0
% 1.66/1.04  res_num_sel_changes:                    0
% 1.66/1.04  res_moves_from_active_to_pass:          0
% 1.66/1.04  
% 1.66/1.04  ------ Superposition
% 1.66/1.04  
% 1.66/1.04  sup_time_total:                         0.
% 1.66/1.04  sup_time_generating:                    0.
% 1.66/1.04  sup_time_sim_full:                      0.
% 1.66/1.04  sup_time_sim_immed:                     0.
% 1.66/1.04  
% 1.66/1.04  sup_num_of_clauses:                     432
% 1.66/1.04  sup_num_in_active:                      88
% 1.66/1.04  sup_num_in_passive:                     344
% 1.66/1.04  sup_num_of_loops:                       94
% 1.66/1.04  sup_fw_superposition:                   228
% 1.66/1.04  sup_bw_superposition:                   253
% 1.66/1.04  sup_immediate_simplified:               41
% 1.66/1.04  sup_given_eliminated:                   0
% 1.66/1.04  comparisons_done:                       0
% 1.66/1.04  comparisons_avoided:                    0
% 1.66/1.04  
% 1.66/1.04  ------ Simplifications
% 1.66/1.04  
% 1.66/1.04  
% 1.66/1.04  sim_fw_subset_subsumed:                 19
% 1.66/1.04  sim_bw_subset_subsumed:                 5
% 1.66/1.04  sim_fw_subsumed:                        8
% 1.66/1.04  sim_bw_subsumed:                        8
% 1.66/1.04  sim_fw_subsumption_res:                 3
% 1.66/1.04  sim_bw_subsumption_res:                 0
% 1.66/1.04  sim_tautology_del:                      19
% 1.66/1.04  sim_eq_tautology_del:                   7
% 1.66/1.04  sim_eq_res_simp:                        0
% 1.66/1.04  sim_fw_demodulated:                     1
% 1.66/1.04  sim_bw_demodulated:                     6
% 1.66/1.04  sim_light_normalised:                   5
% 1.66/1.04  sim_joinable_taut:                      0
% 1.66/1.04  sim_joinable_simp:                      0
% 1.66/1.04  sim_ac_normalised:                      0
% 1.66/1.04  sim_smt_subsumption:                    0
% 1.66/1.04  
%------------------------------------------------------------------------------
