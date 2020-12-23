%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:43 EST 2020

% Result     : Theorem 7.83s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  135 (1939 expanded)
%              Number of clauses        :   80 ( 608 expanded)
%              Number of leaves         :   16 ( 518 expanded)
%              Depth                    :   21
%              Number of atoms          :  508 (9894 expanded)
%              Number of equality atoms :  278 (4549 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                  & k1_relat_1(X0) = k1_relat_1(X1) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
          & ! [X3] :
              ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(X0) = k1_relat_1(X1) )
     => ( k7_relat_1(X0,sK4) != k7_relat_1(X1,sK4)
        & ! [X3] :
            ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,sK4) )
        & k1_relat_1(X0) = k1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( k7_relat_1(sK3,X2) != k7_relat_1(X0,X2)
            & ! [X3] :
                ( k1_funct_1(sK3,X3) = k1_funct_1(X0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(sK3) = k1_relat_1(X0) )
        & v1_funct_1(sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(sK2,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(sK2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(sK2) = k1_relat_1(X1) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4)
    & ! [X3] :
        ( k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3)
        | ~ r2_hidden(X3,sK4) )
    & k1_relat_1(sK2) = k1_relat_1(sK3)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f39,f38,f37])).

fof(f62,plain,(
    k1_relat_1(sK2) = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
             => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X3] :
                      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                      | ~ r2_hidden(X3,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ( k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2))
                    & r2_hidden(sK0(X0,X1,X2),X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3)
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1)
            & r2_hidden(sK1(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f50,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2))
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_620,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_19,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_619,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1308,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_619])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1328,plain,
    ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1308,c_26])).

cnf(c_1329,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1328])).

cnf(c_1335,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_620,c_1329])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1947,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1335,c_24])).

cnf(c_1033,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_620])).

cnf(c_1041,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1033,c_26])).

cnf(c_1962,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1947,c_1041])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | r2_hidden(sK0(X2,X1,X0),X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_614,plain,
    ( k7_relat_1(X0,X1) = k7_relat_1(X2,X1)
    | r1_tarski(X1,k1_relat_1(X2)) != iProver_top
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X1) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_622,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2167,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X3,k1_relat_1(k7_relat_1(X1,X2)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X3)) != iProver_top
    | r2_hidden(sK0(X3,X0,k1_relat_1(k7_relat_1(X1,X2))),X2) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_622])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_609,plain,
    ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11293,plain,
    ( k1_funct_1(sK3,sK0(X0,X1,k1_relat_1(k7_relat_1(X2,sK4)))) = k1_funct_1(sK2,sK0(X0,X1,k1_relat_1(k7_relat_1(X2,sK4))))
    | k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,sK4))) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X2,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(X2,sK4)),k1_relat_1(X1)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X2,sK4)),k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2167,c_609])).

cnf(c_11726,plain,
    ( k1_funct_1(sK2,sK0(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK0(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_11293])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11787,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | k1_funct_1(sK2,sK0(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK0(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11726,c_26,c_27])).

cnf(c_11788,plain,
    ( k1_funct_1(sK2,sK0(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK0(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4))))
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11787])).

cnf(c_11796,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK0(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4))))
    | k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1962,c_11788])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_616,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_605,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,k1_relat_1(k7_relat_1(X0,k1_relat_1(X1)))) = k7_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_625,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1610,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK2)))) = k7_relat_1(sK2,k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_625])).

cnf(c_2329,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2)))) = k7_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_616,c_1610])).

cnf(c_16,plain,
    ( ~ v1_funct_1(k6_relat_1(X0))
    | ~ v1_relat_1(k6_relat_1(X0))
    | k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_8,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_132,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_9,c_8])).

cnf(c_2333,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2)))) = k7_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_2329,c_132])).

cnf(c_4,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_621,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1334,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK2))))) = k1_relat_1(k7_relat_1(X0,k1_relat_1(sK2)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_621,c_1329])).

cnf(c_2449,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2))))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_616,c_1334])).

cnf(c_607,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1609,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK3)))) = k7_relat_1(sK3,k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_625])).

cnf(c_1611,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK2)))) = k7_relat_1(sK3,k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1609,c_19])).

cnf(c_1621,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2)))) = k7_relat_1(sK3,k1_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_616,c_1611])).

cnf(c_1625,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2)))) = k7_relat_1(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_1621,c_132])).

cnf(c_2452,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_2449,c_1625])).

cnf(c_2678,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,X0))) = k7_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_2333,c_2333,c_2452])).

cnf(c_1306,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,X0)))) = k1_relat_1(k7_relat_1(sK3,X0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1041,c_619])).

cnf(c_1853,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,X0)))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1306,c_24])).

cnf(c_2680,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_2678,c_1853])).

cnf(c_3050,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_2680,c_2678])).

cnf(c_2572,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0))) = k7_relat_1(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_1625,c_1625,c_2452])).

cnf(c_3051,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_2680,c_2572])).

cnf(c_11816,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK0(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4))))
    | k7_relat_1(sK3,sK4) = k7_relat_1(sK2,sK4)
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11796,c_3050,c_3051])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,negated_conjecture,
    ( k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_252,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_658,plain,
    ( k7_relat_1(sK3,sK4) != X0
    | k7_relat_1(sK2,sK4) != X0
    | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_680,plain,
    ( k7_relat_1(sK3,sK4) != k7_relat_1(X0,sK4)
    | k7_relat_1(sK2,sK4) != k7_relat_1(X0,sK4)
    | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_681,plain,
    ( k7_relat_1(sK3,sK4) != k7_relat_1(sK2,sK4)
    | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4)
    | k7_relat_1(sK2,sK4) != k7_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_251,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3512,plain,
    ( k7_relat_1(X0,sK4) = k7_relat_1(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_3513,plain,
    ( k7_relat_1(sK2,sK4) = k7_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_3512])).

cnf(c_7676,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK4)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7677,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK4)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7676])).

cnf(c_7679,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7677])).

cnf(c_17750,plain,
    ( k1_funct_1(sK3,sK0(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK0(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11816,c_24,c_25,c_17,c_681,c_3513,c_7679])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X1,sK0(X2,X1,X0)) != k1_funct_1(X2,sK0(X2,X1,X0))
    | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_615,plain,
    ( k1_funct_1(X0,sK0(X1,X0,X2)) != k1_funct_1(X1,sK0(X1,X0,X2))
    | k7_relat_1(X1,X2) = k7_relat_1(X0,X2)
    | r1_tarski(X2,k1_relat_1(X0)) != iProver_top
    | r1_tarski(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_17752,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17750,c_615])).

cnf(c_17753,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17752,c_19])).

cnf(c_17754,plain,
    ( k7_relat_1(sK3,sK4) = k7_relat_1(sK2,sK4)
    | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17753,c_3050,c_3051])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17754,c_7679,c_3513,c_681,c_17,c_27,c_26,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.83/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.83/1.49  
% 7.83/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.83/1.49  
% 7.83/1.49  ------  iProver source info
% 7.83/1.49  
% 7.83/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.83/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.83/1.49  git: non_committed_changes: false
% 7.83/1.49  git: last_make_outside_of_git: false
% 7.83/1.49  
% 7.83/1.49  ------ 
% 7.83/1.49  
% 7.83/1.49  ------ Input Options
% 7.83/1.49  
% 7.83/1.49  --out_options                           all
% 7.83/1.49  --tptp_safe_out                         true
% 7.83/1.49  --problem_path                          ""
% 7.83/1.49  --include_path                          ""
% 7.83/1.49  --clausifier                            res/vclausify_rel
% 7.83/1.49  --clausifier_options                    ""
% 7.83/1.49  --stdin                                 false
% 7.83/1.49  --stats_out                             all
% 7.83/1.49  
% 7.83/1.49  ------ General Options
% 7.83/1.49  
% 7.83/1.49  --fof                                   false
% 7.83/1.49  --time_out_real                         305.
% 7.83/1.49  --time_out_virtual                      -1.
% 7.83/1.49  --symbol_type_check                     false
% 7.83/1.49  --clausify_out                          false
% 7.83/1.49  --sig_cnt_out                           false
% 7.83/1.49  --trig_cnt_out                          false
% 7.83/1.49  --trig_cnt_out_tolerance                1.
% 7.83/1.49  --trig_cnt_out_sk_spl                   false
% 7.83/1.49  --abstr_cl_out                          false
% 7.83/1.49  
% 7.83/1.49  ------ Global Options
% 7.83/1.49  
% 7.83/1.49  --schedule                              default
% 7.83/1.49  --add_important_lit                     false
% 7.83/1.49  --prop_solver_per_cl                    1000
% 7.83/1.49  --min_unsat_core                        false
% 7.83/1.49  --soft_assumptions                      false
% 7.83/1.49  --soft_lemma_size                       3
% 7.83/1.49  --prop_impl_unit_size                   0
% 7.83/1.49  --prop_impl_unit                        []
% 7.83/1.49  --share_sel_clauses                     true
% 7.83/1.49  --reset_solvers                         false
% 7.83/1.49  --bc_imp_inh                            [conj_cone]
% 7.83/1.49  --conj_cone_tolerance                   3.
% 7.83/1.49  --extra_neg_conj                        none
% 7.83/1.49  --large_theory_mode                     true
% 7.83/1.49  --prolific_symb_bound                   200
% 7.83/1.49  --lt_threshold                          2000
% 7.83/1.49  --clause_weak_htbl                      true
% 7.83/1.49  --gc_record_bc_elim                     false
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing Options
% 7.83/1.49  
% 7.83/1.49  --preprocessing_flag                    true
% 7.83/1.49  --time_out_prep_mult                    0.1
% 7.83/1.49  --splitting_mode                        input
% 7.83/1.49  --splitting_grd                         true
% 7.83/1.49  --splitting_cvd                         false
% 7.83/1.49  --splitting_cvd_svl                     false
% 7.83/1.49  --splitting_nvd                         32
% 7.83/1.49  --sub_typing                            true
% 7.83/1.49  --prep_gs_sim                           true
% 7.83/1.49  --prep_unflatten                        true
% 7.83/1.49  --prep_res_sim                          true
% 7.83/1.49  --prep_upred                            true
% 7.83/1.49  --prep_sem_filter                       exhaustive
% 7.83/1.49  --prep_sem_filter_out                   false
% 7.83/1.49  --pred_elim                             true
% 7.83/1.49  --res_sim_input                         true
% 7.83/1.49  --eq_ax_congr_red                       true
% 7.83/1.49  --pure_diseq_elim                       true
% 7.83/1.49  --brand_transform                       false
% 7.83/1.49  --non_eq_to_eq                          false
% 7.83/1.49  --prep_def_merge                        true
% 7.83/1.49  --prep_def_merge_prop_impl              false
% 7.83/1.49  --prep_def_merge_mbd                    true
% 7.83/1.49  --prep_def_merge_tr_red                 false
% 7.83/1.49  --prep_def_merge_tr_cl                  false
% 7.83/1.49  --smt_preprocessing                     true
% 7.83/1.49  --smt_ac_axioms                         fast
% 7.83/1.49  --preprocessed_out                      false
% 7.83/1.49  --preprocessed_stats                    false
% 7.83/1.49  
% 7.83/1.49  ------ Abstraction refinement Options
% 7.83/1.49  
% 7.83/1.49  --abstr_ref                             []
% 7.83/1.49  --abstr_ref_prep                        false
% 7.83/1.49  --abstr_ref_until_sat                   false
% 7.83/1.49  --abstr_ref_sig_restrict                funpre
% 7.83/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.83/1.49  --abstr_ref_under                       []
% 7.83/1.49  
% 7.83/1.49  ------ SAT Options
% 7.83/1.49  
% 7.83/1.49  --sat_mode                              false
% 7.83/1.49  --sat_fm_restart_options                ""
% 7.83/1.49  --sat_gr_def                            false
% 7.83/1.49  --sat_epr_types                         true
% 7.83/1.49  --sat_non_cyclic_types                  false
% 7.83/1.49  --sat_finite_models                     false
% 7.83/1.49  --sat_fm_lemmas                         false
% 7.83/1.49  --sat_fm_prep                           false
% 7.83/1.49  --sat_fm_uc_incr                        true
% 7.83/1.49  --sat_out_model                         small
% 7.83/1.49  --sat_out_clauses                       false
% 7.83/1.49  
% 7.83/1.49  ------ QBF Options
% 7.83/1.49  
% 7.83/1.49  --qbf_mode                              false
% 7.83/1.49  --qbf_elim_univ                         false
% 7.83/1.49  --qbf_dom_inst                          none
% 7.83/1.49  --qbf_dom_pre_inst                      false
% 7.83/1.49  --qbf_sk_in                             false
% 7.83/1.49  --qbf_pred_elim                         true
% 7.83/1.49  --qbf_split                             512
% 7.83/1.49  
% 7.83/1.49  ------ BMC1 Options
% 7.83/1.49  
% 7.83/1.49  --bmc1_incremental                      false
% 7.83/1.49  --bmc1_axioms                           reachable_all
% 7.83/1.49  --bmc1_min_bound                        0
% 7.83/1.49  --bmc1_max_bound                        -1
% 7.83/1.49  --bmc1_max_bound_default                -1
% 7.83/1.49  --bmc1_symbol_reachability              true
% 7.83/1.49  --bmc1_property_lemmas                  false
% 7.83/1.49  --bmc1_k_induction                      false
% 7.83/1.49  --bmc1_non_equiv_states                 false
% 7.83/1.49  --bmc1_deadlock                         false
% 7.83/1.49  --bmc1_ucm                              false
% 7.83/1.49  --bmc1_add_unsat_core                   none
% 7.83/1.49  --bmc1_unsat_core_children              false
% 7.83/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.83/1.49  --bmc1_out_stat                         full
% 7.83/1.49  --bmc1_ground_init                      false
% 7.83/1.49  --bmc1_pre_inst_next_state              false
% 7.83/1.49  --bmc1_pre_inst_state                   false
% 7.83/1.49  --bmc1_pre_inst_reach_state             false
% 7.83/1.49  --bmc1_out_unsat_core                   false
% 7.83/1.49  --bmc1_aig_witness_out                  false
% 7.83/1.49  --bmc1_verbose                          false
% 7.83/1.49  --bmc1_dump_clauses_tptp                false
% 7.83/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.83/1.49  --bmc1_dump_file                        -
% 7.83/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.83/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.83/1.49  --bmc1_ucm_extend_mode                  1
% 7.83/1.49  --bmc1_ucm_init_mode                    2
% 7.83/1.49  --bmc1_ucm_cone_mode                    none
% 7.83/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.83/1.49  --bmc1_ucm_relax_model                  4
% 7.83/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.83/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.83/1.49  --bmc1_ucm_layered_model                none
% 7.83/1.49  --bmc1_ucm_max_lemma_size               10
% 7.83/1.49  
% 7.83/1.49  ------ AIG Options
% 7.83/1.49  
% 7.83/1.49  --aig_mode                              false
% 7.83/1.49  
% 7.83/1.49  ------ Instantiation Options
% 7.83/1.49  
% 7.83/1.49  --instantiation_flag                    true
% 7.83/1.49  --inst_sos_flag                         true
% 7.83/1.49  --inst_sos_phase                        true
% 7.83/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.83/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.83/1.49  --inst_lit_sel_side                     num_symb
% 7.83/1.49  --inst_solver_per_active                1400
% 7.83/1.49  --inst_solver_calls_frac                1.
% 7.83/1.49  --inst_passive_queue_type               priority_queues
% 7.83/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.83/1.49  --inst_passive_queues_freq              [25;2]
% 7.83/1.49  --inst_dismatching                      true
% 7.83/1.49  --inst_eager_unprocessed_to_passive     true
% 7.83/1.49  --inst_prop_sim_given                   true
% 7.83/1.49  --inst_prop_sim_new                     false
% 7.83/1.49  --inst_subs_new                         false
% 7.83/1.49  --inst_eq_res_simp                      false
% 7.83/1.49  --inst_subs_given                       false
% 7.83/1.49  --inst_orphan_elimination               true
% 7.83/1.49  --inst_learning_loop_flag               true
% 7.83/1.49  --inst_learning_start                   3000
% 7.83/1.49  --inst_learning_factor                  2
% 7.83/1.49  --inst_start_prop_sim_after_learn       3
% 7.83/1.49  --inst_sel_renew                        solver
% 7.83/1.49  --inst_lit_activity_flag                true
% 7.83/1.49  --inst_restr_to_given                   false
% 7.83/1.49  --inst_activity_threshold               500
% 7.83/1.49  --inst_out_proof                        true
% 7.83/1.49  
% 7.83/1.49  ------ Resolution Options
% 7.83/1.49  
% 7.83/1.49  --resolution_flag                       true
% 7.83/1.49  --res_lit_sel                           adaptive
% 7.83/1.49  --res_lit_sel_side                      none
% 7.83/1.49  --res_ordering                          kbo
% 7.83/1.49  --res_to_prop_solver                    active
% 7.83/1.49  --res_prop_simpl_new                    false
% 7.83/1.49  --res_prop_simpl_given                  true
% 7.83/1.49  --res_passive_queue_type                priority_queues
% 7.83/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.83/1.49  --res_passive_queues_freq               [15;5]
% 7.83/1.49  --res_forward_subs                      full
% 7.83/1.49  --res_backward_subs                     full
% 7.83/1.49  --res_forward_subs_resolution           true
% 7.83/1.49  --res_backward_subs_resolution          true
% 7.83/1.49  --res_orphan_elimination                true
% 7.83/1.49  --res_time_limit                        2.
% 7.83/1.49  --res_out_proof                         true
% 7.83/1.49  
% 7.83/1.49  ------ Superposition Options
% 7.83/1.49  
% 7.83/1.49  --superposition_flag                    true
% 7.83/1.49  --sup_passive_queue_type                priority_queues
% 7.83/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.83/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.83/1.49  --demod_completeness_check              fast
% 7.83/1.49  --demod_use_ground                      true
% 7.83/1.49  --sup_to_prop_solver                    passive
% 7.83/1.49  --sup_prop_simpl_new                    true
% 7.83/1.49  --sup_prop_simpl_given                  true
% 7.83/1.49  --sup_fun_splitting                     true
% 7.83/1.49  --sup_smt_interval                      50000
% 7.83/1.49  
% 7.83/1.49  ------ Superposition Simplification Setup
% 7.83/1.49  
% 7.83/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.83/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.83/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.83/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.83/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.83/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.83/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.83/1.49  --sup_immed_triv                        [TrivRules]
% 7.83/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.49  --sup_immed_bw_main                     []
% 7.83/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.83/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.83/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.49  --sup_input_bw                          []
% 7.83/1.49  
% 7.83/1.49  ------ Combination Options
% 7.83/1.49  
% 7.83/1.49  --comb_res_mult                         3
% 7.83/1.49  --comb_sup_mult                         2
% 7.83/1.49  --comb_inst_mult                        10
% 7.83/1.49  
% 7.83/1.49  ------ Debug Options
% 7.83/1.49  
% 7.83/1.49  --dbg_backtrace                         false
% 7.83/1.49  --dbg_dump_prop_clauses                 false
% 7.83/1.49  --dbg_dump_prop_clauses_file            -
% 7.83/1.49  --dbg_out_stat                          false
% 7.83/1.49  ------ Parsing...
% 7.83/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  ------ Proving...
% 7.83/1.49  ------ Problem Properties 
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  clauses                                 24
% 7.83/1.49  conjectures                             7
% 7.83/1.49  EPR                                     4
% 7.83/1.49  Horn                                    22
% 7.83/1.49  unary                                   9
% 7.83/1.49  binary                                  3
% 7.83/1.49  lits                                    71
% 7.83/1.49  lits eq                                 16
% 7.83/1.49  fd_pure                                 0
% 7.83/1.49  fd_pseudo                               0
% 7.83/1.49  fd_cond                                 0
% 7.83/1.49  fd_pseudo_cond                          0
% 7.83/1.49  AC symbols                              0
% 7.83/1.49  
% 7.83/1.49  ------ Schedule dynamic 5 is on 
% 7.83/1.49  
% 7.83/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ 
% 7.83/1.49  Current options:
% 7.83/1.49  ------ 
% 7.83/1.49  
% 7.83/1.49  ------ Input Options
% 7.83/1.49  
% 7.83/1.49  --out_options                           all
% 7.83/1.49  --tptp_safe_out                         true
% 7.83/1.49  --problem_path                          ""
% 7.83/1.49  --include_path                          ""
% 7.83/1.49  --clausifier                            res/vclausify_rel
% 7.83/1.49  --clausifier_options                    ""
% 7.83/1.49  --stdin                                 false
% 7.83/1.49  --stats_out                             all
% 7.83/1.49  
% 7.83/1.49  ------ General Options
% 7.83/1.49  
% 7.83/1.49  --fof                                   false
% 7.83/1.49  --time_out_real                         305.
% 7.83/1.49  --time_out_virtual                      -1.
% 7.83/1.49  --symbol_type_check                     false
% 7.83/1.49  --clausify_out                          false
% 7.83/1.49  --sig_cnt_out                           false
% 7.83/1.49  --trig_cnt_out                          false
% 7.83/1.49  --trig_cnt_out_tolerance                1.
% 7.83/1.49  --trig_cnt_out_sk_spl                   false
% 7.83/1.49  --abstr_cl_out                          false
% 7.83/1.49  
% 7.83/1.49  ------ Global Options
% 7.83/1.49  
% 7.83/1.49  --schedule                              default
% 7.83/1.49  --add_important_lit                     false
% 7.83/1.49  --prop_solver_per_cl                    1000
% 7.83/1.49  --min_unsat_core                        false
% 7.83/1.49  --soft_assumptions                      false
% 7.83/1.49  --soft_lemma_size                       3
% 7.83/1.49  --prop_impl_unit_size                   0
% 7.83/1.49  --prop_impl_unit                        []
% 7.83/1.49  --share_sel_clauses                     true
% 7.83/1.49  --reset_solvers                         false
% 7.83/1.49  --bc_imp_inh                            [conj_cone]
% 7.83/1.49  --conj_cone_tolerance                   3.
% 7.83/1.49  --extra_neg_conj                        none
% 7.83/1.49  --large_theory_mode                     true
% 7.83/1.49  --prolific_symb_bound                   200
% 7.83/1.49  --lt_threshold                          2000
% 7.83/1.49  --clause_weak_htbl                      true
% 7.83/1.49  --gc_record_bc_elim                     false
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing Options
% 7.83/1.49  
% 7.83/1.49  --preprocessing_flag                    true
% 7.83/1.49  --time_out_prep_mult                    0.1
% 7.83/1.49  --splitting_mode                        input
% 7.83/1.49  --splitting_grd                         true
% 7.83/1.49  --splitting_cvd                         false
% 7.83/1.49  --splitting_cvd_svl                     false
% 7.83/1.49  --splitting_nvd                         32
% 7.83/1.49  --sub_typing                            true
% 7.83/1.49  --prep_gs_sim                           true
% 7.83/1.49  --prep_unflatten                        true
% 7.83/1.49  --prep_res_sim                          true
% 7.83/1.49  --prep_upred                            true
% 7.83/1.49  --prep_sem_filter                       exhaustive
% 7.83/1.49  --prep_sem_filter_out                   false
% 7.83/1.49  --pred_elim                             true
% 7.83/1.49  --res_sim_input                         true
% 7.83/1.49  --eq_ax_congr_red                       true
% 7.83/1.49  --pure_diseq_elim                       true
% 7.83/1.49  --brand_transform                       false
% 7.83/1.49  --non_eq_to_eq                          false
% 7.83/1.49  --prep_def_merge                        true
% 7.83/1.49  --prep_def_merge_prop_impl              false
% 7.83/1.49  --prep_def_merge_mbd                    true
% 7.83/1.49  --prep_def_merge_tr_red                 false
% 7.83/1.49  --prep_def_merge_tr_cl                  false
% 7.83/1.49  --smt_preprocessing                     true
% 7.83/1.49  --smt_ac_axioms                         fast
% 7.83/1.49  --preprocessed_out                      false
% 7.83/1.49  --preprocessed_stats                    false
% 7.83/1.49  
% 7.83/1.49  ------ Abstraction refinement Options
% 7.83/1.49  
% 7.83/1.49  --abstr_ref                             []
% 7.83/1.49  --abstr_ref_prep                        false
% 7.83/1.49  --abstr_ref_until_sat                   false
% 7.83/1.49  --abstr_ref_sig_restrict                funpre
% 7.83/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.83/1.49  --abstr_ref_under                       []
% 7.83/1.49  
% 7.83/1.49  ------ SAT Options
% 7.83/1.49  
% 7.83/1.49  --sat_mode                              false
% 7.83/1.49  --sat_fm_restart_options                ""
% 7.83/1.49  --sat_gr_def                            false
% 7.83/1.49  --sat_epr_types                         true
% 7.83/1.49  --sat_non_cyclic_types                  false
% 7.83/1.49  --sat_finite_models                     false
% 7.83/1.49  --sat_fm_lemmas                         false
% 7.83/1.49  --sat_fm_prep                           false
% 7.83/1.49  --sat_fm_uc_incr                        true
% 7.83/1.49  --sat_out_model                         small
% 7.83/1.49  --sat_out_clauses                       false
% 7.83/1.49  
% 7.83/1.49  ------ QBF Options
% 7.83/1.49  
% 7.83/1.49  --qbf_mode                              false
% 7.83/1.49  --qbf_elim_univ                         false
% 7.83/1.49  --qbf_dom_inst                          none
% 7.83/1.49  --qbf_dom_pre_inst                      false
% 7.83/1.49  --qbf_sk_in                             false
% 7.83/1.49  --qbf_pred_elim                         true
% 7.83/1.49  --qbf_split                             512
% 7.83/1.49  
% 7.83/1.49  ------ BMC1 Options
% 7.83/1.49  
% 7.83/1.49  --bmc1_incremental                      false
% 7.83/1.49  --bmc1_axioms                           reachable_all
% 7.83/1.49  --bmc1_min_bound                        0
% 7.83/1.49  --bmc1_max_bound                        -1
% 7.83/1.49  --bmc1_max_bound_default                -1
% 7.83/1.49  --bmc1_symbol_reachability              true
% 7.83/1.49  --bmc1_property_lemmas                  false
% 7.83/1.49  --bmc1_k_induction                      false
% 7.83/1.49  --bmc1_non_equiv_states                 false
% 7.83/1.49  --bmc1_deadlock                         false
% 7.83/1.50  --bmc1_ucm                              false
% 7.83/1.50  --bmc1_add_unsat_core                   none
% 7.83/1.50  --bmc1_unsat_core_children              false
% 7.83/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.83/1.50  --bmc1_out_stat                         full
% 7.83/1.50  --bmc1_ground_init                      false
% 7.83/1.50  --bmc1_pre_inst_next_state              false
% 7.83/1.50  --bmc1_pre_inst_state                   false
% 7.83/1.50  --bmc1_pre_inst_reach_state             false
% 7.83/1.50  --bmc1_out_unsat_core                   false
% 7.83/1.50  --bmc1_aig_witness_out                  false
% 7.83/1.50  --bmc1_verbose                          false
% 7.83/1.50  --bmc1_dump_clauses_tptp                false
% 7.83/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.83/1.50  --bmc1_dump_file                        -
% 7.83/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.83/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.83/1.50  --bmc1_ucm_extend_mode                  1
% 7.83/1.50  --bmc1_ucm_init_mode                    2
% 7.83/1.50  --bmc1_ucm_cone_mode                    none
% 7.83/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.83/1.50  --bmc1_ucm_relax_model                  4
% 7.83/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.83/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.83/1.50  --bmc1_ucm_layered_model                none
% 7.83/1.50  --bmc1_ucm_max_lemma_size               10
% 7.83/1.50  
% 7.83/1.50  ------ AIG Options
% 7.83/1.50  
% 7.83/1.50  --aig_mode                              false
% 7.83/1.50  
% 7.83/1.50  ------ Instantiation Options
% 7.83/1.50  
% 7.83/1.50  --instantiation_flag                    true
% 7.83/1.50  --inst_sos_flag                         true
% 7.83/1.50  --inst_sos_phase                        true
% 7.83/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.83/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.83/1.50  --inst_lit_sel_side                     none
% 7.83/1.50  --inst_solver_per_active                1400
% 7.83/1.50  --inst_solver_calls_frac                1.
% 7.83/1.50  --inst_passive_queue_type               priority_queues
% 7.83/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.83/1.50  --inst_passive_queues_freq              [25;2]
% 7.83/1.50  --inst_dismatching                      true
% 7.83/1.50  --inst_eager_unprocessed_to_passive     true
% 7.83/1.50  --inst_prop_sim_given                   true
% 7.83/1.50  --inst_prop_sim_new                     false
% 7.83/1.50  --inst_subs_new                         false
% 7.83/1.50  --inst_eq_res_simp                      false
% 7.83/1.50  --inst_subs_given                       false
% 7.83/1.50  --inst_orphan_elimination               true
% 7.83/1.50  --inst_learning_loop_flag               true
% 7.83/1.50  --inst_learning_start                   3000
% 7.83/1.50  --inst_learning_factor                  2
% 7.83/1.50  --inst_start_prop_sim_after_learn       3
% 7.83/1.50  --inst_sel_renew                        solver
% 7.83/1.50  --inst_lit_activity_flag                true
% 7.83/1.50  --inst_restr_to_given                   false
% 7.83/1.50  --inst_activity_threshold               500
% 7.83/1.50  --inst_out_proof                        true
% 7.83/1.50  
% 7.83/1.50  ------ Resolution Options
% 7.83/1.50  
% 7.83/1.50  --resolution_flag                       false
% 7.83/1.50  --res_lit_sel                           adaptive
% 7.83/1.50  --res_lit_sel_side                      none
% 7.83/1.50  --res_ordering                          kbo
% 7.83/1.50  --res_to_prop_solver                    active
% 7.83/1.50  --res_prop_simpl_new                    false
% 7.83/1.50  --res_prop_simpl_given                  true
% 7.83/1.50  --res_passive_queue_type                priority_queues
% 7.83/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.83/1.50  --res_passive_queues_freq               [15;5]
% 7.83/1.50  --res_forward_subs                      full
% 7.83/1.50  --res_backward_subs                     full
% 7.83/1.50  --res_forward_subs_resolution           true
% 7.83/1.50  --res_backward_subs_resolution          true
% 7.83/1.50  --res_orphan_elimination                true
% 7.83/1.50  --res_time_limit                        2.
% 7.83/1.50  --res_out_proof                         true
% 7.83/1.50  
% 7.83/1.50  ------ Superposition Options
% 7.83/1.50  
% 7.83/1.50  --superposition_flag                    true
% 7.83/1.50  --sup_passive_queue_type                priority_queues
% 7.83/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.83/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.83/1.50  --demod_completeness_check              fast
% 7.83/1.50  --demod_use_ground                      true
% 7.83/1.50  --sup_to_prop_solver                    passive
% 7.83/1.50  --sup_prop_simpl_new                    true
% 7.83/1.50  --sup_prop_simpl_given                  true
% 7.83/1.50  --sup_fun_splitting                     true
% 7.83/1.50  --sup_smt_interval                      50000
% 7.83/1.50  
% 7.83/1.50  ------ Superposition Simplification Setup
% 7.83/1.50  
% 7.83/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.83/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.83/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.83/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.83/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.83/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.83/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.83/1.50  --sup_immed_triv                        [TrivRules]
% 7.83/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.50  --sup_immed_bw_main                     []
% 7.83/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.83/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.83/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.50  --sup_input_bw                          []
% 7.83/1.50  
% 7.83/1.50  ------ Combination Options
% 7.83/1.50  
% 7.83/1.50  --comb_res_mult                         3
% 7.83/1.50  --comb_sup_mult                         2
% 7.83/1.50  --comb_inst_mult                        10
% 7.83/1.50  
% 7.83/1.50  ------ Debug Options
% 7.83/1.50  
% 7.83/1.50  --dbg_backtrace                         false
% 7.83/1.50  --dbg_dump_prop_clauses                 false
% 7.83/1.50  --dbg_dump_prop_clauses_file            -
% 7.83/1.50  --dbg_out_stat                          false
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  ------ Proving...
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  % SZS status Theorem for theBenchmark.p
% 7.83/1.50  
% 7.83/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.83/1.50  
% 7.83/1.50  fof(f4,axiom,(
% 7.83/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f15,plain,(
% 7.83/1.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.83/1.50    inference(ennf_transformation,[],[f4])).
% 7.83/1.50  
% 7.83/1.50  fof(f46,plain,(
% 7.83/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f15])).
% 7.83/1.50  
% 7.83/1.50  fof(f10,conjecture,(
% 7.83/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f11,negated_conjecture,(
% 7.83/1.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X0) = k1_relat_1(X1)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 7.83/1.50    inference(negated_conjecture,[],[f10])).
% 7.83/1.50  
% 7.83/1.50  fof(f24,plain,(
% 7.83/1.50    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 7.83/1.50    inference(ennf_transformation,[],[f11])).
% 7.83/1.50  
% 7.83/1.50  fof(f25,plain,(
% 7.83/1.50    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 7.83/1.50    inference(flattening,[],[f24])).
% 7.83/1.50  
% 7.83/1.50  fof(f39,plain,(
% 7.83/1.50    ( ! [X0,X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => (k7_relat_1(X0,sK4) != k7_relat_1(X1,sK4) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,sK4)) & k1_relat_1(X0) = k1_relat_1(X1))) )),
% 7.83/1.50    introduced(choice_axiom,[])).
% 7.83/1.50  
% 7.83/1.50  fof(f38,plain,(
% 7.83/1.50    ( ! [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK3,X2) != k7_relat_1(X0,X2) & ! [X3] : (k1_funct_1(sK3,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK3) = k1_relat_1(X0)) & v1_funct_1(sK3) & v1_relat_1(sK3))) )),
% 7.83/1.50    introduced(choice_axiom,[])).
% 7.83/1.50  
% 7.83/1.50  fof(f37,plain,(
% 7.83/1.50    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(sK2,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK2) = k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 7.83/1.50    introduced(choice_axiom,[])).
% 7.83/1.50  
% 7.83/1.50  fof(f40,plain,(
% 7.83/1.50    ((k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4) & ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3) | ~r2_hidden(X3,sK4)) & k1_relat_1(sK2) = k1_relat_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 7.83/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f39,f38,f37])).
% 7.83/1.50  
% 7.83/1.50  fof(f62,plain,(
% 7.83/1.50    k1_relat_1(sK2) = k1_relat_1(sK3)),
% 7.83/1.50    inference(cnf_transformation,[],[f40])).
% 7.83/1.50  
% 7.83/1.50  fof(f5,axiom,(
% 7.83/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f16,plain,(
% 7.83/1.50    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.83/1.50    inference(ennf_transformation,[],[f5])).
% 7.83/1.50  
% 7.83/1.50  fof(f17,plain,(
% 7.83/1.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.83/1.50    inference(flattening,[],[f16])).
% 7.83/1.50  
% 7.83/1.50  fof(f47,plain,(
% 7.83/1.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f17])).
% 7.83/1.50  
% 7.83/1.50  fof(f60,plain,(
% 7.83/1.50    v1_relat_1(sK3)),
% 7.83/1.50    inference(cnf_transformation,[],[f40])).
% 7.83/1.50  
% 7.83/1.50  fof(f58,plain,(
% 7.83/1.50    v1_relat_1(sK2)),
% 7.83/1.50    inference(cnf_transformation,[],[f40])).
% 7.83/1.50  
% 7.83/1.50  fof(f8,axiom,(
% 7.83/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f20,plain,(
% 7.83/1.50    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.83/1.50    inference(ennf_transformation,[],[f8])).
% 7.83/1.50  
% 7.83/1.50  fof(f21,plain,(
% 7.83/1.50    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.83/1.50    inference(flattening,[],[f20])).
% 7.83/1.50  
% 7.83/1.50  fof(f28,plain,(
% 7.83/1.50    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.83/1.50    inference(nnf_transformation,[],[f21])).
% 7.83/1.50  
% 7.83/1.50  fof(f29,plain,(
% 7.83/1.50    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.83/1.50    inference(rectify,[],[f28])).
% 7.83/1.50  
% 7.83/1.50  fof(f30,plain,(
% 7.83/1.50    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2)))),
% 7.83/1.50    introduced(choice_axiom,[])).
% 7.83/1.50  
% 7.83/1.50  fof(f31,plain,(
% 7.83/1.50    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.83/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 7.83/1.50  
% 7.83/1.50  fof(f52,plain,(
% 7.83/1.50    ( ! [X2,X0,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f31])).
% 7.83/1.50  
% 7.83/1.50  fof(f2,axiom,(
% 7.83/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f13,plain,(
% 7.83/1.50    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 7.83/1.50    inference(ennf_transformation,[],[f2])).
% 7.83/1.50  
% 7.83/1.50  fof(f26,plain,(
% 7.83/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 7.83/1.50    inference(nnf_transformation,[],[f13])).
% 7.83/1.50  
% 7.83/1.50  fof(f27,plain,(
% 7.83/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 7.83/1.50    inference(flattening,[],[f26])).
% 7.83/1.50  
% 7.83/1.50  fof(f42,plain,(
% 7.83/1.50    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f27])).
% 7.83/1.50  
% 7.83/1.50  fof(f63,plain,(
% 7.83/1.50    ( ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3) | ~r2_hidden(X3,sK4)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f40])).
% 7.83/1.50  
% 7.83/1.50  fof(f61,plain,(
% 7.83/1.50    v1_funct_1(sK3)),
% 7.83/1.50    inference(cnf_transformation,[],[f40])).
% 7.83/1.50  
% 7.83/1.50  fof(f7,axiom,(
% 7.83/1.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f49,plain,(
% 7.83/1.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.83/1.50    inference(cnf_transformation,[],[f7])).
% 7.83/1.50  
% 7.83/1.50  fof(f1,axiom,(
% 7.83/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f12,plain,(
% 7.83/1.50    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.83/1.50    inference(ennf_transformation,[],[f1])).
% 7.83/1.50  
% 7.83/1.50  fof(f41,plain,(
% 7.83/1.50    ( ! [X0,X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f12])).
% 7.83/1.50  
% 7.83/1.50  fof(f9,axiom,(
% 7.83/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f22,plain,(
% 7.83/1.50    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.83/1.50    inference(ennf_transformation,[],[f9])).
% 7.83/1.50  
% 7.83/1.50  fof(f23,plain,(
% 7.83/1.50    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.83/1.50    inference(flattening,[],[f22])).
% 7.83/1.50  
% 7.83/1.50  fof(f32,plain,(
% 7.83/1.50    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.83/1.50    inference(nnf_transformation,[],[f23])).
% 7.83/1.50  
% 7.83/1.50  fof(f33,plain,(
% 7.83/1.50    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.83/1.50    inference(flattening,[],[f32])).
% 7.83/1.50  
% 7.83/1.50  fof(f34,plain,(
% 7.83/1.50    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.83/1.50    inference(rectify,[],[f33])).
% 7.83/1.50  
% 7.83/1.50  fof(f35,plain,(
% 7.83/1.50    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.83/1.50    introduced(choice_axiom,[])).
% 7.83/1.50  
% 7.83/1.50  fof(f36,plain,(
% 7.83/1.50    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1) & r2_hidden(sK1(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.83/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 7.83/1.50  
% 7.83/1.50  fof(f54,plain,(
% 7.83/1.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f36])).
% 7.83/1.50  
% 7.83/1.50  fof(f68,plain,(
% 7.83/1.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 7.83/1.50    inference(equality_resolution,[],[f54])).
% 7.83/1.50  
% 7.83/1.50  fof(f50,plain,(
% 7.83/1.50    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 7.83/1.50    inference(cnf_transformation,[],[f7])).
% 7.83/1.50  
% 7.83/1.50  fof(f3,axiom,(
% 7.83/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.83/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.50  
% 7.83/1.50  fof(f14,plain,(
% 7.83/1.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.83/1.50    inference(ennf_transformation,[],[f3])).
% 7.83/1.50  
% 7.83/1.50  fof(f45,plain,(
% 7.83/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f14])).
% 7.83/1.50  
% 7.83/1.50  fof(f59,plain,(
% 7.83/1.50    v1_funct_1(sK2)),
% 7.83/1.50    inference(cnf_transformation,[],[f40])).
% 7.83/1.50  
% 7.83/1.50  fof(f64,plain,(
% 7.83/1.50    k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4)),
% 7.83/1.50    inference(cnf_transformation,[],[f40])).
% 7.83/1.50  
% 7.83/1.50  fof(f53,plain,(
% 7.83/1.50    ( ! [X2,X0,X1] : (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | k1_funct_1(X0,sK0(X0,X1,X2)) != k1_funct_1(X1,sK0(X0,X1,X2)) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.83/1.50    inference(cnf_transformation,[],[f31])).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5,plain,
% 7.83/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 7.83/1.50      | ~ v1_relat_1(X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_620,plain,
% 7.83/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 7.83/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_19,negated_conjecture,
% 7.83/1.50      ( k1_relat_1(sK2) = k1_relat_1(sK3) ),
% 7.83/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_6,plain,
% 7.83/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.83/1.50      | ~ v1_relat_1(X1)
% 7.83/1.50      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.83/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_619,plain,
% 7.83/1.50      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.83/1.50      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.83/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1308,plain,
% 7.83/1.50      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.83/1.50      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_19,c_619]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_21,negated_conjecture,
% 7.83/1.50      ( v1_relat_1(sK3) ),
% 7.83/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_26,plain,
% 7.83/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1328,plain,
% 7.83/1.50      ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 7.83/1.50      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_1308,c_26]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1329,plain,
% 7.83/1.50      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 7.83/1.50      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 7.83/1.50      inference(renaming,[status(thm)],[c_1328]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1335,plain,
% 7.83/1.50      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_620,c_1329]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_23,negated_conjecture,
% 7.83/1.50      ( v1_relat_1(sK2) ),
% 7.83/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_24,plain,
% 7.83/1.50      ( v1_relat_1(sK2) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1947,plain,
% 7.83/1.50      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_1335,c_24]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1033,plain,
% 7.83/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_19,c_620]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1041,plain,
% 7.83/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK2)) = iProver_top ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_1033,c_26]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1962,plain,
% 7.83/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(sK2)) = iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1947,c_1041]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_11,plain,
% 7.83/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.83/1.50      | ~ r1_tarski(X0,k1_relat_1(X2))
% 7.83/1.50      | r2_hidden(sK0(X2,X1,X0),X0)
% 7.83/1.50      | ~ v1_funct_1(X1)
% 7.83/1.50      | ~ v1_funct_1(X2)
% 7.83/1.50      | ~ v1_relat_1(X1)
% 7.83/1.50      | ~ v1_relat_1(X2)
% 7.83/1.50      | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_614,plain,
% 7.83/1.50      ( k7_relat_1(X0,X1) = k7_relat_1(X2,X1)
% 7.83/1.50      | r1_tarski(X1,k1_relat_1(X2)) != iProver_top
% 7.83/1.50      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.83/1.50      | r2_hidden(sK0(X0,X2,X1),X1) = iProver_top
% 7.83/1.50      | v1_funct_1(X2) != iProver_top
% 7.83/1.50      | v1_funct_1(X0) != iProver_top
% 7.83/1.50      | v1_relat_1(X2) != iProver_top
% 7.83/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3,plain,
% 7.83/1.50      ( r2_hidden(X0,X1)
% 7.83/1.50      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 7.83/1.50      | ~ v1_relat_1(X2) ),
% 7.83/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_622,plain,
% 7.83/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.83/1.50      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) != iProver_top
% 7.83/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2167,plain,
% 7.83/1.50      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X3,k1_relat_1(k7_relat_1(X1,X2)))
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X0)) != iProver_top
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X3)) != iProver_top
% 7.83/1.50      | r2_hidden(sK0(X3,X0,k1_relat_1(k7_relat_1(X1,X2))),X2) = iProver_top
% 7.83/1.50      | v1_funct_1(X3) != iProver_top
% 7.83/1.50      | v1_funct_1(X0) != iProver_top
% 7.83/1.50      | v1_relat_1(X3) != iProver_top
% 7.83/1.50      | v1_relat_1(X1) != iProver_top
% 7.83/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_614,c_622]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_18,negated_conjecture,
% 7.83/1.50      ( ~ r2_hidden(X0,sK4) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_609,plain,
% 7.83/1.50      ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
% 7.83/1.50      | r2_hidden(X0,sK4) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_11293,plain,
% 7.83/1.50      ( k1_funct_1(sK3,sK0(X0,X1,k1_relat_1(k7_relat_1(X2,sK4)))) = k1_funct_1(sK2,sK0(X0,X1,k1_relat_1(k7_relat_1(X2,sK4))))
% 7.83/1.50      | k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,sK4))) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X2,sK4)))
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X2,sK4)),k1_relat_1(X1)) != iProver_top
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X2,sK4)),k1_relat_1(X0)) != iProver_top
% 7.83/1.50      | v1_funct_1(X1) != iProver_top
% 7.83/1.50      | v1_funct_1(X0) != iProver_top
% 7.83/1.50      | v1_relat_1(X1) != iProver_top
% 7.83/1.50      | v1_relat_1(X2) != iProver_top
% 7.83/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_2167,c_609]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_11726,plain,
% 7.83/1.50      ( k1_funct_1(sK2,sK0(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK0(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4))))
% 7.83/1.50      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.83/1.50      | v1_funct_1(X0) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(X1) != iProver_top
% 7.83/1.50      | v1_relat_1(X0) != iProver_top
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_19,c_11293]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_20,negated_conjecture,
% 7.83/1.50      ( v1_funct_1(sK3) ),
% 7.83/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_27,plain,
% 7.83/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_11787,plain,
% 7.83/1.50      ( v1_relat_1(X0) != iProver_top
% 7.83/1.50      | v1_relat_1(X1) != iProver_top
% 7.83/1.50      | k1_funct_1(sK2,sK0(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK0(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4))))
% 7.83/1.50      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.83/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_11726,c_26,c_27]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_11788,plain,
% 7.83/1.50      ( k1_funct_1(sK2,sK0(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4)))) = k1_funct_1(sK3,sK0(sK3,X0,k1_relat_1(k7_relat_1(X1,sK4))))
% 7.83/1.50      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,sK4))) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(X1,sK4)))
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(X0)) != iProver_top
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(X1,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.83/1.50      | v1_funct_1(X0) != iProver_top
% 7.83/1.50      | v1_relat_1(X0) != iProver_top
% 7.83/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.83/1.50      inference(renaming,[status(thm)],[c_11787]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_11796,plain,
% 7.83/1.50      ( k1_funct_1(sK3,sK0(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK0(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4))))
% 7.83/1.50      | k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1962,c_11788]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_9,plain,
% 7.83/1.50      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.83/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_616,plain,
% 7.83/1.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_605,plain,
% 7.83/1.50      ( v1_relat_1(sK2) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_0,plain,
% 7.83/1.50      ( ~ v1_relat_1(X0)
% 7.83/1.50      | ~ v1_relat_1(X1)
% 7.83/1.50      | k7_relat_1(X1,k1_relat_1(k7_relat_1(X0,k1_relat_1(X1)))) = k7_relat_1(X1,k1_relat_1(X0)) ),
% 7.83/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_625,plain,
% 7.83/1.50      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
% 7.83/1.50      | v1_relat_1(X1) != iProver_top
% 7.83/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1610,plain,
% 7.83/1.50      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK2)))) = k7_relat_1(sK2,k1_relat_1(X0))
% 7.83/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_605,c_625]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2329,plain,
% 7.83/1.50      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2)))) = k7_relat_1(sK2,k1_relat_1(k6_relat_1(X0))) ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_616,c_1610]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_16,plain,
% 7.83/1.50      ( ~ v1_funct_1(k6_relat_1(X0))
% 7.83/1.50      | ~ v1_relat_1(k6_relat_1(X0))
% 7.83/1.50      | k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.83/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_8,plain,
% 7.83/1.50      ( v1_funct_1(k6_relat_1(X0)) ),
% 7.83/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_132,plain,
% 7.83/1.50      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_16,c_9,c_8]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2333,plain,
% 7.83/1.50      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2)))) = k7_relat_1(sK2,X0) ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_2329,c_132]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4,plain,
% 7.83/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_621,plain,
% 7.83/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 7.83/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1334,plain,
% 7.83/1.50      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK2))))) = k1_relat_1(k7_relat_1(X0,k1_relat_1(sK2)))
% 7.83/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_621,c_1329]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2449,plain,
% 7.83/1.50      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2))))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2))) ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_616,c_1334]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_607,plain,
% 7.83/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1609,plain,
% 7.83/1.50      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK3)))) = k7_relat_1(sK3,k1_relat_1(X0))
% 7.83/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_607,c_625]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1611,plain,
% 7.83/1.50      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK2)))) = k7_relat_1(sK3,k1_relat_1(X0))
% 7.83/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_1609,c_19]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1621,plain,
% 7.83/1.50      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2)))) = k7_relat_1(sK3,k1_relat_1(k6_relat_1(X0))) ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_616,c_1611]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1625,plain,
% 7.83/1.50      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2)))) = k7_relat_1(sK3,X0) ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_1621,c_132]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2452,plain,
% 7.83/1.50      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK2))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_2449,c_1625]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2678,plain,
% 7.83/1.50      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,X0))) = k7_relat_1(sK2,X0) ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_2333,c_2333,c_2452]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1306,plain,
% 7.83/1.50      ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,X0)))) = k1_relat_1(k7_relat_1(sK3,X0))
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1041,c_619]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1853,plain,
% 7.83/1.50      ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,X0)))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_1306,c_24]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2680,plain,
% 7.83/1.50      ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 7.83/1.50      inference(demodulation,[status(thm)],[c_2678,c_1853]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3050,plain,
% 7.83/1.50      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(sK2,X0) ),
% 7.83/1.50      inference(demodulation,[status(thm)],[c_2680,c_2678]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2572,plain,
% 7.83/1.50      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0))) = k7_relat_1(sK3,X0) ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_1625,c_1625,c_2452]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3051,plain,
% 7.83/1.50      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(sK3,X0) ),
% 7.83/1.50      inference(demodulation,[status(thm)],[c_2680,c_2572]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_11816,plain,
% 7.83/1.50      ( k1_funct_1(sK3,sK0(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK0(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4))))
% 7.83/1.50      | k7_relat_1(sK3,sK4) = k7_relat_1(sK2,sK4)
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.83/1.50      inference(demodulation,[status(thm)],[c_11796,c_3050,c_3051]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_22,negated_conjecture,
% 7.83/1.50      ( v1_funct_1(sK2) ),
% 7.83/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_25,plain,
% 7.83/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_17,negated_conjecture,
% 7.83/1.50      ( k7_relat_1(sK2,sK4) != k7_relat_1(sK3,sK4) ),
% 7.83/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_252,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_658,plain,
% 7.83/1.50      ( k7_relat_1(sK3,sK4) != X0
% 7.83/1.50      | k7_relat_1(sK2,sK4) != X0
% 7.83/1.50      | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_252]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_680,plain,
% 7.83/1.50      ( k7_relat_1(sK3,sK4) != k7_relat_1(X0,sK4)
% 7.83/1.50      | k7_relat_1(sK2,sK4) != k7_relat_1(X0,sK4)
% 7.83/1.50      | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_658]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_681,plain,
% 7.83/1.50      ( k7_relat_1(sK3,sK4) != k7_relat_1(sK2,sK4)
% 7.83/1.50      | k7_relat_1(sK2,sK4) = k7_relat_1(sK3,sK4)
% 7.83/1.50      | k7_relat_1(sK2,sK4) != k7_relat_1(sK2,sK4) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_680]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_251,plain,( X0 = X0 ),theory(equality) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3512,plain,
% 7.83/1.50      ( k7_relat_1(X0,sK4) = k7_relat_1(X0,sK4) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_251]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3513,plain,
% 7.83/1.50      ( k7_relat_1(sK2,sK4) = k7_relat_1(sK2,sK4) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_3512]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_7676,plain,
% 7.83/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK4)),k1_relat_1(X0))
% 7.83/1.50      | ~ v1_relat_1(X0) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_7677,plain,
% 7.83/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK4)),k1_relat_1(X0)) = iProver_top
% 7.83/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_7676]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_7679,plain,
% 7.83/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) = iProver_top
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_7677]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_17750,plain,
% 7.83/1.50      ( k1_funct_1(sK3,sK0(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) = k1_funct_1(sK2,sK0(sK3,sK2,k1_relat_1(k7_relat_1(sK2,sK4)))) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_11816,c_24,c_25,c_17,c_681,c_3513,c_7679]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_10,plain,
% 7.83/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.83/1.50      | ~ r1_tarski(X0,k1_relat_1(X2))
% 7.83/1.50      | ~ v1_funct_1(X1)
% 7.83/1.50      | ~ v1_funct_1(X2)
% 7.83/1.50      | ~ v1_relat_1(X1)
% 7.83/1.50      | ~ v1_relat_1(X2)
% 7.83/1.50      | k1_funct_1(X1,sK0(X2,X1,X0)) != k1_funct_1(X2,sK0(X2,X1,X0))
% 7.83/1.50      | k7_relat_1(X2,X0) = k7_relat_1(X1,X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_615,plain,
% 7.83/1.50      ( k1_funct_1(X0,sK0(X1,X0,X2)) != k1_funct_1(X1,sK0(X1,X0,X2))
% 7.83/1.50      | k7_relat_1(X1,X2) = k7_relat_1(X0,X2)
% 7.83/1.50      | r1_tarski(X2,k1_relat_1(X0)) != iProver_top
% 7.83/1.50      | r1_tarski(X2,k1_relat_1(X1)) != iProver_top
% 7.83/1.50      | v1_funct_1(X0) != iProver_top
% 7.83/1.50      | v1_funct_1(X1) != iProver_top
% 7.83/1.50      | v1_relat_1(X0) != iProver_top
% 7.83/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_17752,plain,
% 7.83/1.50      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK3)) != iProver_top
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_17750,c_615]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_17753,plain,
% 7.83/1.50      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK2,sK4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,sK4)))
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_17752,c_19]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_17754,plain,
% 7.83/1.50      ( k7_relat_1(sK3,sK4) = k7_relat_1(sK2,sK4)
% 7.83/1.50      | r1_tarski(k1_relat_1(k7_relat_1(sK2,sK4)),k1_relat_1(sK2)) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.83/1.50      inference(demodulation,[status(thm)],[c_17753,c_3050,c_3051]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(contradiction,plain,
% 7.83/1.50      ( $false ),
% 7.83/1.50      inference(minisat,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_17754,c_7679,c_3513,c_681,c_17,c_27,c_26,c_25,c_24]) ).
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.83/1.50  
% 7.83/1.50  ------                               Statistics
% 7.83/1.50  
% 7.83/1.50  ------ General
% 7.83/1.50  
% 7.83/1.50  abstr_ref_over_cycles:                  0
% 7.83/1.50  abstr_ref_under_cycles:                 0
% 7.83/1.50  gc_basic_clause_elim:                   0
% 7.83/1.50  forced_gc_time:                         0
% 7.83/1.50  parsing_time:                           0.014
% 7.83/1.50  unif_index_cands_time:                  0.
% 7.83/1.50  unif_index_add_time:                    0.
% 7.83/1.50  orderings_time:                         0.
% 7.83/1.50  out_proof_time:                         0.013
% 7.83/1.50  total_time:                             0.83
% 7.83/1.50  num_of_symbols:                         44
% 7.83/1.50  num_of_terms:                           29357
% 7.83/1.50  
% 7.83/1.50  ------ Preprocessing
% 7.83/1.50  
% 7.83/1.50  num_of_splits:                          0
% 7.83/1.50  num_of_split_atoms:                     0
% 7.83/1.50  num_of_reused_defs:                     0
% 7.83/1.50  num_eq_ax_congr_red:                    8
% 7.83/1.50  num_of_sem_filtered_clauses:            1
% 7.83/1.50  num_of_subtypes:                        0
% 7.83/1.50  monotx_restored_types:                  0
% 7.83/1.50  sat_num_of_epr_types:                   0
% 7.83/1.50  sat_num_of_non_cyclic_types:            0
% 7.83/1.50  sat_guarded_non_collapsed_types:        0
% 7.83/1.50  num_pure_diseq_elim:                    0
% 7.83/1.50  simp_replaced_by:                       0
% 7.83/1.50  res_preprocessed:                       95
% 7.83/1.50  prep_upred:                             0
% 7.83/1.50  prep_unflattend:                        0
% 7.83/1.50  smt_new_axioms:                         0
% 7.83/1.50  pred_elim_cands:                        4
% 7.83/1.50  pred_elim:                              0
% 7.83/1.50  pred_elim_cl:                           0
% 7.83/1.50  pred_elim_cycles:                       1
% 7.83/1.50  merged_defs:                            0
% 7.83/1.50  merged_defs_ncl:                        0
% 7.83/1.50  bin_hyper_res:                          0
% 7.83/1.50  prep_cycles:                            3
% 7.83/1.50  pred_elim_time:                         0.
% 7.83/1.50  splitting_time:                         0.
% 7.83/1.50  sem_filter_time:                        0.
% 7.83/1.50  monotx_time:                            0.001
% 7.83/1.50  subtype_inf_time:                       0.
% 7.83/1.50  
% 7.83/1.50  ------ Problem properties
% 7.83/1.50  
% 7.83/1.50  clauses:                                24
% 7.83/1.50  conjectures:                            7
% 7.83/1.50  epr:                                    4
% 7.83/1.50  horn:                                   22
% 7.83/1.50  ground:                                 6
% 7.83/1.50  unary:                                  9
% 7.83/1.50  binary:                                 3
% 7.83/1.50  lits:                                   71
% 7.83/1.50  lits_eq:                                16
% 7.83/1.50  fd_pure:                                0
% 7.83/1.50  fd_pseudo:                              0
% 7.83/1.50  fd_cond:                                0
% 7.83/1.50  fd_pseudo_cond:                         0
% 7.83/1.50  ac_symbols:                             0
% 7.83/1.50  
% 7.83/1.50  ------ Propositional Solver
% 7.83/1.50  
% 7.83/1.50  prop_solver_calls:                      31
% 7.83/1.50  prop_fast_solver_calls:                 1918
% 7.83/1.50  smt_solver_calls:                       0
% 7.83/1.50  smt_fast_solver_calls:                  0
% 7.83/1.50  prop_num_of_clauses:                    8364
% 7.83/1.50  prop_preprocess_simplified:             11552
% 7.83/1.50  prop_fo_subsumed:                       98
% 7.83/1.50  prop_solver_time:                       0.
% 7.83/1.50  smt_solver_time:                        0.
% 7.83/1.50  smt_fast_solver_time:                   0.
% 7.83/1.50  prop_fast_solver_time:                  0.
% 7.83/1.50  prop_unsat_core_time:                   0.001
% 7.83/1.50  
% 7.83/1.50  ------ QBF
% 7.83/1.50  
% 7.83/1.50  qbf_q_res:                              0
% 7.83/1.50  qbf_num_tautologies:                    0
% 7.83/1.50  qbf_prep_cycles:                        0
% 7.83/1.50  
% 7.83/1.50  ------ BMC1
% 7.83/1.50  
% 7.83/1.50  bmc1_current_bound:                     -1
% 7.83/1.50  bmc1_last_solved_bound:                 -1
% 7.83/1.50  bmc1_unsat_core_size:                   -1
% 7.83/1.50  bmc1_unsat_core_parents_size:           -1
% 7.83/1.50  bmc1_merge_next_fun:                    0
% 7.83/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.83/1.50  
% 7.83/1.50  ------ Instantiation
% 7.83/1.50  
% 7.83/1.50  inst_num_of_clauses:                    2484
% 7.83/1.50  inst_num_in_passive:                    250
% 7.83/1.50  inst_num_in_active:                     1169
% 7.83/1.50  inst_num_in_unprocessed:                1067
% 7.83/1.50  inst_num_of_loops:                      1280
% 7.83/1.50  inst_num_of_learning_restarts:          0
% 7.83/1.50  inst_num_moves_active_passive:          104
% 7.83/1.50  inst_lit_activity:                      0
% 7.83/1.50  inst_lit_activity_moves:                0
% 7.83/1.50  inst_num_tautologies:                   0
% 7.83/1.50  inst_num_prop_implied:                  0
% 7.83/1.50  inst_num_existing_simplified:           0
% 7.83/1.50  inst_num_eq_res_simplified:             0
% 7.83/1.50  inst_num_child_elim:                    0
% 7.83/1.50  inst_num_of_dismatching_blockings:      2074
% 7.83/1.50  inst_num_of_non_proper_insts:           3622
% 7.83/1.50  inst_num_of_duplicates:                 0
% 7.83/1.50  inst_inst_num_from_inst_to_res:         0
% 7.83/1.50  inst_dismatching_checking_time:         0.
% 7.83/1.50  
% 7.83/1.50  ------ Resolution
% 7.83/1.50  
% 7.83/1.50  res_num_of_clauses:                     0
% 7.83/1.50  res_num_in_passive:                     0
% 7.83/1.50  res_num_in_active:                      0
% 7.83/1.50  res_num_of_loops:                       98
% 7.83/1.50  res_forward_subset_subsumed:            286
% 7.83/1.50  res_backward_subset_subsumed:           12
% 7.83/1.50  res_forward_subsumed:                   0
% 7.83/1.50  res_backward_subsumed:                  0
% 7.83/1.50  res_forward_subsumption_resolution:     0
% 7.83/1.50  res_backward_subsumption_resolution:    0
% 7.83/1.50  res_clause_to_clause_subsumption:       5633
% 7.83/1.50  res_orphan_elimination:                 0
% 7.83/1.50  res_tautology_del:                      312
% 7.83/1.50  res_num_eq_res_simplified:              0
% 7.83/1.50  res_num_sel_changes:                    0
% 7.83/1.50  res_moves_from_active_to_pass:          0
% 7.83/1.50  
% 7.83/1.50  ------ Superposition
% 7.83/1.50  
% 7.83/1.50  sup_time_total:                         0.
% 7.83/1.50  sup_time_generating:                    0.
% 7.83/1.50  sup_time_sim_full:                      0.
% 7.83/1.50  sup_time_sim_immed:                     0.
% 7.83/1.50  
% 7.83/1.50  sup_num_of_clauses:                     792
% 7.83/1.50  sup_num_in_active:                      225
% 7.83/1.50  sup_num_in_passive:                     567
% 7.83/1.50  sup_num_of_loops:                       254
% 7.83/1.50  sup_fw_superposition:                   1187
% 7.83/1.50  sup_bw_superposition:                   576
% 7.83/1.50  sup_immediate_simplified:               989
% 7.83/1.50  sup_given_eliminated:                   0
% 7.83/1.50  comparisons_done:                       0
% 7.83/1.50  comparisons_avoided:                    251
% 7.83/1.50  
% 7.83/1.50  ------ Simplifications
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  sim_fw_subset_subsumed:                 56
% 7.83/1.50  sim_bw_subset_subsumed:                 19
% 7.83/1.50  sim_fw_subsumed:                        229
% 7.83/1.50  sim_bw_subsumed:                        31
% 7.83/1.50  sim_fw_subsumption_res:                 0
% 7.83/1.50  sim_bw_subsumption_res:                 0
% 7.83/1.50  sim_tautology_del:                      82
% 7.83/1.50  sim_eq_tautology_del:                   82
% 7.83/1.50  sim_eq_res_simp:                        0
% 7.83/1.50  sim_fw_demodulated:                     513
% 7.83/1.50  sim_bw_demodulated:                     26
% 7.83/1.50  sim_light_normalised:                   537
% 7.83/1.50  sim_joinable_taut:                      0
% 7.83/1.50  sim_joinable_simp:                      0
% 7.83/1.50  sim_ac_normalised:                      0
% 7.83/1.50  sim_smt_subsumption:                    0
% 7.83/1.50  
%------------------------------------------------------------------------------
