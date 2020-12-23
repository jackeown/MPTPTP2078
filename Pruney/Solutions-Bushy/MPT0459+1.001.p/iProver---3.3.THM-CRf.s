%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0459+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:21 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 189 expanded)
%              Number of clauses        :   46 (  50 expanded)
%              Number of leaves         :   17 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  405 ( 935 expanded)
%              Number of equality atoms :   85 ( 173 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f42,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK8(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK7(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK6(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2),sK7(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK8(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f28,f31,f30,f29])).

fof(f47,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
             => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          & r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          & r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          & r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
     => ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(sK11,X0))
        & r1_tarski(k1_relat_1(X0),k2_relat_1(sK11))
        & v1_relat_1(sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
            & r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(sK10) != k2_relat_1(k5_relat_1(X1,sK10))
          & r1_tarski(k1_relat_1(sK10),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k2_relat_1(sK10) != k2_relat_1(k5_relat_1(sK11,sK10))
    & r1_tarski(k1_relat_1(sK10),k2_relat_1(sK11))
    & v1_relat_1(sK11)
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f14,f34,f33])).

fof(f54,plain,(
    r1_tarski(k1_relat_1(sK10),k2_relat_1(sK11)) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19,f18,f17])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f46,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    k2_relat_1(sK10) != k2_relat_1(k5_relat_1(sK11,sK10)) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7437,plain,
    ( r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(k5_relat_1(sK11,sK10)))
    | ~ r2_hidden(k4_tarski(sK5(sK11,sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),k5_relat_1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7438,plain,
    ( r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(k5_relat_1(sK11,sK10))) = iProver_top
    | r2_hidden(k4_tarski(sK5(sK11,sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),k5_relat_1(sK11,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7437])).

cnf(c_12,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_957,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),X1)
    | r2_hidden(k4_tarski(X0,sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),k5_relat_1(X1,sK10))
    | ~ r2_hidden(k4_tarski(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(X1,sK10))
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3590,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK11,sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK11)
    | r2_hidden(k4_tarski(sK5(sK11,sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),k5_relat_1(sK11,sK10))
    | ~ r2_hidden(k4_tarski(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10)
    | ~ v1_relat_1(k5_relat_1(sK11,sK10))
    | ~ v1_relat_1(sK11)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_957])).

cnf(c_3591,plain,
    ( r2_hidden(k4_tarski(sK5(sK11,sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK11) != iProver_top
    | r2_hidden(k4_tarski(sK5(sK11,sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),k5_relat_1(sK11,sK10)) = iProver_top
    | r2_hidden(k4_tarski(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10) != iProver_top
    | v1_relat_1(k5_relat_1(sK11,sK10)) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3590])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | ~ r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_852,plain,
    ( ~ r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(k5_relat_1(sK11,sK10)))
    | ~ r2_hidden(k4_tarski(X0,sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10)
    | k2_relat_1(sK10) = k2_relat_1(k5_relat_1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3477,plain,
    ( ~ r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(k5_relat_1(sK11,sK10)))
    | ~ r2_hidden(k4_tarski(sK5(sK10,sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10)
    | k2_relat_1(sK10) = k2_relat_1(k5_relat_1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_3478,plain,
    ( k2_relat_1(sK10) = k2_relat_1(k5_relat_1(sK11,sK10))
    | r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(k5_relat_1(sK11,sK10))) != iProver_top
    | r2_hidden(k4_tarski(sK5(sK10,sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3477])).

cnf(c_3112,plain,
    ( r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(sK10))
    | ~ r2_hidden(k4_tarski(sK9(sK11,sK10,sK5(k5_relat_1(sK11,sK10),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3113,plain,
    ( r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(sK10)) = iProver_top
    | r2_hidden(k4_tarski(sK9(sK11,sK10,sK5(k5_relat_1(sK11,sK10),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3112])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK5(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2788,plain,
    ( ~ r2_hidden(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(sK11))
    | r2_hidden(k4_tarski(sK5(sK11,sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK11) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2789,plain,
    ( r2_hidden(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(sK5(sK11,sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2788])).

cnf(c_1464,plain,
    ( ~ r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(sK10))
    | r2_hidden(k4_tarski(sK5(sK10,sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1465,plain,
    ( r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(sK10)) != iProver_top
    | r2_hidden(k4_tarski(sK5(sK10,sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1464])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k1_relat_1(sK10),k2_relat_1(sK11)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_216,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k2_relat_1(sK11) != X2
    | k1_relat_1(sK10) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_217,plain,
    ( r2_hidden(X0,k2_relat_1(sK11))
    | ~ r2_hidden(X0,k1_relat_1(sK10)) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_1461,plain,
    ( r2_hidden(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(sK11))
    | ~ r2_hidden(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k1_relat_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_1462,plain,
    ( r2_hidden(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(sK11)) = iProver_top
    | r2_hidden(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k1_relat_1(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1461])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1120,plain,
    ( v1_relat_1(k5_relat_1(sK11,sK10))
    | ~ v1_relat_1(sK11)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1121,plain,
    ( v1_relat_1(k5_relat_1(sK11,sK10)) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_954,plain,
    ( r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(sK10))
    | ~ r2_hidden(k4_tarski(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_955,plain,
    ( r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(sK10)) = iProver_top
    | r2_hidden(k4_tarski(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_951,plain,
    ( r2_hidden(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k1_relat_1(sK10))
    | ~ r2_hidden(k4_tarski(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_952,plain,
    ( r2_hidden(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k1_relat_1(sK10)) = iProver_top
    | r2_hidden(k4_tarski(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_951])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK9(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_909,plain,
    ( r2_hidden(k4_tarski(sK9(sK11,sK10,sK5(k5_relat_1(sK11,sK10),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10)
    | ~ r2_hidden(k4_tarski(sK5(k5_relat_1(sK11,sK10),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),k5_relat_1(sK11,sK10))
    | ~ v1_relat_1(k5_relat_1(sK11,sK10))
    | ~ v1_relat_1(sK11)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_910,plain,
    ( r2_hidden(k4_tarski(sK9(sK11,sK10,sK5(k5_relat_1(sK11,sK10),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10) = iProver_top
    | r2_hidden(k4_tarski(sK5(k5_relat_1(sK11,sK10),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),k5_relat_1(sK11,sK10)) != iProver_top
    | v1_relat_1(k5_relat_1(sK11,sK10)) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_909])).

cnf(c_867,plain,
    ( ~ r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(k5_relat_1(sK11,sK10)))
    | r2_hidden(k4_tarski(sK5(k5_relat_1(sK11,sK10),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),k5_relat_1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_868,plain,
    ( r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(k5_relat_1(sK11,sK10))) != iProver_top
    | r2_hidden(k4_tarski(sK5(k5_relat_1(sK11,sK10),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),k5_relat_1(sK11,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_867])).

cnf(c_6,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_862,plain,
    ( r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(k5_relat_1(sK11,sK10)))
    | r2_hidden(k4_tarski(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10)
    | k2_relat_1(sK10) = k2_relat_1(k5_relat_1(sK11,sK10)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_863,plain,
    ( k2_relat_1(sK10) = k2_relat_1(k5_relat_1(sK11,sK10))
    | r2_hidden(sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),k2_relat_1(k5_relat_1(sK11,sK10))) = iProver_top
    | r2_hidden(k4_tarski(sK4(sK10,k2_relat_1(k5_relat_1(sK11,sK10))),sK3(sK10,k2_relat_1(k5_relat_1(sK11,sK10)))),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_16,negated_conjecture,
    ( k2_relat_1(sK10) != k2_relat_1(k5_relat_1(sK11,sK10)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,plain,
    ( v1_relat_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,plain,
    ( v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7438,c_3591,c_3478,c_3113,c_2789,c_1465,c_1462,c_1121,c_955,c_952,c_910,c_868,c_863,c_16,c_21,c_20])).


%------------------------------------------------------------------------------
