%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:28 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 174 expanded)
%              Number of clauses        :   31 (  35 expanded)
%              Number of leaves         :   17 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  367 ( 897 expanded)
%              Number of equality atoms :   47 ( 135 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

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
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
             => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1))
          & r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1))
          & r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1))
          & r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
     => ( k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,sK11))
        & r1_tarski(k2_relat_1(X0),k1_relat_1(sK11))
        & v1_relat_1(sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1))
            & r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_relat_1(sK10) != k1_relat_1(k5_relat_1(sK10,X1))
          & r1_tarski(k2_relat_1(sK10),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k1_relat_1(sK10) != k1_relat_1(k5_relat_1(sK10,sK11))
    & r1_tarski(k2_relat_1(sK10),k1_relat_1(sK11))
    & v1_relat_1(sK11)
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f14,f34,f33])).

fof(f54,plain,(
    r1_tarski(k2_relat_1(sK10),k1_relat_1(sK11)) ),
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

fof(f45,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    k1_relat_1(sK10) != k1_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_31075,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK11,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11))
    | r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_7131,plain,
    ( r2_hidden(k4_tarski(X0,sK2(sK11,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(X1,sK11))
    | ~ r2_hidden(k4_tarski(X0,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))),X1)
    | ~ r2_hidden(k4_tarski(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK11,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),sK11)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(X1,sK11))
    | ~ v1_relat_1(sK11) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_18405,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK11,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),sK11)
    | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK11,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11))
    | ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))),sK10)
    | ~ v1_relat_1(k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(sK11)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_7131])).

cnf(c_3263,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK9(sK10,sK11,sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))))),sK10)
    | r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0,X1),X2),X0)
    | ~ r2_hidden(sK0(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_852,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),X0),sK10)
    | ~ r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11)))
    | k1_relat_1(sK10) = k1_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3081,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK10,sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),sK10)
    | ~ r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11)))
    | k1_relat_1(sK10) = k1_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2771,plain,
    ( ~ r2_hidden(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK11))
    | r2_hidden(k4_tarski(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK11,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),sK11) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK10),k1_relat_1(sK11)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_216,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k2_relat_1(sK10) != X1
    | k1_relat_1(sK11) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_217,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK10))
    | r2_hidden(X0,k1_relat_1(sK11)) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_1525,plain,
    ( ~ r2_hidden(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(sK10))
    | r2_hidden(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK11)) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_1509,plain,
    ( r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK10,sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),sK10)
    | ~ r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1120,plain,
    ( v1_relat_1(k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(sK11)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_954,plain,
    ( r2_hidden(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(sK10))
    | ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))),sK10) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_951,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))),sK10)
    | r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK9(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_908,plain,
    ( r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK9(sK10,sK11,sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))))),sK10)
    | ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(k5_relat_1(sK10,sK11))
    | ~ v1_relat_1(sK11)
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_867,plain,
    ( r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11))
    | ~ r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
    | r2_hidden(sK0(X0,X1),X1)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_857,plain,
    ( r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))),sK10)
    | r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11)))
    | k1_relat_1(sK10) = k1_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_16,negated_conjecture,
    ( k1_relat_1(sK10) != k1_relat_1(k5_relat_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31075,c_18405,c_3263,c_3081,c_2771,c_1525,c_1509,c_1120,c_954,c_951,c_908,c_867,c_857,c_16,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.62/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/1.48  
% 7.62/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.62/1.48  
% 7.62/1.48  ------  iProver source info
% 7.62/1.48  
% 7.62/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.62/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.62/1.48  git: non_committed_changes: false
% 7.62/1.48  git: last_make_outside_of_git: false
% 7.62/1.48  
% 7.62/1.48  ------ 
% 7.62/1.48  
% 7.62/1.48  ------ Input Options
% 7.62/1.48  
% 7.62/1.48  --out_options                           all
% 7.62/1.48  --tptp_safe_out                         true
% 7.62/1.48  --problem_path                          ""
% 7.62/1.48  --include_path                          ""
% 7.62/1.48  --clausifier                            res/vclausify_rel
% 7.62/1.48  --clausifier_options                    --mode clausify
% 7.62/1.48  --stdin                                 false
% 7.62/1.48  --stats_out                             all
% 7.62/1.48  
% 7.62/1.48  ------ General Options
% 7.62/1.48  
% 7.62/1.48  --fof                                   false
% 7.62/1.48  --time_out_real                         305.
% 7.62/1.48  --time_out_virtual                      -1.
% 7.62/1.48  --symbol_type_check                     false
% 7.62/1.48  --clausify_out                          false
% 7.62/1.48  --sig_cnt_out                           false
% 7.62/1.48  --trig_cnt_out                          false
% 7.62/1.48  --trig_cnt_out_tolerance                1.
% 7.62/1.48  --trig_cnt_out_sk_spl                   false
% 7.62/1.48  --abstr_cl_out                          false
% 7.62/1.48  
% 7.62/1.48  ------ Global Options
% 7.62/1.48  
% 7.62/1.48  --schedule                              default
% 7.62/1.48  --add_important_lit                     false
% 7.62/1.48  --prop_solver_per_cl                    1000
% 7.62/1.48  --min_unsat_core                        false
% 7.62/1.48  --soft_assumptions                      false
% 7.62/1.48  --soft_lemma_size                       3
% 7.62/1.48  --prop_impl_unit_size                   0
% 7.62/1.48  --prop_impl_unit                        []
% 7.62/1.48  --share_sel_clauses                     true
% 7.62/1.48  --reset_solvers                         false
% 7.62/1.48  --bc_imp_inh                            [conj_cone]
% 7.62/1.48  --conj_cone_tolerance                   3.
% 7.62/1.48  --extra_neg_conj                        none
% 7.62/1.48  --large_theory_mode                     true
% 7.62/1.48  --prolific_symb_bound                   200
% 7.62/1.48  --lt_threshold                          2000
% 7.62/1.48  --clause_weak_htbl                      true
% 7.62/1.48  --gc_record_bc_elim                     false
% 7.62/1.48  
% 7.62/1.48  ------ Preprocessing Options
% 7.62/1.48  
% 7.62/1.48  --preprocessing_flag                    true
% 7.62/1.48  --time_out_prep_mult                    0.1
% 7.62/1.48  --splitting_mode                        input
% 7.62/1.48  --splitting_grd                         true
% 7.62/1.48  --splitting_cvd                         false
% 7.62/1.48  --splitting_cvd_svl                     false
% 7.62/1.48  --splitting_nvd                         32
% 7.62/1.48  --sub_typing                            true
% 7.62/1.48  --prep_gs_sim                           true
% 7.62/1.48  --prep_unflatten                        true
% 7.62/1.48  --prep_res_sim                          true
% 7.62/1.48  --prep_upred                            true
% 7.62/1.48  --prep_sem_filter                       exhaustive
% 7.62/1.48  --prep_sem_filter_out                   false
% 7.62/1.48  --pred_elim                             true
% 7.62/1.48  --res_sim_input                         true
% 7.62/1.48  --eq_ax_congr_red                       true
% 7.62/1.48  --pure_diseq_elim                       true
% 7.62/1.48  --brand_transform                       false
% 7.62/1.48  --non_eq_to_eq                          false
% 7.62/1.48  --prep_def_merge                        true
% 7.62/1.48  --prep_def_merge_prop_impl              false
% 7.62/1.48  --prep_def_merge_mbd                    true
% 7.62/1.48  --prep_def_merge_tr_red                 false
% 7.62/1.48  --prep_def_merge_tr_cl                  false
% 7.62/1.48  --smt_preprocessing                     true
% 7.62/1.48  --smt_ac_axioms                         fast
% 7.62/1.48  --preprocessed_out                      false
% 7.62/1.48  --preprocessed_stats                    false
% 7.62/1.48  
% 7.62/1.48  ------ Abstraction refinement Options
% 7.62/1.48  
% 7.62/1.48  --abstr_ref                             []
% 7.62/1.48  --abstr_ref_prep                        false
% 7.62/1.48  --abstr_ref_until_sat                   false
% 7.62/1.48  --abstr_ref_sig_restrict                funpre
% 7.62/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.62/1.48  --abstr_ref_under                       []
% 7.62/1.48  
% 7.62/1.48  ------ SAT Options
% 7.62/1.48  
% 7.62/1.48  --sat_mode                              false
% 7.62/1.48  --sat_fm_restart_options                ""
% 7.62/1.48  --sat_gr_def                            false
% 7.62/1.48  --sat_epr_types                         true
% 7.62/1.48  --sat_non_cyclic_types                  false
% 7.62/1.48  --sat_finite_models                     false
% 7.62/1.48  --sat_fm_lemmas                         false
% 7.62/1.48  --sat_fm_prep                           false
% 7.62/1.48  --sat_fm_uc_incr                        true
% 7.62/1.48  --sat_out_model                         small
% 7.62/1.48  --sat_out_clauses                       false
% 7.62/1.48  
% 7.62/1.48  ------ QBF Options
% 7.62/1.48  
% 7.62/1.48  --qbf_mode                              false
% 7.62/1.48  --qbf_elim_univ                         false
% 7.62/1.48  --qbf_dom_inst                          none
% 7.62/1.48  --qbf_dom_pre_inst                      false
% 7.62/1.48  --qbf_sk_in                             false
% 7.62/1.48  --qbf_pred_elim                         true
% 7.62/1.48  --qbf_split                             512
% 7.62/1.48  
% 7.62/1.48  ------ BMC1 Options
% 7.62/1.48  
% 7.62/1.48  --bmc1_incremental                      false
% 7.62/1.48  --bmc1_axioms                           reachable_all
% 7.62/1.48  --bmc1_min_bound                        0
% 7.62/1.48  --bmc1_max_bound                        -1
% 7.62/1.48  --bmc1_max_bound_default                -1
% 7.62/1.48  --bmc1_symbol_reachability              true
% 7.62/1.48  --bmc1_property_lemmas                  false
% 7.62/1.48  --bmc1_k_induction                      false
% 7.62/1.48  --bmc1_non_equiv_states                 false
% 7.62/1.48  --bmc1_deadlock                         false
% 7.62/1.48  --bmc1_ucm                              false
% 7.62/1.48  --bmc1_add_unsat_core                   none
% 7.62/1.48  --bmc1_unsat_core_children              false
% 7.62/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.62/1.48  --bmc1_out_stat                         full
% 7.62/1.48  --bmc1_ground_init                      false
% 7.62/1.48  --bmc1_pre_inst_next_state              false
% 7.62/1.48  --bmc1_pre_inst_state                   false
% 7.62/1.48  --bmc1_pre_inst_reach_state             false
% 7.62/1.48  --bmc1_out_unsat_core                   false
% 7.62/1.48  --bmc1_aig_witness_out                  false
% 7.62/1.48  --bmc1_verbose                          false
% 7.62/1.48  --bmc1_dump_clauses_tptp                false
% 7.62/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.62/1.48  --bmc1_dump_file                        -
% 7.62/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.62/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.62/1.48  --bmc1_ucm_extend_mode                  1
% 7.62/1.48  --bmc1_ucm_init_mode                    2
% 7.62/1.48  --bmc1_ucm_cone_mode                    none
% 7.62/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.62/1.48  --bmc1_ucm_relax_model                  4
% 7.62/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.62/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.62/1.48  --bmc1_ucm_layered_model                none
% 7.62/1.48  --bmc1_ucm_max_lemma_size               10
% 7.62/1.48  
% 7.62/1.48  ------ AIG Options
% 7.62/1.48  
% 7.62/1.48  --aig_mode                              false
% 7.62/1.48  
% 7.62/1.48  ------ Instantiation Options
% 7.62/1.48  
% 7.62/1.48  --instantiation_flag                    true
% 7.62/1.48  --inst_sos_flag                         false
% 7.62/1.48  --inst_sos_phase                        true
% 7.62/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.62/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.62/1.48  --inst_lit_sel_side                     num_symb
% 7.62/1.48  --inst_solver_per_active                1400
% 7.62/1.48  --inst_solver_calls_frac                1.
% 7.62/1.48  --inst_passive_queue_type               priority_queues
% 7.62/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.62/1.48  --inst_passive_queues_freq              [25;2]
% 7.62/1.48  --inst_dismatching                      true
% 7.62/1.48  --inst_eager_unprocessed_to_passive     true
% 7.62/1.48  --inst_prop_sim_given                   true
% 7.62/1.48  --inst_prop_sim_new                     false
% 7.62/1.48  --inst_subs_new                         false
% 7.62/1.48  --inst_eq_res_simp                      false
% 7.62/1.48  --inst_subs_given                       false
% 7.62/1.48  --inst_orphan_elimination               true
% 7.62/1.48  --inst_learning_loop_flag               true
% 7.62/1.48  --inst_learning_start                   3000
% 7.62/1.48  --inst_learning_factor                  2
% 7.62/1.48  --inst_start_prop_sim_after_learn       3
% 7.62/1.48  --inst_sel_renew                        solver
% 7.62/1.48  --inst_lit_activity_flag                true
% 7.62/1.48  --inst_restr_to_given                   false
% 7.62/1.48  --inst_activity_threshold               500
% 7.62/1.48  --inst_out_proof                        true
% 7.62/1.48  
% 7.62/1.48  ------ Resolution Options
% 7.62/1.48  
% 7.62/1.48  --resolution_flag                       true
% 7.62/1.48  --res_lit_sel                           adaptive
% 7.62/1.48  --res_lit_sel_side                      none
% 7.62/1.48  --res_ordering                          kbo
% 7.62/1.48  --res_to_prop_solver                    active
% 7.62/1.48  --res_prop_simpl_new                    false
% 7.62/1.48  --res_prop_simpl_given                  true
% 7.62/1.48  --res_passive_queue_type                priority_queues
% 7.62/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.62/1.48  --res_passive_queues_freq               [15;5]
% 7.62/1.48  --res_forward_subs                      full
% 7.62/1.48  --res_backward_subs                     full
% 7.62/1.48  --res_forward_subs_resolution           true
% 7.62/1.48  --res_backward_subs_resolution          true
% 7.62/1.48  --res_orphan_elimination                true
% 7.62/1.48  --res_time_limit                        2.
% 7.62/1.48  --res_out_proof                         true
% 7.62/1.48  
% 7.62/1.48  ------ Superposition Options
% 7.62/1.48  
% 7.62/1.48  --superposition_flag                    true
% 7.62/1.48  --sup_passive_queue_type                priority_queues
% 7.62/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.62/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.62/1.48  --demod_completeness_check              fast
% 7.62/1.48  --demod_use_ground                      true
% 7.62/1.48  --sup_to_prop_solver                    passive
% 7.62/1.48  --sup_prop_simpl_new                    true
% 7.62/1.48  --sup_prop_simpl_given                  true
% 7.62/1.48  --sup_fun_splitting                     false
% 7.62/1.48  --sup_smt_interval                      50000
% 7.62/1.48  
% 7.62/1.48  ------ Superposition Simplification Setup
% 7.62/1.48  
% 7.62/1.48  --sup_indices_passive                   []
% 7.62/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.62/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.48  --sup_full_bw                           [BwDemod]
% 7.62/1.48  --sup_immed_triv                        [TrivRules]
% 7.62/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.48  --sup_immed_bw_main                     []
% 7.62/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.62/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.62/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.62/1.48  
% 7.62/1.48  ------ Combination Options
% 7.62/1.48  
% 7.62/1.48  --comb_res_mult                         3
% 7.62/1.48  --comb_sup_mult                         2
% 7.62/1.48  --comb_inst_mult                        10
% 7.62/1.48  
% 7.62/1.48  ------ Debug Options
% 7.62/1.48  
% 7.62/1.48  --dbg_backtrace                         false
% 7.62/1.48  --dbg_dump_prop_clauses                 false
% 7.62/1.48  --dbg_dump_prop_clauses_file            -
% 7.62/1.48  --dbg_out_stat                          false
% 7.62/1.48  ------ Parsing...
% 7.62/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.62/1.48  
% 7.62/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.62/1.48  
% 7.62/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.62/1.48  
% 7.62/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.48  ------ Proving...
% 7.62/1.48  ------ Problem Properties 
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  clauses                                 19
% 7.62/1.48  conjectures                             3
% 7.62/1.48  EPR                                     2
% 7.62/1.48  Horn                                    15
% 7.62/1.48  unary                                   3
% 7.62/1.48  binary                                  5
% 7.62/1.48  lits                                    63
% 7.62/1.48  lits eq                                 8
% 7.62/1.48  fd_pure                                 0
% 7.62/1.48  fd_pseudo                               0
% 7.62/1.48  fd_cond                                 0
% 7.62/1.48  fd_pseudo_cond                          7
% 7.62/1.48  AC symbols                              0
% 7.62/1.48  
% 7.62/1.48  ------ Schedule dynamic 5 is on 
% 7.62/1.48  
% 7.62/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  ------ 
% 7.62/1.48  Current options:
% 7.62/1.48  ------ 
% 7.62/1.48  
% 7.62/1.48  ------ Input Options
% 7.62/1.48  
% 7.62/1.48  --out_options                           all
% 7.62/1.48  --tptp_safe_out                         true
% 7.62/1.48  --problem_path                          ""
% 7.62/1.48  --include_path                          ""
% 7.62/1.48  --clausifier                            res/vclausify_rel
% 7.62/1.48  --clausifier_options                    --mode clausify
% 7.62/1.48  --stdin                                 false
% 7.62/1.48  --stats_out                             all
% 7.62/1.48  
% 7.62/1.48  ------ General Options
% 7.62/1.48  
% 7.62/1.48  --fof                                   false
% 7.62/1.48  --time_out_real                         305.
% 7.62/1.48  --time_out_virtual                      -1.
% 7.62/1.48  --symbol_type_check                     false
% 7.62/1.48  --clausify_out                          false
% 7.62/1.48  --sig_cnt_out                           false
% 7.62/1.48  --trig_cnt_out                          false
% 7.62/1.48  --trig_cnt_out_tolerance                1.
% 7.62/1.48  --trig_cnt_out_sk_spl                   false
% 7.62/1.48  --abstr_cl_out                          false
% 7.62/1.48  
% 7.62/1.48  ------ Global Options
% 7.62/1.48  
% 7.62/1.48  --schedule                              default
% 7.62/1.48  --add_important_lit                     false
% 7.62/1.48  --prop_solver_per_cl                    1000
% 7.62/1.48  --min_unsat_core                        false
% 7.62/1.48  --soft_assumptions                      false
% 7.62/1.48  --soft_lemma_size                       3
% 7.62/1.48  --prop_impl_unit_size                   0
% 7.62/1.48  --prop_impl_unit                        []
% 7.62/1.48  --share_sel_clauses                     true
% 7.62/1.48  --reset_solvers                         false
% 7.62/1.48  --bc_imp_inh                            [conj_cone]
% 7.62/1.48  --conj_cone_tolerance                   3.
% 7.62/1.48  --extra_neg_conj                        none
% 7.62/1.48  --large_theory_mode                     true
% 7.62/1.48  --prolific_symb_bound                   200
% 7.62/1.48  --lt_threshold                          2000
% 7.62/1.48  --clause_weak_htbl                      true
% 7.62/1.48  --gc_record_bc_elim                     false
% 7.62/1.48  
% 7.62/1.48  ------ Preprocessing Options
% 7.62/1.48  
% 7.62/1.48  --preprocessing_flag                    true
% 7.62/1.48  --time_out_prep_mult                    0.1
% 7.62/1.48  --splitting_mode                        input
% 7.62/1.48  --splitting_grd                         true
% 7.62/1.48  --splitting_cvd                         false
% 7.62/1.48  --splitting_cvd_svl                     false
% 7.62/1.48  --splitting_nvd                         32
% 7.62/1.48  --sub_typing                            true
% 7.62/1.48  --prep_gs_sim                           true
% 7.62/1.48  --prep_unflatten                        true
% 7.62/1.48  --prep_res_sim                          true
% 7.62/1.48  --prep_upred                            true
% 7.62/1.48  --prep_sem_filter                       exhaustive
% 7.62/1.48  --prep_sem_filter_out                   false
% 7.62/1.48  --pred_elim                             true
% 7.62/1.48  --res_sim_input                         true
% 7.62/1.48  --eq_ax_congr_red                       true
% 7.62/1.48  --pure_diseq_elim                       true
% 7.62/1.48  --brand_transform                       false
% 7.62/1.48  --non_eq_to_eq                          false
% 7.62/1.48  --prep_def_merge                        true
% 7.62/1.48  --prep_def_merge_prop_impl              false
% 7.62/1.48  --prep_def_merge_mbd                    true
% 7.62/1.48  --prep_def_merge_tr_red                 false
% 7.62/1.48  --prep_def_merge_tr_cl                  false
% 7.62/1.48  --smt_preprocessing                     true
% 7.62/1.48  --smt_ac_axioms                         fast
% 7.62/1.48  --preprocessed_out                      false
% 7.62/1.48  --preprocessed_stats                    false
% 7.62/1.48  
% 7.62/1.48  ------ Abstraction refinement Options
% 7.62/1.48  
% 7.62/1.48  --abstr_ref                             []
% 7.62/1.48  --abstr_ref_prep                        false
% 7.62/1.48  --abstr_ref_until_sat                   false
% 7.62/1.48  --abstr_ref_sig_restrict                funpre
% 7.62/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.62/1.48  --abstr_ref_under                       []
% 7.62/1.48  
% 7.62/1.48  ------ SAT Options
% 7.62/1.48  
% 7.62/1.48  --sat_mode                              false
% 7.62/1.48  --sat_fm_restart_options                ""
% 7.62/1.48  --sat_gr_def                            false
% 7.62/1.48  --sat_epr_types                         true
% 7.62/1.48  --sat_non_cyclic_types                  false
% 7.62/1.48  --sat_finite_models                     false
% 7.62/1.48  --sat_fm_lemmas                         false
% 7.62/1.48  --sat_fm_prep                           false
% 7.62/1.48  --sat_fm_uc_incr                        true
% 7.62/1.48  --sat_out_model                         small
% 7.62/1.48  --sat_out_clauses                       false
% 7.62/1.48  
% 7.62/1.48  ------ QBF Options
% 7.62/1.48  
% 7.62/1.48  --qbf_mode                              false
% 7.62/1.48  --qbf_elim_univ                         false
% 7.62/1.48  --qbf_dom_inst                          none
% 7.62/1.48  --qbf_dom_pre_inst                      false
% 7.62/1.48  --qbf_sk_in                             false
% 7.62/1.48  --qbf_pred_elim                         true
% 7.62/1.48  --qbf_split                             512
% 7.62/1.48  
% 7.62/1.48  ------ BMC1 Options
% 7.62/1.48  
% 7.62/1.48  --bmc1_incremental                      false
% 7.62/1.48  --bmc1_axioms                           reachable_all
% 7.62/1.48  --bmc1_min_bound                        0
% 7.62/1.48  --bmc1_max_bound                        -1
% 7.62/1.48  --bmc1_max_bound_default                -1
% 7.62/1.48  --bmc1_symbol_reachability              true
% 7.62/1.48  --bmc1_property_lemmas                  false
% 7.62/1.48  --bmc1_k_induction                      false
% 7.62/1.48  --bmc1_non_equiv_states                 false
% 7.62/1.48  --bmc1_deadlock                         false
% 7.62/1.48  --bmc1_ucm                              false
% 7.62/1.48  --bmc1_add_unsat_core                   none
% 7.62/1.48  --bmc1_unsat_core_children              false
% 7.62/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.62/1.48  --bmc1_out_stat                         full
% 7.62/1.48  --bmc1_ground_init                      false
% 7.62/1.48  --bmc1_pre_inst_next_state              false
% 7.62/1.48  --bmc1_pre_inst_state                   false
% 7.62/1.48  --bmc1_pre_inst_reach_state             false
% 7.62/1.48  --bmc1_out_unsat_core                   false
% 7.62/1.48  --bmc1_aig_witness_out                  false
% 7.62/1.48  --bmc1_verbose                          false
% 7.62/1.48  --bmc1_dump_clauses_tptp                false
% 7.62/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.62/1.48  --bmc1_dump_file                        -
% 7.62/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.62/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.62/1.48  --bmc1_ucm_extend_mode                  1
% 7.62/1.48  --bmc1_ucm_init_mode                    2
% 7.62/1.48  --bmc1_ucm_cone_mode                    none
% 7.62/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.62/1.48  --bmc1_ucm_relax_model                  4
% 7.62/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.62/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.62/1.48  --bmc1_ucm_layered_model                none
% 7.62/1.48  --bmc1_ucm_max_lemma_size               10
% 7.62/1.48  
% 7.62/1.48  ------ AIG Options
% 7.62/1.48  
% 7.62/1.48  --aig_mode                              false
% 7.62/1.48  
% 7.62/1.48  ------ Instantiation Options
% 7.62/1.48  
% 7.62/1.48  --instantiation_flag                    true
% 7.62/1.48  --inst_sos_flag                         false
% 7.62/1.48  --inst_sos_phase                        true
% 7.62/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.62/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.62/1.48  --inst_lit_sel_side                     none
% 7.62/1.48  --inst_solver_per_active                1400
% 7.62/1.48  --inst_solver_calls_frac                1.
% 7.62/1.48  --inst_passive_queue_type               priority_queues
% 7.62/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.62/1.48  --inst_passive_queues_freq              [25;2]
% 7.62/1.48  --inst_dismatching                      true
% 7.62/1.48  --inst_eager_unprocessed_to_passive     true
% 7.62/1.48  --inst_prop_sim_given                   true
% 7.62/1.48  --inst_prop_sim_new                     false
% 7.62/1.48  --inst_subs_new                         false
% 7.62/1.48  --inst_eq_res_simp                      false
% 7.62/1.48  --inst_subs_given                       false
% 7.62/1.48  --inst_orphan_elimination               true
% 7.62/1.48  --inst_learning_loop_flag               true
% 7.62/1.48  --inst_learning_start                   3000
% 7.62/1.48  --inst_learning_factor                  2
% 7.62/1.48  --inst_start_prop_sim_after_learn       3
% 7.62/1.48  --inst_sel_renew                        solver
% 7.62/1.48  --inst_lit_activity_flag                true
% 7.62/1.48  --inst_restr_to_given                   false
% 7.62/1.48  --inst_activity_threshold               500
% 7.62/1.48  --inst_out_proof                        true
% 7.62/1.48  
% 7.62/1.48  ------ Resolution Options
% 7.62/1.48  
% 7.62/1.48  --resolution_flag                       false
% 7.62/1.48  --res_lit_sel                           adaptive
% 7.62/1.48  --res_lit_sel_side                      none
% 7.62/1.48  --res_ordering                          kbo
% 7.62/1.48  --res_to_prop_solver                    active
% 7.62/1.48  --res_prop_simpl_new                    false
% 7.62/1.48  --res_prop_simpl_given                  true
% 7.62/1.48  --res_passive_queue_type                priority_queues
% 7.62/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.62/1.48  --res_passive_queues_freq               [15;5]
% 7.62/1.48  --res_forward_subs                      full
% 7.62/1.48  --res_backward_subs                     full
% 7.62/1.48  --res_forward_subs_resolution           true
% 7.62/1.48  --res_backward_subs_resolution          true
% 7.62/1.48  --res_orphan_elimination                true
% 7.62/1.48  --res_time_limit                        2.
% 7.62/1.48  --res_out_proof                         true
% 7.62/1.48  
% 7.62/1.48  ------ Superposition Options
% 7.62/1.48  
% 7.62/1.48  --superposition_flag                    true
% 7.62/1.48  --sup_passive_queue_type                priority_queues
% 7.62/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.62/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.62/1.48  --demod_completeness_check              fast
% 7.62/1.48  --demod_use_ground                      true
% 7.62/1.48  --sup_to_prop_solver                    passive
% 7.62/1.48  --sup_prop_simpl_new                    true
% 7.62/1.48  --sup_prop_simpl_given                  true
% 7.62/1.48  --sup_fun_splitting                     false
% 7.62/1.48  --sup_smt_interval                      50000
% 7.62/1.48  
% 7.62/1.48  ------ Superposition Simplification Setup
% 7.62/1.48  
% 7.62/1.48  --sup_indices_passive                   []
% 7.62/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.62/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.48  --sup_full_bw                           [BwDemod]
% 7.62/1.48  --sup_immed_triv                        [TrivRules]
% 7.62/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.48  --sup_immed_bw_main                     []
% 7.62/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.62/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.62/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.62/1.48  
% 7.62/1.48  ------ Combination Options
% 7.62/1.48  
% 7.62/1.48  --comb_res_mult                         3
% 7.62/1.48  --comb_sup_mult                         2
% 7.62/1.48  --comb_inst_mult                        10
% 7.62/1.48  
% 7.62/1.48  ------ Debug Options
% 7.62/1.48  
% 7.62/1.48  --dbg_backtrace                         false
% 7.62/1.48  --dbg_dump_prop_clauses                 false
% 7.62/1.48  --dbg_dump_prop_clauses_file            -
% 7.62/1.48  --dbg_out_stat                          false
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  ------ Proving...
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  % SZS status Theorem for theBenchmark.p
% 7.62/1.48  
% 7.62/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.62/1.48  
% 7.62/1.48  fof(f2,axiom,(
% 7.62/1.48    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f15,plain,(
% 7.62/1.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 7.62/1.48    inference(nnf_transformation,[],[f2])).
% 7.62/1.48  
% 7.62/1.48  fof(f16,plain,(
% 7.62/1.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.62/1.48    inference(rectify,[],[f15])).
% 7.62/1.48  
% 7.62/1.48  fof(f19,plain,(
% 7.62/1.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0))),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f18,plain,(
% 7.62/1.48    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0))) )),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f17,plain,(
% 7.62/1.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f20,plain,(
% 7.62/1.48    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 7.62/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19,f18,f17])).
% 7.62/1.48  
% 7.62/1.48  fof(f38,plain,(
% 7.62/1.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 7.62/1.48    inference(cnf_transformation,[],[f20])).
% 7.62/1.48  
% 7.62/1.48  fof(f56,plain,(
% 7.62/1.48    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 7.62/1.48    inference(equality_resolution,[],[f38])).
% 7.62/1.48  
% 7.62/1.48  fof(f4,axiom,(
% 7.62/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f10,plain,(
% 7.62/1.48    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.62/1.48    inference(ennf_transformation,[],[f4])).
% 7.62/1.48  
% 7.62/1.48  fof(f27,plain,(
% 7.62/1.48    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.62/1.48    inference(nnf_transformation,[],[f10])).
% 7.62/1.48  
% 7.62/1.48  fof(f28,plain,(
% 7.62/1.48    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.62/1.48    inference(rectify,[],[f27])).
% 7.62/1.48  
% 7.62/1.48  fof(f31,plain,(
% 7.62/1.48    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)))),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f30,plain,(
% 7.62/1.48    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK8(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK8(X0,X1,X2)),X0)))) )),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f29,plain,(
% 7.62/1.48    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK7(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2))))),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f32,plain,(
% 7.62/1.48    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK8(X0,X1,X2),sK7(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK8(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.62/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f28,f31,f30,f29])).
% 7.62/1.48  
% 7.62/1.48  fof(f47,plain,(
% 7.62/1.48    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f32])).
% 7.62/1.48  
% 7.62/1.48  fof(f60,plain,(
% 7.62/1.48    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.62/1.48    inference(equality_resolution,[],[f47])).
% 7.62/1.48  
% 7.62/1.48  fof(f40,plain,(
% 7.62/1.48    ( ! [X0,X3,X1] : (k1_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f20])).
% 7.62/1.48  
% 7.62/1.48  fof(f37,plain,(
% 7.62/1.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 7.62/1.48    inference(cnf_transformation,[],[f20])).
% 7.62/1.48  
% 7.62/1.48  fof(f57,plain,(
% 7.62/1.48    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 7.62/1.48    inference(equality_resolution,[],[f37])).
% 7.62/1.48  
% 7.62/1.48  fof(f1,axiom,(
% 7.62/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f8,plain,(
% 7.62/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.62/1.48    inference(unused_predicate_definition_removal,[],[f1])).
% 7.62/1.48  
% 7.62/1.48  fof(f9,plain,(
% 7.62/1.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 7.62/1.48    inference(ennf_transformation,[],[f8])).
% 7.62/1.48  
% 7.62/1.48  fof(f36,plain,(
% 7.62/1.48    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f9])).
% 7.62/1.48  
% 7.62/1.48  fof(f6,conjecture,(
% 7.62/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f7,negated_conjecture,(
% 7.62/1.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 7.62/1.48    inference(negated_conjecture,[],[f6])).
% 7.62/1.48  
% 7.62/1.48  fof(f13,plain,(
% 7.62/1.48    ? [X0] : (? [X1] : ((k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1)) & r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.62/1.48    inference(ennf_transformation,[],[f7])).
% 7.62/1.48  
% 7.62/1.48  fof(f14,plain,(
% 7.62/1.48    ? [X0] : (? [X1] : (k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1)) & r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.62/1.48    inference(flattening,[],[f13])).
% 7.62/1.48  
% 7.62/1.48  fof(f34,plain,(
% 7.62/1.48    ( ! [X0] : (? [X1] : (k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1)) & r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,sK11)) & r1_tarski(k2_relat_1(X0),k1_relat_1(sK11)) & v1_relat_1(sK11))) )),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f33,plain,(
% 7.62/1.48    ? [X0] : (? [X1] : (k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1)) & r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k1_relat_1(sK10) != k1_relat_1(k5_relat_1(sK10,X1)) & r1_tarski(k2_relat_1(sK10),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK10))),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f35,plain,(
% 7.62/1.48    (k1_relat_1(sK10) != k1_relat_1(k5_relat_1(sK10,sK11)) & r1_tarski(k2_relat_1(sK10),k1_relat_1(sK11)) & v1_relat_1(sK11)) & v1_relat_1(sK10)),
% 7.62/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f14,f34,f33])).
% 7.62/1.48  
% 7.62/1.48  fof(f54,plain,(
% 7.62/1.48    r1_tarski(k2_relat_1(sK10),k1_relat_1(sK11))),
% 7.62/1.48    inference(cnf_transformation,[],[f35])).
% 7.62/1.48  
% 7.62/1.48  fof(f5,axiom,(
% 7.62/1.48    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f11,plain,(
% 7.62/1.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 7.62/1.48    inference(ennf_transformation,[],[f5])).
% 7.62/1.48  
% 7.62/1.48  fof(f12,plain,(
% 7.62/1.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 7.62/1.48    inference(flattening,[],[f11])).
% 7.62/1.48  
% 7.62/1.48  fof(f51,plain,(
% 7.62/1.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f12])).
% 7.62/1.48  
% 7.62/1.48  fof(f3,axiom,(
% 7.62/1.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f21,plain,(
% 7.62/1.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 7.62/1.48    inference(nnf_transformation,[],[f3])).
% 7.62/1.48  
% 7.62/1.48  fof(f22,plain,(
% 7.62/1.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.62/1.48    inference(rectify,[],[f21])).
% 7.62/1.48  
% 7.62/1.48  fof(f25,plain,(
% 7.62/1.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f24,plain,(
% 7.62/1.48    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK4(X0,X1),X2),X0))) )),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f23,plain,(
% 7.62/1.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f26,plain,(
% 7.62/1.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 7.62/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 7.62/1.48  
% 7.62/1.48  fof(f42,plain,(
% 7.62/1.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 7.62/1.48    inference(cnf_transformation,[],[f26])).
% 7.62/1.48  
% 7.62/1.48  fof(f58,plain,(
% 7.62/1.48    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 7.62/1.48    inference(equality_resolution,[],[f42])).
% 7.62/1.48  
% 7.62/1.48  fof(f45,plain,(
% 7.62/1.48    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f32])).
% 7.62/1.48  
% 7.62/1.48  fof(f62,plain,(
% 7.62/1.48    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.62/1.48    inference(equality_resolution,[],[f45])).
% 7.62/1.48  
% 7.62/1.48  fof(f39,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f20])).
% 7.62/1.48  
% 7.62/1.48  fof(f55,plain,(
% 7.62/1.48    k1_relat_1(sK10) != k1_relat_1(k5_relat_1(sK10,sK11))),
% 7.62/1.48    inference(cnf_transformation,[],[f35])).
% 7.62/1.48  
% 7.62/1.48  fof(f53,plain,(
% 7.62/1.48    v1_relat_1(sK11)),
% 7.62/1.48    inference(cnf_transformation,[],[f35])).
% 7.62/1.48  
% 7.62/1.48  fof(f52,plain,(
% 7.62/1.48    v1_relat_1(sK10)),
% 7.62/1.48    inference(cnf_transformation,[],[f35])).
% 7.62/1.48  
% 7.62/1.48  cnf(c_3,plain,
% 7.62/1.48      ( r2_hidden(X0,k1_relat_1(X1)) | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
% 7.62/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_31075,plain,
% 7.62/1.48      ( ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK11,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11))
% 7.62/1.48      | r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11))) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_12,plain,
% 7.62/1.48      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.62/1.48      | ~ r2_hidden(k4_tarski(X3,X0),X4)
% 7.62/1.48      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
% 7.62/1.48      | ~ v1_relat_1(X2)
% 7.62/1.48      | ~ v1_relat_1(X4)
% 7.62/1.48      | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
% 7.62/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_7131,plain,
% 7.62/1.48      ( r2_hidden(k4_tarski(X0,sK2(sK11,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(X1,sK11))
% 7.62/1.48      | ~ r2_hidden(k4_tarski(X0,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))),X1)
% 7.62/1.48      | ~ r2_hidden(k4_tarski(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK11,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),sK11)
% 7.62/1.48      | ~ v1_relat_1(X1)
% 7.62/1.48      | ~ v1_relat_1(k5_relat_1(X1,sK11))
% 7.62/1.48      | ~ v1_relat_1(sK11) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_18405,plain,
% 7.62/1.48      ( ~ r2_hidden(k4_tarski(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK11,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),sK11)
% 7.62/1.48      | r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK11,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11))
% 7.62/1.48      | ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))),sK10)
% 7.62/1.48      | ~ v1_relat_1(k5_relat_1(sK10,sK11))
% 7.62/1.48      | ~ v1_relat_1(sK11)
% 7.62/1.48      | ~ v1_relat_1(sK10) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_7131]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_3263,plain,
% 7.62/1.48      ( ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK9(sK10,sK11,sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))))),sK10)
% 7.62/1.48      | r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK10)) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1,plain,
% 7.62/1.48      ( ~ r2_hidden(k4_tarski(sK0(X0,X1),X2),X0)
% 7.62/1.48      | ~ r2_hidden(sK0(X0,X1),X1)
% 7.62/1.48      | k1_relat_1(X0) = X1 ),
% 7.62/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_852,plain,
% 7.62/1.48      ( ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),X0),sK10)
% 7.62/1.48      | ~ r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11)))
% 7.62/1.48      | k1_relat_1(sK10) = k1_relat_1(k5_relat_1(sK10,sK11)) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_3081,plain,
% 7.62/1.48      ( ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK10,sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),sK10)
% 7.62/1.48      | ~ r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11)))
% 7.62/1.48      | k1_relat_1(sK10) = k1_relat_1(k5_relat_1(sK10,sK11)) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_852]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_4,plain,
% 7.62/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.62/1.48      | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
% 7.62/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_2771,plain,
% 7.62/1.48      ( ~ r2_hidden(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK11))
% 7.62/1.48      | r2_hidden(k4_tarski(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK11,sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),sK11) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_4]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_0,plain,
% 7.62/1.48      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.62/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_17,negated_conjecture,
% 7.62/1.48      ( r1_tarski(k2_relat_1(sK10),k1_relat_1(sK11)) ),
% 7.62/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_216,plain,
% 7.62/1.48      ( ~ r2_hidden(X0,X1)
% 7.62/1.48      | r2_hidden(X0,X2)
% 7.62/1.48      | k2_relat_1(sK10) != X1
% 7.62/1.48      | k1_relat_1(sK11) != X2 ),
% 7.62/1.48      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_217,plain,
% 7.62/1.48      ( ~ r2_hidden(X0,k2_relat_1(sK10))
% 7.62/1.48      | r2_hidden(X0,k1_relat_1(sK11)) ),
% 7.62/1.48      inference(unflattening,[status(thm)],[c_216]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1525,plain,
% 7.62/1.48      ( ~ r2_hidden(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(sK10))
% 7.62/1.48      | r2_hidden(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK11)) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_217]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1509,plain,
% 7.62/1.48      ( r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(sK10,sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),sK10)
% 7.62/1.48      | ~ r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK10)) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_4]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_15,plain,
% 7.62/1.48      ( ~ v1_relat_1(X0)
% 7.62/1.48      | ~ v1_relat_1(X1)
% 7.62/1.48      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 7.62/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1120,plain,
% 7.62/1.48      ( v1_relat_1(k5_relat_1(sK10,sK11))
% 7.62/1.48      | ~ v1_relat_1(sK11)
% 7.62/1.48      | ~ v1_relat_1(sK10) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_15]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_7,plain,
% 7.62/1.48      ( r2_hidden(X0,k2_relat_1(X1)) | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
% 7.62/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_954,plain,
% 7.62/1.48      ( r2_hidden(sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k2_relat_1(sK10))
% 7.62/1.48      | ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))),sK10) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_7]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_951,plain,
% 7.62/1.48      ( ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))),sK10)
% 7.62/1.48      | r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(sK10)) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_14,plain,
% 7.62/1.48      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 7.62/1.48      | r2_hidden(k4_tarski(X0,sK9(X2,X3,X0,X1)),X2)
% 7.62/1.48      | ~ v1_relat_1(X3)
% 7.62/1.48      | ~ v1_relat_1(X2)
% 7.62/1.48      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 7.62/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_908,plain,
% 7.62/1.48      ( r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK9(sK10,sK11,sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))))),sK10)
% 7.62/1.48      | ~ r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11))
% 7.62/1.48      | ~ v1_relat_1(k5_relat_1(sK10,sK11))
% 7.62/1.48      | ~ v1_relat_1(sK11)
% 7.62/1.48      | ~ v1_relat_1(sK10) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_14]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_867,plain,
% 7.62/1.48      ( r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK2(k5_relat_1(sK10,sK11),sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))))),k5_relat_1(sK10,sK11))
% 7.62/1.48      | ~ r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11))) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_4]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_2,plain,
% 7.62/1.48      ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
% 7.62/1.48      | r2_hidden(sK0(X0,X1),X1)
% 7.62/1.48      | k1_relat_1(X0) = X1 ),
% 7.62/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_857,plain,
% 7.62/1.48      ( r2_hidden(k4_tarski(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),sK1(sK10,k1_relat_1(k5_relat_1(sK10,sK11)))),sK10)
% 7.62/1.48      | r2_hidden(sK0(sK10,k1_relat_1(k5_relat_1(sK10,sK11))),k1_relat_1(k5_relat_1(sK10,sK11)))
% 7.62/1.48      | k1_relat_1(sK10) = k1_relat_1(k5_relat_1(sK10,sK11)) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_16,negated_conjecture,
% 7.62/1.48      ( k1_relat_1(sK10) != k1_relat_1(k5_relat_1(sK10,sK11)) ),
% 7.62/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_18,negated_conjecture,
% 7.62/1.48      ( v1_relat_1(sK11) ),
% 7.62/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_19,negated_conjecture,
% 7.62/1.48      ( v1_relat_1(sK10) ),
% 7.62/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(contradiction,plain,
% 7.62/1.48      ( $false ),
% 7.62/1.48      inference(minisat,
% 7.62/1.48                [status(thm)],
% 7.62/1.48                [c_31075,c_18405,c_3263,c_3081,c_2771,c_1525,c_1509,
% 7.62/1.48                 c_1120,c_954,c_951,c_908,c_867,c_857,c_16,c_18,c_19]) ).
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.62/1.48  
% 7.62/1.48  ------                               Statistics
% 7.62/1.48  
% 7.62/1.48  ------ General
% 7.62/1.48  
% 7.62/1.48  abstr_ref_over_cycles:                  0
% 7.62/1.48  abstr_ref_under_cycles:                 0
% 7.62/1.48  gc_basic_clause_elim:                   0
% 7.62/1.48  forced_gc_time:                         0
% 7.62/1.48  parsing_time:                           0.011
% 7.62/1.48  unif_index_cands_time:                  0.
% 7.62/1.48  unif_index_add_time:                    0.
% 7.62/1.48  orderings_time:                         0.
% 7.62/1.48  out_proof_time:                         0.01
% 7.62/1.48  total_time:                             0.858
% 7.62/1.48  num_of_symbols:                         50
% 7.62/1.48  num_of_terms:                           36808
% 7.62/1.48  
% 7.62/1.48  ------ Preprocessing
% 7.62/1.48  
% 7.62/1.48  num_of_splits:                          0
% 7.62/1.48  num_of_split_atoms:                     0
% 7.62/1.48  num_of_reused_defs:                     0
% 7.62/1.48  num_eq_ax_congr_red:                    75
% 7.62/1.48  num_of_sem_filtered_clauses:            1
% 7.62/1.48  num_of_subtypes:                        0
% 7.62/1.48  monotx_restored_types:                  0
% 7.62/1.48  sat_num_of_epr_types:                   0
% 7.62/1.48  sat_num_of_non_cyclic_types:            0
% 7.62/1.48  sat_guarded_non_collapsed_types:        0
% 7.62/1.48  num_pure_diseq_elim:                    0
% 7.62/1.48  simp_replaced_by:                       0
% 7.62/1.48  res_preprocessed:                       94
% 7.62/1.48  prep_upred:                             0
% 7.62/1.48  prep_unflattend:                        2
% 7.62/1.48  smt_new_axioms:                         0
% 7.62/1.48  pred_elim_cands:                        2
% 7.62/1.48  pred_elim:                              1
% 7.62/1.48  pred_elim_cl:                           1
% 7.62/1.48  pred_elim_cycles:                       3
% 7.62/1.48  merged_defs:                            0
% 7.62/1.48  merged_defs_ncl:                        0
% 7.62/1.48  bin_hyper_res:                          0
% 7.62/1.48  prep_cycles:                            4
% 7.62/1.48  pred_elim_time:                         0.001
% 7.62/1.48  splitting_time:                         0.
% 7.62/1.48  sem_filter_time:                        0.
% 7.62/1.48  monotx_time:                            0.
% 7.62/1.48  subtype_inf_time:                       0.
% 7.62/1.48  
% 7.62/1.48  ------ Problem properties
% 7.62/1.48  
% 7.62/1.48  clauses:                                19
% 7.62/1.48  conjectures:                            3
% 7.62/1.48  epr:                                    2
% 7.62/1.48  horn:                                   15
% 7.62/1.48  ground:                                 3
% 7.62/1.48  unary:                                  3
% 7.62/1.48  binary:                                 5
% 7.62/1.48  lits:                                   63
% 7.62/1.48  lits_eq:                                8
% 7.62/1.48  fd_pure:                                0
% 7.62/1.48  fd_pseudo:                              0
% 7.62/1.48  fd_cond:                                0
% 7.62/1.48  fd_pseudo_cond:                         7
% 7.62/1.48  ac_symbols:                             0
% 7.62/1.48  
% 7.62/1.48  ------ Propositional Solver
% 7.62/1.48  
% 7.62/1.48  prop_solver_calls:                      30
% 7.62/1.48  prop_fast_solver_calls:                 1296
% 7.62/1.48  smt_solver_calls:                       0
% 7.62/1.48  smt_fast_solver_calls:                  0
% 7.62/1.48  prop_num_of_clauses:                    9611
% 7.62/1.48  prop_preprocess_simplified:             14672
% 7.62/1.48  prop_fo_subsumed:                       1
% 7.62/1.48  prop_solver_time:                       0.
% 7.62/1.48  smt_solver_time:                        0.
% 7.62/1.48  smt_fast_solver_time:                   0.
% 7.62/1.48  prop_fast_solver_time:                  0.
% 7.62/1.48  prop_unsat_core_time:                   0.001
% 7.62/1.48  
% 7.62/1.48  ------ QBF
% 7.62/1.48  
% 7.62/1.48  qbf_q_res:                              0
% 7.62/1.48  qbf_num_tautologies:                    0
% 7.62/1.48  qbf_prep_cycles:                        0
% 7.62/1.48  
% 7.62/1.48  ------ BMC1
% 7.62/1.48  
% 7.62/1.48  bmc1_current_bound:                     -1
% 7.62/1.48  bmc1_last_solved_bound:                 -1
% 7.62/1.48  bmc1_unsat_core_size:                   -1
% 7.62/1.48  bmc1_unsat_core_parents_size:           -1
% 7.62/1.48  bmc1_merge_next_fun:                    0
% 7.62/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.62/1.48  
% 7.62/1.48  ------ Instantiation
% 7.62/1.48  
% 7.62/1.48  inst_num_of_clauses:                    1965
% 7.62/1.48  inst_num_in_passive:                    1075
% 7.62/1.48  inst_num_in_active:                     880
% 7.62/1.48  inst_num_in_unprocessed:                9
% 7.62/1.48  inst_num_of_loops:                      1119
% 7.62/1.48  inst_num_of_learning_restarts:          0
% 7.62/1.48  inst_num_moves_active_passive:          235
% 7.62/1.48  inst_lit_activity:                      0
% 7.62/1.48  inst_lit_activity_moves:                0
% 7.62/1.48  inst_num_tautologies:                   0
% 7.62/1.48  inst_num_prop_implied:                  0
% 7.62/1.48  inst_num_existing_simplified:           0
% 7.62/1.48  inst_num_eq_res_simplified:             0
% 7.62/1.48  inst_num_child_elim:                    0
% 7.62/1.48  inst_num_of_dismatching_blockings:      1325
% 7.62/1.48  inst_num_of_non_proper_insts:           2541
% 7.62/1.48  inst_num_of_duplicates:                 0
% 7.62/1.48  inst_inst_num_from_inst_to_res:         0
% 7.62/1.48  inst_dismatching_checking_time:         0.
% 7.62/1.48  
% 7.62/1.48  ------ Resolution
% 7.62/1.48  
% 7.62/1.48  res_num_of_clauses:                     0
% 7.62/1.48  res_num_in_passive:                     0
% 7.62/1.48  res_num_in_active:                      0
% 7.62/1.48  res_num_of_loops:                       98
% 7.62/1.48  res_forward_subset_subsumed:            316
% 7.62/1.48  res_backward_subset_subsumed:           0
% 7.62/1.48  res_forward_subsumed:                   0
% 7.62/1.48  res_backward_subsumed:                  0
% 7.62/1.48  res_forward_subsumption_resolution:     0
% 7.62/1.48  res_backward_subsumption_resolution:    0
% 7.62/1.48  res_clause_to_clause_subsumption:       4910
% 7.62/1.48  res_orphan_elimination:                 0
% 7.62/1.48  res_tautology_del:                      270
% 7.62/1.48  res_num_eq_res_simplified:              0
% 7.62/1.48  res_num_sel_changes:                    0
% 7.62/1.48  res_moves_from_active_to_pass:          0
% 7.62/1.48  
% 7.62/1.48  ------ Superposition
% 7.62/1.48  
% 7.62/1.48  sup_time_total:                         0.
% 7.62/1.48  sup_time_generating:                    0.
% 7.62/1.48  sup_time_sim_full:                      0.
% 7.62/1.48  sup_time_sim_immed:                     0.
% 7.62/1.48  
% 7.62/1.48  sup_num_of_clauses:                     1270
% 7.62/1.48  sup_num_in_active:                      222
% 7.62/1.48  sup_num_in_passive:                     1048
% 7.62/1.48  sup_num_of_loops:                       222
% 7.62/1.48  sup_fw_superposition:                   811
% 7.62/1.48  sup_bw_superposition:                   539
% 7.62/1.48  sup_immediate_simplified:               20
% 7.62/1.48  sup_given_eliminated:                   0
% 7.62/1.48  comparisons_done:                       0
% 7.62/1.48  comparisons_avoided:                    0
% 7.62/1.48  
% 7.62/1.48  ------ Simplifications
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  sim_fw_subset_subsumed:                 4
% 7.62/1.48  sim_bw_subset_subsumed:                 0
% 7.62/1.48  sim_fw_subsumed:                        13
% 7.62/1.48  sim_bw_subsumed:                        1
% 7.62/1.48  sim_fw_subsumption_res:                 5
% 7.62/1.48  sim_bw_subsumption_res:                 0
% 7.62/1.48  sim_tautology_del:                      8
% 7.62/1.48  sim_eq_tautology_del:                   16
% 7.62/1.48  sim_eq_res_simp:                        6
% 7.62/1.48  sim_fw_demodulated:                     0
% 7.62/1.48  sim_bw_demodulated:                     0
% 7.62/1.48  sim_light_normalised:                   0
% 7.62/1.48  sim_joinable_taut:                      0
% 7.62/1.48  sim_joinable_simp:                      0
% 7.62/1.48  sim_ac_normalised:                      0
% 7.62/1.48  sim_smt_subsumption:                    0
% 7.62/1.48  
%------------------------------------------------------------------------------
