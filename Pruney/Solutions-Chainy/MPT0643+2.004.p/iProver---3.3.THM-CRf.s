%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:16 EST 2020

% Result     : Theorem 19.29s
% Output     : CNFRefutation 19.29s
% Verified   : 
% Statistics : Number of formulae       :  190 (1094 expanded)
%              Number of clauses        :  114 ( 261 expanded)
%              Number of leaves         :   17 ( 286 expanded)
%              Depth                    :   29
%              Number of atoms          :  877 (9011 expanded)
%              Number of equality atoms :  378 (3644 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f94,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f72])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k6_relat_1(X0) != sK12
        & k5_relat_1(sK12,X1) = X1
        & v2_funct_1(X1)
        & r1_tarski(k2_relat_1(sK12),X0)
        & k1_relat_1(sK12) = X0
        & k1_relat_1(X1) = X0
        & v1_funct_1(sK12)
        & v1_relat_1(sK12) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k6_relat_1(X0) != X2
            & k5_relat_1(X2,X1) = X1
            & v2_funct_1(X1)
            & r1_tarski(k2_relat_1(X2),X0)
            & k1_relat_1(X2) = X0
            & k1_relat_1(X1) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k6_relat_1(sK10) != X2
          & k5_relat_1(X2,sK11) = sK11
          & v2_funct_1(sK11)
          & r1_tarski(k2_relat_1(X2),sK10)
          & k1_relat_1(X2) = sK10
          & k1_relat_1(sK11) = sK10
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK11)
      & v1_relat_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k6_relat_1(sK10) != sK12
    & k5_relat_1(sK12,sK11) = sK11
    & v2_funct_1(sK11)
    & r1_tarski(k2_relat_1(sK12),sK10)
    & k1_relat_1(sK12) = sK10
    & k1_relat_1(sK11) = sK10
    & v1_funct_1(sK12)
    & v1_relat_1(sK12)
    & v1_funct_1(sK11)
    & v1_relat_1(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f21,f46,f45])).

fof(f74,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    k1_relat_1(sK11) = sK10 ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( k1_funct_1(X1,sK9(X0,X1)) != sK9(X0,X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( k1_funct_1(X1,sK9(X0,X1)) != sK9(X0,X1)
            & r2_hidden(sK9(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f40,f41])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK9(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | r2_hidden(sK9(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f76,plain,(
    v1_funct_1(sK12) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    v1_relat_1(sK12) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    k1_relat_1(sK12) = sK10 ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    k6_relat_1(sK10) != sK12 ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    k5_relat_1(sK12,sK11) = sK11 ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK1(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK0(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f26,f25,f24])).

fof(f49,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | k1_funct_1(X1,sK9(X0,X1)) != sK9(X0,X1)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k1_funct_1(X1,sK9(k1_relat_1(X1),X1)) != sK9(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f51,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f3,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) = X2
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1)
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f57,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f87,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f79,plain,(
    r1_tarski(k2_relat_1(sK12),sK10) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK7(X0) != sK8(X0)
        & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0))
        & r2_hidden(sK8(X0),k1_relat_1(X0))
        & r2_hidden(sK7(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK7(X0) != sK8(X0)
            & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0))
            & r2_hidden(sK8(X0),k1_relat_1(X0))
            & r2_hidden(sK7(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f35,f36])).

fof(f61,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    v2_funct_1(sK11) ),
    inference(cnf_transformation,[],[f47])).

fof(f50,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_712,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_713,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK11))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK11,X0)),sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_34,negated_conjecture,
    ( v1_relat_1(sK11) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_717,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK11,X0)),sK11)
    | ~ r2_hidden(X0,k1_relat_1(sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_713,c_34])).

cnf(c_718,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK11))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK11,X0)),sK11) ),
    inference(renaming,[status(thm)],[c_717])).

cnf(c_2007,plain,
    ( r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK11,X0)),sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_30,negated_conjecture,
    ( k1_relat_1(sK11) = sK10 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2039,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK11,X0)),sK11) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2007,c_30])).

cnf(c_19,plain,
    ( r2_hidden(sK9(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK12) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_828,plain,
    ( r2_hidden(sK9(k1_relat_1(X0),X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_829,plain,
    ( r2_hidden(sK9(k1_relat_1(sK12),sK12),k1_relat_1(sK12))
    | ~ v1_relat_1(sK12)
    | k6_relat_1(k1_relat_1(sK12)) = sK12 ),
    inference(unflattening,[status(thm)],[c_828])).

cnf(c_32,negated_conjecture,
    ( v1_relat_1(sK12) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_831,plain,
    ( r2_hidden(sK9(k1_relat_1(sK12),sK12),k1_relat_1(sK12))
    | k6_relat_1(k1_relat_1(sK12)) = sK12 ),
    inference(global_propositional_subsumption,[status(thm)],[c_829,c_32])).

cnf(c_2002,plain,
    ( k6_relat_1(k1_relat_1(sK12)) = sK12
    | r2_hidden(sK9(k1_relat_1(sK12),sK12),k1_relat_1(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_29,negated_conjecture,
    ( k1_relat_1(sK12) = sK10 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2032,plain,
    ( k6_relat_1(sK10) = sK12
    | r2_hidden(sK9(sK10,sK12),sK10) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2002,c_29])).

cnf(c_25,negated_conjecture,
    ( k6_relat_1(sK10) != sK12 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2590,plain,
    ( r2_hidden(sK9(sK10,sK12),sK10) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2032,c_25])).

cnf(c_26,negated_conjecture,
    ( k5_relat_1(sK12,sK11) = sK11 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_6,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2023,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_23,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_517,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK12 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_518,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | ~ v1_relat_1(sK12)
    | k1_funct_1(sK12,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_522,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
    | k1_funct_1(sK12,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_518,c_32])).

cnf(c_2017,plain,
    ( k1_funct_1(sK12,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_3711,plain,
    ( sK3(sK12,X0,X1,X2) = k1_funct_1(sK12,X1)
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK12,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(sK12,X0)) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_2023,c_2017])).

cnf(c_37,plain,
    ( v1_relat_1(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_47951,plain,
    ( v1_relat_1(k5_relat_1(sK12,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK12,X0)) != iProver_top
    | sK3(sK12,X0,X1,X2) = k1_funct_1(sK12,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3711,c_37])).

cnf(c_47952,plain,
    ( sK3(sK12,X0,X1,X2) = k1_funct_1(sK12,X1)
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK12,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(sK12,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_47951])).

cnf(c_47981,plain,
    ( sK3(sK12,sK11,X0,X1) = k1_funct_1(sK12,X0)
    | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
    | v1_relat_1(k5_relat_1(sK12,sK11)) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_47952])).

cnf(c_47982,plain,
    ( sK3(sK12,sK11,X0,X1) = k1_funct_1(sK12,X0)
    | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_47981,c_26])).

cnf(c_35,plain,
    ( v1_relat_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_48050,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
    | sK3(sK12,sK11,X0,X1) = k1_funct_1(sK12,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_47982,c_35])).

cnf(c_48051,plain,
    ( sK3(sK12,sK11,X0,X1) = k1_funct_1(sK12,X0)
    | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
    inference(renaming,[status(thm)],[c_48050])).

cnf(c_48064,plain,
    ( sK3(sK12,sK11,X0,k1_funct_1(sK11,X0)) = k1_funct_1(sK12,X0)
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_2039,c_48051])).

cnf(c_48325,plain,
    ( sK3(sK12,sK11,sK9(sK10,sK12),k1_funct_1(sK11,sK9(sK10,sK12))) = k1_funct_1(sK12,sK9(sK10,sK12)) ),
    inference(superposition,[status(thm)],[c_2590,c_48064])).

cnf(c_48609,plain,
    ( r2_hidden(k4_tarski(sK9(sK10,sK12),k1_funct_1(sK11,sK9(sK10,sK12))),k5_relat_1(sK12,sK11)) != iProver_top
    | r2_hidden(k4_tarski(sK9(sK10,sK12),k1_funct_1(sK12,sK9(sK10,sK12))),sK12) = iProver_top
    | v1_relat_1(k5_relat_1(sK12,sK11)) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_48325,c_2023])).

cnf(c_48613,plain,
    ( r2_hidden(k4_tarski(sK9(sK10,sK12),k1_funct_1(sK11,sK9(sK10,sK12))),sK11) != iProver_top
    | r2_hidden(k4_tarski(sK9(sK10,sK12),k1_funct_1(sK12,sK9(sK10,sK12))),sK12) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_48609,c_26])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK9(k1_relat_1(X0),X0)) != sK9(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_842,plain,
    ( ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK9(k1_relat_1(X0),X0)) != sK9(k1_relat_1(X0),X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_31])).

cnf(c_843,plain,
    ( ~ v1_relat_1(sK12)
    | k1_funct_1(sK12,sK9(k1_relat_1(sK12),sK12)) != sK9(k1_relat_1(sK12),sK12)
    | k6_relat_1(k1_relat_1(sK12)) = sK12 ),
    inference(unflattening,[status(thm)],[c_842])).

cnf(c_845,plain,
    ( k1_funct_1(sK12,sK9(k1_relat_1(sK12),sK12)) != sK9(k1_relat_1(sK12),sK12)
    | k6_relat_1(k1_relat_1(sK12)) = sK12 ),
    inference(global_propositional_subsumption,[status(thm)],[c_843,c_32])).

cnf(c_2042,plain,
    ( k1_funct_1(sK12,sK9(sK10,sK12)) != sK9(sK10,sK12)
    | k6_relat_1(sK10) = sK12 ),
    inference(light_normalisation,[status(thm)],[c_845,c_29])).

cnf(c_571,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_572,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK12))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK12,X0)),sK12)
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_576,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK12,X0)),sK12)
    | ~ r2_hidden(X0,k1_relat_1(sK12)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_32])).

cnf(c_577,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK12))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK12,X0)),sK12) ),
    inference(renaming,[status(thm)],[c_576])).

cnf(c_2014,plain,
    ( r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK12,X0)),sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_2040,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK12,X0)),sK12) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2014,c_29])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2025,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X4) != iProver_top
    | v1_relat_1(k5_relat_1(X4,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3616,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK11,X0)),k5_relat_1(X2,sK11)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,sK11)) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_2039,c_2025])).

cnf(c_17271,plain,
    ( v1_relat_1(k5_relat_1(X2,sK11)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK11,X0)),k5_relat_1(X2,sK11)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3616,c_35])).

cnf(c_17272,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK11,X0)),k5_relat_1(X2,sK11)) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k5_relat_1(X2,sK11)) != iProver_top ),
    inference(renaming,[status(thm)],[c_17271])).

cnf(c_17284,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK12) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK11,X0)),sK11) = iProver_top
    | v1_relat_1(k5_relat_1(sK12,sK11)) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_17272])).

cnf(c_17292,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK12) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK11,X0)),sK11) = iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17284,c_26])).

cnf(c_17330,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK12) != iProver_top
    | r2_hidden(k4_tarski(X1,k1_funct_1(sK11,X0)),sK11) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17292,c_35,c_37])).

cnf(c_535,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK11 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_536,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ v1_relat_1(sK11)
    | k1_funct_1(sK11,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_540,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | k1_funct_1(sK11,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_34])).

cnf(c_2016,plain,
    ( k1_funct_1(sK11,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_17352,plain,
    ( k1_funct_1(sK11,X0) = k1_funct_1(sK11,X1)
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_17330,c_2016])).

cnf(c_17628,plain,
    ( k1_funct_1(sK11,k1_funct_1(sK12,X0)) = k1_funct_1(sK11,X0)
    | r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k1_funct_1(sK12,X0),sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_2040,c_17352])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_652,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK12 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_31])).

cnf(c_653,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK12))
    | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12))
    | ~ v1_relat_1(sK12) ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_657,plain,
    ( r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12))
    | ~ r2_hidden(X0,k1_relat_1(sK12)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_32])).

cnf(c_658,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK12))
    | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) ),
    inference(renaming,[status(thm)],[c_657])).

cnf(c_2010,plain,
    ( r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
    | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_2037,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2010,c_29])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK12),sK10) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_338,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k2_relat_1(sK12) != X1
    | sK10 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_28])).

cnf(c_339,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK12))
    | r2_hidden(X0,sK10) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_2019,plain,
    ( r2_hidden(X0,k2_relat_1(sK12)) != iProver_top
    | r2_hidden(X0,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_3425,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k1_funct_1(sK12,X0),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_2037,c_2019])).

cnf(c_17679,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | k1_funct_1(sK11,k1_funct_1(sK12,X0)) = k1_funct_1(sK11,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17628,c_3425])).

cnf(c_17680,plain,
    ( k1_funct_1(sK11,k1_funct_1(sK12,X0)) = k1_funct_1(sK11,X0)
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(renaming,[status(thm)],[c_17679])).

cnf(c_17704,plain,
    ( k1_funct_1(sK11,k1_funct_1(sK12,sK9(sK10,sK12))) = k1_funct_1(sK11,sK9(sK10,sK12)) ),
    inference(superposition,[status(thm)],[c_2590,c_17680])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_730,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_731,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK11))
    | ~ r2_hidden(X1,k1_relat_1(sK11))
    | ~ v2_funct_1(sK11)
    | ~ v1_relat_1(sK11)
    | X0 = X1
    | k1_funct_1(sK11,X0) != k1_funct_1(sK11,X1) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK11) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_461,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_462,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK11))
    | ~ r2_hidden(X1,k1_relat_1(sK11))
    | ~ v1_funct_1(sK11)
    | ~ v1_relat_1(sK11)
    | X0 = X1
    | k1_funct_1(sK11,X0) != k1_funct_1(sK11,X1) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_466,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK11))
    | ~ r2_hidden(X1,k1_relat_1(sK11))
    | X0 = X1
    | k1_funct_1(sK11,X0) != k1_funct_1(sK11,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_34,c_33])).

cnf(c_733,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK11))
    | ~ r2_hidden(X1,k1_relat_1(sK11))
    | X0 = X1
    | k1_funct_1(sK11,X0) != k1_funct_1(sK11,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_34,c_33,c_462])).

cnf(c_2018,plain,
    ( X0 = X1
    | k1_funct_1(sK11,X0) != k1_funct_1(sK11,X1)
    | r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_2045,plain,
    ( X0 = X1
    | k1_funct_1(sK11,X0) != k1_funct_1(sK11,X1)
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2018,c_30])).

cnf(c_17775,plain,
    ( k1_funct_1(sK11,sK9(sK10,sK12)) != k1_funct_1(sK11,X0)
    | k1_funct_1(sK12,sK9(sK10,sK12)) = X0
    | r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k1_funct_1(sK12,sK9(sK10,sK12)),sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_17704,c_2045])).

cnf(c_23603,plain,
    ( k1_funct_1(sK12,sK9(sK10,sK12)) = sK9(sK10,sK12)
    | r2_hidden(sK9(sK10,sK12),sK10) != iProver_top
    | r2_hidden(k1_funct_1(sK12,sK9(sK10,sK12)),sK10) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_17775])).

cnf(c_5,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2024,plain,
    ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X3) != iProver_top
    | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_24,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_694,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK11 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_695,plain,
    ( r2_hidden(X0,k1_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | ~ v1_relat_1(sK11) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_699,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
    | r2_hidden(X0,k1_relat_1(sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_34])).

cnf(c_700,plain,
    ( r2_hidden(X0,k1_relat_1(sK11))
    | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
    inference(renaming,[status(thm)],[c_699])).

cnf(c_2008,plain,
    ( r2_hidden(X0,k1_relat_1(sK11)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_2033,plain,
    ( r2_hidden(X0,sK10) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2008,c_30])).

cnf(c_3599,plain,
    ( r2_hidden(sK3(X0,sK11,X1,X2),sK10) = iProver_top
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK11)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK11)) != iProver_top
    | v1_relat_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_2024,c_2033])).

cnf(c_11562,plain,
    ( v1_relat_1(k5_relat_1(X0,sK11)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK11)) != iProver_top
    | r2_hidden(sK3(X0,sK11,X1,X2),sK10) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3599,c_35])).

cnf(c_11563,plain,
    ( r2_hidden(sK3(X0,sK11,X1,X2),sK10) = iProver_top
    | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK11)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k5_relat_1(X0,sK11)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11562])).

cnf(c_11572,plain,
    ( r2_hidden(sK3(sK12,sK11,X0,X1),sK10) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
    | v1_relat_1(k5_relat_1(sK12,sK11)) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_11563])).

cnf(c_11573,plain,
    ( r2_hidden(sK3(sK12,sK11,X0,X1),sK10) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11572,c_26])).

cnf(c_11741,plain,
    ( r2_hidden(sK3(sK12,sK11,X0,X1),sK10) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11573,c_35,c_37])).

cnf(c_48611,plain,
    ( r2_hidden(k1_funct_1(sK12,sK9(sK10,sK12)),sK10) = iProver_top
    | r2_hidden(k4_tarski(sK9(sK10,sK12),k1_funct_1(sK11,sK9(sK10,sK12))),sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_48325,c_11741])).

cnf(c_48626,plain,
    ( r2_hidden(k4_tarski(sK9(sK10,sK12),k1_funct_1(sK11,sK9(sK10,sK12))),sK11) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_48613,c_25,c_2042,c_2032,c_23603,c_48611])).

cnf(c_48630,plain,
    ( r2_hidden(sK9(sK10,sK12),sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_2039,c_48626])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48630,c_2032,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.29/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.29/3.00  
% 19.29/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.29/3.00  
% 19.29/3.00  ------  iProver source info
% 19.29/3.00  
% 19.29/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.29/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.29/3.00  git: non_committed_changes: false
% 19.29/3.00  git: last_make_outside_of_git: false
% 19.29/3.00  
% 19.29/3.00  ------ 
% 19.29/3.00  
% 19.29/3.00  ------ Input Options
% 19.29/3.00  
% 19.29/3.00  --out_options                           all
% 19.29/3.00  --tptp_safe_out                         true
% 19.29/3.00  --problem_path                          ""
% 19.29/3.00  --include_path                          ""
% 19.29/3.00  --clausifier                            res/vclausify_rel
% 19.29/3.00  --clausifier_options                    ""
% 19.29/3.00  --stdin                                 false
% 19.29/3.00  --stats_out                             all
% 19.29/3.00  
% 19.29/3.00  ------ General Options
% 19.29/3.00  
% 19.29/3.00  --fof                                   false
% 19.29/3.00  --time_out_real                         305.
% 19.29/3.00  --time_out_virtual                      -1.
% 19.29/3.00  --symbol_type_check                     false
% 19.29/3.00  --clausify_out                          false
% 19.29/3.00  --sig_cnt_out                           false
% 19.29/3.00  --trig_cnt_out                          false
% 19.29/3.00  --trig_cnt_out_tolerance                1.
% 19.29/3.00  --trig_cnt_out_sk_spl                   false
% 19.29/3.00  --abstr_cl_out                          false
% 19.29/3.00  
% 19.29/3.00  ------ Global Options
% 19.29/3.00  
% 19.29/3.00  --schedule                              default
% 19.29/3.00  --add_important_lit                     false
% 19.29/3.00  --prop_solver_per_cl                    1000
% 19.29/3.00  --min_unsat_core                        false
% 19.29/3.00  --soft_assumptions                      false
% 19.29/3.00  --soft_lemma_size                       3
% 19.29/3.00  --prop_impl_unit_size                   0
% 19.29/3.00  --prop_impl_unit                        []
% 19.29/3.00  --share_sel_clauses                     true
% 19.29/3.00  --reset_solvers                         false
% 19.29/3.00  --bc_imp_inh                            [conj_cone]
% 19.29/3.00  --conj_cone_tolerance                   3.
% 19.29/3.00  --extra_neg_conj                        none
% 19.29/3.00  --large_theory_mode                     true
% 19.29/3.00  --prolific_symb_bound                   200
% 19.29/3.00  --lt_threshold                          2000
% 19.29/3.00  --clause_weak_htbl                      true
% 19.29/3.00  --gc_record_bc_elim                     false
% 19.29/3.00  
% 19.29/3.00  ------ Preprocessing Options
% 19.29/3.00  
% 19.29/3.00  --preprocessing_flag                    true
% 19.29/3.00  --time_out_prep_mult                    0.1
% 19.29/3.00  --splitting_mode                        input
% 19.29/3.00  --splitting_grd                         true
% 19.29/3.00  --splitting_cvd                         false
% 19.29/3.00  --splitting_cvd_svl                     false
% 19.29/3.00  --splitting_nvd                         32
% 19.29/3.00  --sub_typing                            true
% 19.29/3.00  --prep_gs_sim                           true
% 19.29/3.00  --prep_unflatten                        true
% 19.29/3.00  --prep_res_sim                          true
% 19.29/3.00  --prep_upred                            true
% 19.29/3.00  --prep_sem_filter                       exhaustive
% 19.29/3.00  --prep_sem_filter_out                   false
% 19.29/3.00  --pred_elim                             true
% 19.29/3.00  --res_sim_input                         true
% 19.29/3.00  --eq_ax_congr_red                       true
% 19.29/3.00  --pure_diseq_elim                       true
% 19.29/3.00  --brand_transform                       false
% 19.29/3.00  --non_eq_to_eq                          false
% 19.29/3.00  --prep_def_merge                        true
% 19.29/3.00  --prep_def_merge_prop_impl              false
% 19.29/3.00  --prep_def_merge_mbd                    true
% 19.29/3.00  --prep_def_merge_tr_red                 false
% 19.29/3.00  --prep_def_merge_tr_cl                  false
% 19.29/3.00  --smt_preprocessing                     true
% 19.29/3.00  --smt_ac_axioms                         fast
% 19.29/3.00  --preprocessed_out                      false
% 19.29/3.00  --preprocessed_stats                    false
% 19.29/3.00  
% 19.29/3.00  ------ Abstraction refinement Options
% 19.29/3.00  
% 19.29/3.00  --abstr_ref                             []
% 19.29/3.00  --abstr_ref_prep                        false
% 19.29/3.00  --abstr_ref_until_sat                   false
% 19.29/3.00  --abstr_ref_sig_restrict                funpre
% 19.29/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.29/3.00  --abstr_ref_under                       []
% 19.29/3.00  
% 19.29/3.00  ------ SAT Options
% 19.29/3.00  
% 19.29/3.00  --sat_mode                              false
% 19.29/3.00  --sat_fm_restart_options                ""
% 19.29/3.00  --sat_gr_def                            false
% 19.29/3.00  --sat_epr_types                         true
% 19.29/3.00  --sat_non_cyclic_types                  false
% 19.29/3.00  --sat_finite_models                     false
% 19.29/3.00  --sat_fm_lemmas                         false
% 19.29/3.00  --sat_fm_prep                           false
% 19.29/3.00  --sat_fm_uc_incr                        true
% 19.29/3.00  --sat_out_model                         small
% 19.29/3.00  --sat_out_clauses                       false
% 19.29/3.00  
% 19.29/3.00  ------ QBF Options
% 19.29/3.00  
% 19.29/3.00  --qbf_mode                              false
% 19.29/3.00  --qbf_elim_univ                         false
% 19.29/3.00  --qbf_dom_inst                          none
% 19.29/3.00  --qbf_dom_pre_inst                      false
% 19.29/3.00  --qbf_sk_in                             false
% 19.29/3.00  --qbf_pred_elim                         true
% 19.29/3.00  --qbf_split                             512
% 19.29/3.00  
% 19.29/3.00  ------ BMC1 Options
% 19.29/3.00  
% 19.29/3.00  --bmc1_incremental                      false
% 19.29/3.00  --bmc1_axioms                           reachable_all
% 19.29/3.00  --bmc1_min_bound                        0
% 19.29/3.00  --bmc1_max_bound                        -1
% 19.29/3.00  --bmc1_max_bound_default                -1
% 19.29/3.00  --bmc1_symbol_reachability              true
% 19.29/3.00  --bmc1_property_lemmas                  false
% 19.29/3.00  --bmc1_k_induction                      false
% 19.29/3.00  --bmc1_non_equiv_states                 false
% 19.29/3.00  --bmc1_deadlock                         false
% 19.29/3.00  --bmc1_ucm                              false
% 19.29/3.00  --bmc1_add_unsat_core                   none
% 19.29/3.00  --bmc1_unsat_core_children              false
% 19.29/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.29/3.00  --bmc1_out_stat                         full
% 19.29/3.00  --bmc1_ground_init                      false
% 19.29/3.00  --bmc1_pre_inst_next_state              false
% 19.29/3.00  --bmc1_pre_inst_state                   false
% 19.29/3.00  --bmc1_pre_inst_reach_state             false
% 19.29/3.00  --bmc1_out_unsat_core                   false
% 19.29/3.00  --bmc1_aig_witness_out                  false
% 19.29/3.00  --bmc1_verbose                          false
% 19.29/3.00  --bmc1_dump_clauses_tptp                false
% 19.29/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.29/3.00  --bmc1_dump_file                        -
% 19.29/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.29/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.29/3.00  --bmc1_ucm_extend_mode                  1
% 19.29/3.00  --bmc1_ucm_init_mode                    2
% 19.29/3.00  --bmc1_ucm_cone_mode                    none
% 19.29/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.29/3.00  --bmc1_ucm_relax_model                  4
% 19.29/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.29/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.29/3.00  --bmc1_ucm_layered_model                none
% 19.29/3.00  --bmc1_ucm_max_lemma_size               10
% 19.29/3.00  
% 19.29/3.00  ------ AIG Options
% 19.29/3.00  
% 19.29/3.00  --aig_mode                              false
% 19.29/3.00  
% 19.29/3.00  ------ Instantiation Options
% 19.29/3.00  
% 19.29/3.00  --instantiation_flag                    true
% 19.29/3.00  --inst_sos_flag                         true
% 19.29/3.00  --inst_sos_phase                        true
% 19.29/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.29/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.29/3.00  --inst_lit_sel_side                     num_symb
% 19.29/3.00  --inst_solver_per_active                1400
% 19.29/3.00  --inst_solver_calls_frac                1.
% 19.29/3.00  --inst_passive_queue_type               priority_queues
% 19.29/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.29/3.00  --inst_passive_queues_freq              [25;2]
% 19.29/3.00  --inst_dismatching                      true
% 19.29/3.00  --inst_eager_unprocessed_to_passive     true
% 19.29/3.00  --inst_prop_sim_given                   true
% 19.29/3.00  --inst_prop_sim_new                     false
% 19.29/3.00  --inst_subs_new                         false
% 19.29/3.00  --inst_eq_res_simp                      false
% 19.29/3.00  --inst_subs_given                       false
% 19.29/3.00  --inst_orphan_elimination               true
% 19.29/3.00  --inst_learning_loop_flag               true
% 19.29/3.00  --inst_learning_start                   3000
% 19.29/3.00  --inst_learning_factor                  2
% 19.29/3.00  --inst_start_prop_sim_after_learn       3
% 19.29/3.00  --inst_sel_renew                        solver
% 19.29/3.00  --inst_lit_activity_flag                true
% 19.29/3.00  --inst_restr_to_given                   false
% 19.29/3.00  --inst_activity_threshold               500
% 19.29/3.00  --inst_out_proof                        true
% 19.29/3.00  
% 19.29/3.00  ------ Resolution Options
% 19.29/3.00  
% 19.29/3.00  --resolution_flag                       true
% 19.29/3.00  --res_lit_sel                           adaptive
% 19.29/3.00  --res_lit_sel_side                      none
% 19.29/3.00  --res_ordering                          kbo
% 19.29/3.00  --res_to_prop_solver                    active
% 19.29/3.00  --res_prop_simpl_new                    false
% 19.29/3.00  --res_prop_simpl_given                  true
% 19.29/3.00  --res_passive_queue_type                priority_queues
% 19.29/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.29/3.00  --res_passive_queues_freq               [15;5]
% 19.29/3.00  --res_forward_subs                      full
% 19.29/3.00  --res_backward_subs                     full
% 19.29/3.00  --res_forward_subs_resolution           true
% 19.29/3.00  --res_backward_subs_resolution          true
% 19.29/3.00  --res_orphan_elimination                true
% 19.29/3.00  --res_time_limit                        2.
% 19.29/3.00  --res_out_proof                         true
% 19.29/3.00  
% 19.29/3.00  ------ Superposition Options
% 19.29/3.00  
% 19.29/3.00  --superposition_flag                    true
% 19.29/3.00  --sup_passive_queue_type                priority_queues
% 19.29/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.29/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.29/3.00  --demod_completeness_check              fast
% 19.29/3.00  --demod_use_ground                      true
% 19.29/3.00  --sup_to_prop_solver                    passive
% 19.29/3.00  --sup_prop_simpl_new                    true
% 19.29/3.00  --sup_prop_simpl_given                  true
% 19.29/3.00  --sup_fun_splitting                     true
% 19.29/3.00  --sup_smt_interval                      50000
% 19.29/3.00  
% 19.29/3.00  ------ Superposition Simplification Setup
% 19.29/3.00  
% 19.29/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.29/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.29/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.29/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.29/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.29/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.29/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.29/3.00  --sup_immed_triv                        [TrivRules]
% 19.29/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.29/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.29/3.00  --sup_immed_bw_main                     []
% 19.29/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.29/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.29/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.29/3.00  --sup_input_bw                          []
% 19.29/3.00  
% 19.29/3.00  ------ Combination Options
% 19.29/3.00  
% 19.29/3.00  --comb_res_mult                         3
% 19.29/3.00  --comb_sup_mult                         2
% 19.29/3.00  --comb_inst_mult                        10
% 19.29/3.00  
% 19.29/3.00  ------ Debug Options
% 19.29/3.00  
% 19.29/3.00  --dbg_backtrace                         false
% 19.29/3.00  --dbg_dump_prop_clauses                 false
% 19.29/3.00  --dbg_dump_prop_clauses_file            -
% 19.29/3.00  --dbg_out_stat                          false
% 19.29/3.00  ------ Parsing...
% 19.29/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.29/3.00  
% 19.29/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 19.29/3.00  
% 19.29/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.29/3.00  
% 19.29/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.29/3.00  ------ Proving...
% 19.29/3.00  ------ Problem Properties 
% 19.29/3.00  
% 19.29/3.00  
% 19.29/3.00  clauses                                 46
% 19.29/3.00  conjectures                             7
% 19.29/3.00  EPR                                     3
% 19.29/3.00  Horn                                    35
% 19.29/3.00  unary                                   7
% 19.29/3.00  binary                                  21
% 19.29/3.00  lits                                    127
% 19.29/3.00  lits eq                                 41
% 19.29/3.00  fd_pure                                 0
% 19.29/3.00  fd_pseudo                               0
% 19.29/3.00  fd_cond                                 6
% 19.29/3.00  fd_pseudo_cond                          7
% 19.29/3.00  AC symbols                              0
% 19.29/3.00  
% 19.29/3.00  ------ Schedule dynamic 5 is on 
% 19.29/3.00  
% 19.29/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.29/3.00  
% 19.29/3.00  
% 19.29/3.00  ------ 
% 19.29/3.00  Current options:
% 19.29/3.00  ------ 
% 19.29/3.00  
% 19.29/3.00  ------ Input Options
% 19.29/3.00  
% 19.29/3.00  --out_options                           all
% 19.29/3.00  --tptp_safe_out                         true
% 19.29/3.00  --problem_path                          ""
% 19.29/3.00  --include_path                          ""
% 19.29/3.00  --clausifier                            res/vclausify_rel
% 19.29/3.00  --clausifier_options                    ""
% 19.29/3.00  --stdin                                 false
% 19.29/3.00  --stats_out                             all
% 19.29/3.00  
% 19.29/3.00  ------ General Options
% 19.29/3.00  
% 19.29/3.00  --fof                                   false
% 19.29/3.00  --time_out_real                         305.
% 19.29/3.00  --time_out_virtual                      -1.
% 19.29/3.00  --symbol_type_check                     false
% 19.29/3.00  --clausify_out                          false
% 19.29/3.00  --sig_cnt_out                           false
% 19.29/3.00  --trig_cnt_out                          false
% 19.29/3.00  --trig_cnt_out_tolerance                1.
% 19.29/3.00  --trig_cnt_out_sk_spl                   false
% 19.29/3.00  --abstr_cl_out                          false
% 19.29/3.00  
% 19.29/3.00  ------ Global Options
% 19.29/3.00  
% 19.29/3.00  --schedule                              default
% 19.29/3.00  --add_important_lit                     false
% 19.29/3.00  --prop_solver_per_cl                    1000
% 19.29/3.00  --min_unsat_core                        false
% 19.29/3.00  --soft_assumptions                      false
% 19.29/3.00  --soft_lemma_size                       3
% 19.29/3.00  --prop_impl_unit_size                   0
% 19.29/3.00  --prop_impl_unit                        []
% 19.29/3.00  --share_sel_clauses                     true
% 19.29/3.00  --reset_solvers                         false
% 19.29/3.00  --bc_imp_inh                            [conj_cone]
% 19.29/3.00  --conj_cone_tolerance                   3.
% 19.29/3.00  --extra_neg_conj                        none
% 19.29/3.00  --large_theory_mode                     true
% 19.29/3.00  --prolific_symb_bound                   200
% 19.29/3.00  --lt_threshold                          2000
% 19.29/3.00  --clause_weak_htbl                      true
% 19.29/3.00  --gc_record_bc_elim                     false
% 19.29/3.00  
% 19.29/3.00  ------ Preprocessing Options
% 19.29/3.00  
% 19.29/3.00  --preprocessing_flag                    true
% 19.29/3.00  --time_out_prep_mult                    0.1
% 19.29/3.00  --splitting_mode                        input
% 19.29/3.00  --splitting_grd                         true
% 19.29/3.00  --splitting_cvd                         false
% 19.29/3.00  --splitting_cvd_svl                     false
% 19.29/3.00  --splitting_nvd                         32
% 19.29/3.00  --sub_typing                            true
% 19.29/3.00  --prep_gs_sim                           true
% 19.29/3.00  --prep_unflatten                        true
% 19.29/3.00  --prep_res_sim                          true
% 19.29/3.00  --prep_upred                            true
% 19.29/3.00  --prep_sem_filter                       exhaustive
% 19.29/3.00  --prep_sem_filter_out                   false
% 19.29/3.00  --pred_elim                             true
% 19.29/3.00  --res_sim_input                         true
% 19.29/3.00  --eq_ax_congr_red                       true
% 19.29/3.00  --pure_diseq_elim                       true
% 19.29/3.00  --brand_transform                       false
% 19.29/3.00  --non_eq_to_eq                          false
% 19.29/3.00  --prep_def_merge                        true
% 19.29/3.00  --prep_def_merge_prop_impl              false
% 19.29/3.00  --prep_def_merge_mbd                    true
% 19.29/3.00  --prep_def_merge_tr_red                 false
% 19.29/3.00  --prep_def_merge_tr_cl                  false
% 19.29/3.00  --smt_preprocessing                     true
% 19.29/3.00  --smt_ac_axioms                         fast
% 19.29/3.00  --preprocessed_out                      false
% 19.29/3.00  --preprocessed_stats                    false
% 19.29/3.00  
% 19.29/3.00  ------ Abstraction refinement Options
% 19.29/3.00  
% 19.29/3.00  --abstr_ref                             []
% 19.29/3.00  --abstr_ref_prep                        false
% 19.29/3.00  --abstr_ref_until_sat                   false
% 19.29/3.00  --abstr_ref_sig_restrict                funpre
% 19.29/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.29/3.00  --abstr_ref_under                       []
% 19.29/3.00  
% 19.29/3.00  ------ SAT Options
% 19.29/3.00  
% 19.29/3.00  --sat_mode                              false
% 19.29/3.00  --sat_fm_restart_options                ""
% 19.29/3.00  --sat_gr_def                            false
% 19.29/3.00  --sat_epr_types                         true
% 19.29/3.00  --sat_non_cyclic_types                  false
% 19.29/3.00  --sat_finite_models                     false
% 19.29/3.00  --sat_fm_lemmas                         false
% 19.29/3.00  --sat_fm_prep                           false
% 19.29/3.00  --sat_fm_uc_incr                        true
% 19.29/3.00  --sat_out_model                         small
% 19.29/3.00  --sat_out_clauses                       false
% 19.29/3.00  
% 19.29/3.00  ------ QBF Options
% 19.29/3.00  
% 19.29/3.00  --qbf_mode                              false
% 19.29/3.00  --qbf_elim_univ                         false
% 19.29/3.00  --qbf_dom_inst                          none
% 19.29/3.00  --qbf_dom_pre_inst                      false
% 19.29/3.00  --qbf_sk_in                             false
% 19.29/3.00  --qbf_pred_elim                         true
% 19.29/3.00  --qbf_split                             512
% 19.29/3.00  
% 19.29/3.00  ------ BMC1 Options
% 19.29/3.00  
% 19.29/3.00  --bmc1_incremental                      false
% 19.29/3.00  --bmc1_axioms                           reachable_all
% 19.29/3.00  --bmc1_min_bound                        0
% 19.29/3.00  --bmc1_max_bound                        -1
% 19.29/3.00  --bmc1_max_bound_default                -1
% 19.29/3.00  --bmc1_symbol_reachability              true
% 19.29/3.00  --bmc1_property_lemmas                  false
% 19.29/3.00  --bmc1_k_induction                      false
% 19.29/3.00  --bmc1_non_equiv_states                 false
% 19.29/3.00  --bmc1_deadlock                         false
% 19.29/3.00  --bmc1_ucm                              false
% 19.29/3.00  --bmc1_add_unsat_core                   none
% 19.29/3.00  --bmc1_unsat_core_children              false
% 19.29/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.29/3.00  --bmc1_out_stat                         full
% 19.29/3.00  --bmc1_ground_init                      false
% 19.29/3.00  --bmc1_pre_inst_next_state              false
% 19.29/3.00  --bmc1_pre_inst_state                   false
% 19.29/3.00  --bmc1_pre_inst_reach_state             false
% 19.29/3.00  --bmc1_out_unsat_core                   false
% 19.29/3.00  --bmc1_aig_witness_out                  false
% 19.29/3.00  --bmc1_verbose                          false
% 19.29/3.00  --bmc1_dump_clauses_tptp                false
% 19.29/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.29/3.00  --bmc1_dump_file                        -
% 19.29/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.29/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.29/3.00  --bmc1_ucm_extend_mode                  1
% 19.29/3.00  --bmc1_ucm_init_mode                    2
% 19.29/3.00  --bmc1_ucm_cone_mode                    none
% 19.29/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.29/3.00  --bmc1_ucm_relax_model                  4
% 19.29/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.29/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.29/3.00  --bmc1_ucm_layered_model                none
% 19.29/3.00  --bmc1_ucm_max_lemma_size               10
% 19.29/3.00  
% 19.29/3.00  ------ AIG Options
% 19.29/3.00  
% 19.29/3.00  --aig_mode                              false
% 19.29/3.00  
% 19.29/3.00  ------ Instantiation Options
% 19.29/3.00  
% 19.29/3.00  --instantiation_flag                    true
% 19.29/3.00  --inst_sos_flag                         true
% 19.29/3.00  --inst_sos_phase                        true
% 19.29/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.29/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.29/3.00  --inst_lit_sel_side                     none
% 19.29/3.00  --inst_solver_per_active                1400
% 19.29/3.00  --inst_solver_calls_frac                1.
% 19.29/3.00  --inst_passive_queue_type               priority_queues
% 19.29/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.29/3.00  --inst_passive_queues_freq              [25;2]
% 19.29/3.00  --inst_dismatching                      true
% 19.29/3.00  --inst_eager_unprocessed_to_passive     true
% 19.29/3.00  --inst_prop_sim_given                   true
% 19.29/3.00  --inst_prop_sim_new                     false
% 19.29/3.00  --inst_subs_new                         false
% 19.29/3.00  --inst_eq_res_simp                      false
% 19.29/3.00  --inst_subs_given                       false
% 19.29/3.00  --inst_orphan_elimination               true
% 19.29/3.00  --inst_learning_loop_flag               true
% 19.29/3.00  --inst_learning_start                   3000
% 19.29/3.00  --inst_learning_factor                  2
% 19.29/3.00  --inst_start_prop_sim_after_learn       3
% 19.29/3.00  --inst_sel_renew                        solver
% 19.29/3.00  --inst_lit_activity_flag                true
% 19.29/3.00  --inst_restr_to_given                   false
% 19.29/3.00  --inst_activity_threshold               500
% 19.29/3.00  --inst_out_proof                        true
% 19.29/3.00  
% 19.29/3.00  ------ Resolution Options
% 19.29/3.00  
% 19.29/3.00  --resolution_flag                       false
% 19.29/3.00  --res_lit_sel                           adaptive
% 19.29/3.00  --res_lit_sel_side                      none
% 19.29/3.00  --res_ordering                          kbo
% 19.29/3.00  --res_to_prop_solver                    active
% 19.29/3.00  --res_prop_simpl_new                    false
% 19.29/3.00  --res_prop_simpl_given                  true
% 19.29/3.00  --res_passive_queue_type                priority_queues
% 19.29/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.29/3.00  --res_passive_queues_freq               [15;5]
% 19.29/3.00  --res_forward_subs                      full
% 19.29/3.00  --res_backward_subs                     full
% 19.29/3.00  --res_forward_subs_resolution           true
% 19.29/3.00  --res_backward_subs_resolution          true
% 19.29/3.00  --res_orphan_elimination                true
% 19.29/3.00  --res_time_limit                        2.
% 19.29/3.00  --res_out_proof                         true
% 19.29/3.00  
% 19.29/3.00  ------ Superposition Options
% 19.29/3.00  
% 19.29/3.00  --superposition_flag                    true
% 19.29/3.00  --sup_passive_queue_type                priority_queues
% 19.29/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.29/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.29/3.00  --demod_completeness_check              fast
% 19.29/3.00  --demod_use_ground                      true
% 19.29/3.00  --sup_to_prop_solver                    passive
% 19.29/3.00  --sup_prop_simpl_new                    true
% 19.29/3.00  --sup_prop_simpl_given                  true
% 19.29/3.00  --sup_fun_splitting                     true
% 19.29/3.00  --sup_smt_interval                      50000
% 19.29/3.00  
% 19.29/3.00  ------ Superposition Simplification Setup
% 19.29/3.00  
% 19.29/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.29/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.29/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.29/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.29/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.29/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.29/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.29/3.00  --sup_immed_triv                        [TrivRules]
% 19.29/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.29/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.29/3.00  --sup_immed_bw_main                     []
% 19.29/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.29/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.29/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.29/3.00  --sup_input_bw                          []
% 19.29/3.00  
% 19.29/3.00  ------ Combination Options
% 19.29/3.00  
% 19.29/3.00  --comb_res_mult                         3
% 19.29/3.00  --comb_sup_mult                         2
% 19.29/3.00  --comb_inst_mult                        10
% 19.29/3.00  
% 19.29/3.00  ------ Debug Options
% 19.29/3.00  
% 19.29/3.00  --dbg_backtrace                         false
% 19.29/3.00  --dbg_dump_prop_clauses                 false
% 19.29/3.00  --dbg_dump_prop_clauses_file            -
% 19.29/3.00  --dbg_out_stat                          false
% 19.29/3.00  
% 19.29/3.00  
% 19.29/3.00  
% 19.29/3.00  
% 19.29/3.00  ------ Proving...
% 19.29/3.00  
% 19.29/3.00  
% 19.29/3.00  % SZS status Theorem for theBenchmark.p
% 19.29/3.00  
% 19.29/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.29/3.00  
% 19.29/3.00  fof(f6,axiom,(
% 19.29/3.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 19.29/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.29/3.00  
% 19.29/3.00  fof(f18,plain,(
% 19.29/3.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 19.29/3.00    inference(ennf_transformation,[],[f6])).
% 19.29/3.00  
% 19.29/3.00  fof(f19,plain,(
% 19.29/3.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 19.29/3.00    inference(flattening,[],[f18])).
% 19.29/3.00  
% 19.29/3.00  fof(f43,plain,(
% 19.29/3.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 19.29/3.00    inference(nnf_transformation,[],[f19])).
% 19.29/3.00  
% 19.29/3.00  fof(f44,plain,(
% 19.29/3.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 19.29/3.00    inference(flattening,[],[f43])).
% 19.29/3.00  
% 19.29/3.00  fof(f72,plain,(
% 19.29/3.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.29/3.00    inference(cnf_transformation,[],[f44])).
% 19.29/3.00  
% 19.29/3.00  fof(f94,plain,(
% 19.29/3.00    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.29/3.00    inference(equality_resolution,[],[f72])).
% 19.29/3.00  
% 19.29/3.00  fof(f7,conjecture,(
% 19.29/3.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 19.29/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.29/3.00  
% 19.29/3.00  fof(f8,negated_conjecture,(
% 19.29/3.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 19.29/3.00    inference(negated_conjecture,[],[f7])).
% 19.29/3.00  
% 19.29/3.00  fof(f20,plain,(
% 19.29/3.00    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 19.29/3.00    inference(ennf_transformation,[],[f8])).
% 19.29/3.00  
% 19.29/3.00  fof(f21,plain,(
% 19.29/3.00    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 19.29/3.00    inference(flattening,[],[f20])).
% 19.29/3.00  
% 19.29/3.00  fof(f46,plain,(
% 19.29/3.00    ( ! [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k6_relat_1(X0) != sK12 & k5_relat_1(sK12,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(sK12),X0) & k1_relat_1(sK12) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(sK12) & v1_relat_1(sK12))) )),
% 19.29/3.00    introduced(choice_axiom,[])).
% 19.29/3.00  
% 19.29/3.00  fof(f45,plain,(
% 19.29/3.00    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k6_relat_1(sK10) != X2 & k5_relat_1(X2,sK11) = sK11 & v2_funct_1(sK11) & r1_tarski(k2_relat_1(X2),sK10) & k1_relat_1(X2) = sK10 & k1_relat_1(sK11) = sK10 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK11) & v1_relat_1(sK11))),
% 19.29/3.00    introduced(choice_axiom,[])).
% 19.29/3.00  
% 19.29/3.00  fof(f47,plain,(
% 19.29/3.00    (k6_relat_1(sK10) != sK12 & k5_relat_1(sK12,sK11) = sK11 & v2_funct_1(sK11) & r1_tarski(k2_relat_1(sK12),sK10) & k1_relat_1(sK12) = sK10 & k1_relat_1(sK11) = sK10 & v1_funct_1(sK12) & v1_relat_1(sK12)) & v1_funct_1(sK11) & v1_relat_1(sK11)),
% 19.29/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f21,f46,f45])).
% 19.29/3.00  
% 19.29/3.00  fof(f74,plain,(
% 19.29/3.00    v1_funct_1(sK11)),
% 19.29/3.00    inference(cnf_transformation,[],[f47])).
% 19.29/3.00  
% 19.29/3.00  fof(f73,plain,(
% 19.29/3.00    v1_relat_1(sK11)),
% 19.29/3.00    inference(cnf_transformation,[],[f47])).
% 19.29/3.00  
% 19.29/3.00  fof(f77,plain,(
% 19.29/3.00    k1_relat_1(sK11) = sK10),
% 19.29/3.00    inference(cnf_transformation,[],[f47])).
% 19.29/3.00  
% 19.29/3.00  fof(f5,axiom,(
% 19.29/3.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 19.29/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.29/3.00  
% 19.29/3.00  fof(f16,plain,(
% 19.29/3.00    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 19.29/3.00    inference(ennf_transformation,[],[f5])).
% 19.29/3.00  
% 19.29/3.00  fof(f17,plain,(
% 19.29/3.00    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.29/3.00    inference(flattening,[],[f16])).
% 19.29/3.00  
% 19.29/3.00  fof(f38,plain,(
% 19.29/3.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.29/3.00    inference(nnf_transformation,[],[f17])).
% 19.29/3.00  
% 19.29/3.00  fof(f39,plain,(
% 19.29/3.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.29/3.00    inference(flattening,[],[f38])).
% 19.29/3.00  
% 19.29/3.00  fof(f40,plain,(
% 19.29/3.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.29/3.00    inference(rectify,[],[f39])).
% 19.29/3.00  
% 19.29/3.00  fof(f41,plain,(
% 19.29/3.00    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (k1_funct_1(X1,sK9(X0,X1)) != sK9(X0,X1) & r2_hidden(sK9(X0,X1),X0)))),
% 19.29/3.00    introduced(choice_axiom,[])).
% 19.29/3.00  
% 19.29/3.00  fof(f42,plain,(
% 19.29/3.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (k1_funct_1(X1,sK9(X0,X1)) != sK9(X0,X1) & r2_hidden(sK9(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.29/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f40,f41])).
% 19.29/3.00  
% 19.29/3.00  fof(f68,plain,(
% 19.29/3.00    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK9(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.29/3.00    inference(cnf_transformation,[],[f42])).
% 19.29/3.00  
% 19.29/3.00  fof(f91,plain,(
% 19.29/3.00    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | r2_hidden(sK9(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.29/3.00    inference(equality_resolution,[],[f68])).
% 19.29/3.00  
% 19.29/3.00  fof(f76,plain,(
% 19.29/3.00    v1_funct_1(sK12)),
% 19.29/3.00    inference(cnf_transformation,[],[f47])).
% 19.29/3.00  
% 19.29/3.00  fof(f75,plain,(
% 19.29/3.00    v1_relat_1(sK12)),
% 19.29/3.00    inference(cnf_transformation,[],[f47])).
% 19.29/3.00  
% 19.29/3.00  fof(f78,plain,(
% 19.29/3.00    k1_relat_1(sK12) = sK10),
% 19.29/3.00    inference(cnf_transformation,[],[f47])).
% 19.29/3.00  
% 19.29/3.00  fof(f82,plain,(
% 19.29/3.00    k6_relat_1(sK10) != sK12),
% 19.29/3.00    inference(cnf_transformation,[],[f47])).
% 19.29/3.00  
% 19.29/3.00  fof(f81,plain,(
% 19.29/3.00    k5_relat_1(sK12,sK11) = sK11),
% 19.29/3.00    inference(cnf_transformation,[],[f47])).
% 19.29/3.00  
% 19.29/3.00  fof(f2,axiom,(
% 19.29/3.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 19.29/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.29/3.00  
% 19.29/3.00  fof(f11,plain,(
% 19.29/3.00    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.29/3.00    inference(ennf_transformation,[],[f2])).
% 19.29/3.00  
% 19.29/3.00  fof(f22,plain,(
% 19.29/3.00    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.29/3.00    inference(nnf_transformation,[],[f11])).
% 19.29/3.00  
% 19.29/3.00  fof(f23,plain,(
% 19.29/3.00    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.29/3.00    inference(rectify,[],[f22])).
% 19.29/3.00  
% 19.29/3.00  fof(f26,plain,(
% 19.29/3.00    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)))),
% 19.29/3.00    introduced(choice_axiom,[])).
% 19.29/3.00  
% 19.29/3.00  fof(f25,plain,(
% 19.29/3.00    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK2(X0,X1,X2)),X0)))) )),
% 19.29/3.00    introduced(choice_axiom,[])).
% 19.29/3.00  
% 19.29/3.00  fof(f24,plain,(
% 19.29/3.00    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK1(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2))))),
% 19.29/3.00    introduced(choice_axiom,[])).
% 19.29/3.00  
% 19.29/3.00  fof(f27,plain,(
% 19.29/3.00    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.29/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f26,f25,f24])).
% 19.29/3.00  
% 19.29/3.00  fof(f49,plain,(
% 19.29/3.00    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.29/3.00    inference(cnf_transformation,[],[f27])).
% 19.29/3.00  
% 19.29/3.00  fof(f85,plain,(
% 19.29/3.00    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK3(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.29/3.00    inference(equality_resolution,[],[f49])).
% 19.29/3.00  
% 19.29/3.00  fof(f71,plain,(
% 19.29/3.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.29/3.00    inference(cnf_transformation,[],[f44])).
% 19.29/3.00  
% 19.29/3.00  fof(f69,plain,(
% 19.29/3.00    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | k1_funct_1(X1,sK9(X0,X1)) != sK9(X0,X1) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.29/3.00    inference(cnf_transformation,[],[f42])).
% 19.29/3.00  
% 19.29/3.00  fof(f90,plain,(
% 19.29/3.00    ( ! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k1_funct_1(X1,sK9(k1_relat_1(X1),X1)) != sK9(k1_relat_1(X1),X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.29/3.00    inference(equality_resolution,[],[f69])).
% 19.29/3.00  
% 19.29/3.00  fof(f51,plain,(
% 19.29/3.00    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.29/3.00    inference(cnf_transformation,[],[f27])).
% 19.29/3.00  
% 19.29/3.00  fof(f83,plain,(
% 19.29/3.00    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.29/3.00    inference(equality_resolution,[],[f51])).
% 19.29/3.00  
% 19.29/3.00  fof(f3,axiom,(
% 19.29/3.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 19.29/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.29/3.00  
% 19.29/3.00  fof(f12,plain,(
% 19.29/3.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.29/3.00    inference(ennf_transformation,[],[f3])).
% 19.29/3.00  
% 19.29/3.00  fof(f13,plain,(
% 19.29/3.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.29/3.00    inference(flattening,[],[f12])).
% 19.29/3.00  
% 19.29/3.00  fof(f28,plain,(
% 19.29/3.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.29/3.00    inference(nnf_transformation,[],[f13])).
% 19.29/3.00  
% 19.29/3.00  fof(f29,plain,(
% 19.29/3.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.29/3.00    inference(rectify,[],[f28])).
% 19.29/3.00  
% 19.29/3.00  fof(f32,plain,(
% 19.29/3.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 19.29/3.00    introduced(choice_axiom,[])).
% 19.29/3.00  
% 19.29/3.00  fof(f31,plain,(
% 19.29/3.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) = X2 & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))) )),
% 19.29/3.00    introduced(choice_axiom,[])).
% 19.29/3.00  
% 19.29/3.00  fof(f30,plain,(
% 19.29/3.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 19.29/3.00    introduced(choice_axiom,[])).
% 19.29/3.00  
% 19.29/3.00  fof(f33,plain,(
% 19.29/3.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((k1_funct_1(X0,sK5(X0,X1)) = sK4(X0,X1) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.29/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 19.29/3.00  
% 19.29/3.00  fof(f57,plain,(
% 19.29/3.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.29/3.00    inference(cnf_transformation,[],[f33])).
% 19.29/3.00  
% 19.29/3.00  fof(f86,plain,(
% 19.29/3.00    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.29/3.00    inference(equality_resolution,[],[f57])).
% 19.29/3.00  
% 19.29/3.00  fof(f87,plain,(
% 19.29/3.00    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.29/3.00    inference(equality_resolution,[],[f86])).
% 19.29/3.00  
% 19.29/3.00  fof(f1,axiom,(
% 19.29/3.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.29/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.29/3.00  
% 19.29/3.00  fof(f9,plain,(
% 19.29/3.00    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.29/3.00    inference(unused_predicate_definition_removal,[],[f1])).
% 19.29/3.00  
% 19.29/3.00  fof(f10,plain,(
% 19.29/3.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 19.29/3.00    inference(ennf_transformation,[],[f9])).
% 19.29/3.00  
% 19.29/3.00  fof(f48,plain,(
% 19.29/3.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 19.29/3.00    inference(cnf_transformation,[],[f10])).
% 19.29/3.00  
% 19.29/3.00  fof(f79,plain,(
% 19.29/3.00    r1_tarski(k2_relat_1(sK12),sK10)),
% 19.29/3.00    inference(cnf_transformation,[],[f47])).
% 19.29/3.00  
% 19.29/3.00  fof(f4,axiom,(
% 19.29/3.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 19.29/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.29/3.00  
% 19.29/3.00  fof(f14,plain,(
% 19.29/3.00    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.29/3.00    inference(ennf_transformation,[],[f4])).
% 19.29/3.00  
% 19.29/3.00  fof(f15,plain,(
% 19.29/3.00    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.29/3.00    inference(flattening,[],[f14])).
% 19.29/3.00  
% 19.29/3.00  fof(f34,plain,(
% 19.29/3.00    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.29/3.00    inference(nnf_transformation,[],[f15])).
% 19.29/3.00  
% 19.29/3.00  fof(f35,plain,(
% 19.29/3.00    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.29/3.00    inference(rectify,[],[f34])).
% 19.29/3.00  
% 19.29/3.00  fof(f36,plain,(
% 19.29/3.00    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK7(X0) != sK8(X0) & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0))))),
% 19.29/3.00    introduced(choice_axiom,[])).
% 19.29/3.00  
% 19.29/3.00  fof(f37,plain,(
% 19.29/3.00    ! [X0] : (((v2_funct_1(X0) | (sK7(X0) != sK8(X0) & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.29/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f35,f36])).
% 19.29/3.00  
% 19.29/3.00  fof(f61,plain,(
% 19.29/3.00    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.29/3.00    inference(cnf_transformation,[],[f37])).
% 19.29/3.00  
% 19.29/3.00  fof(f80,plain,(
% 19.29/3.00    v2_funct_1(sK11)),
% 19.29/3.00    inference(cnf_transformation,[],[f47])).
% 19.29/3.00  
% 19.29/3.00  fof(f50,plain,(
% 19.29/3.00    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.29/3.00    inference(cnf_transformation,[],[f27])).
% 19.29/3.00  
% 19.29/3.00  fof(f84,plain,(
% 19.29/3.00    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.29/3.00    inference(equality_resolution,[],[f50])).
% 19.29/3.00  
% 19.29/3.00  fof(f70,plain,(
% 19.29/3.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.29/3.00    inference(cnf_transformation,[],[f44])).
% 19.29/3.00  
% 19.29/3.00  cnf(c_22,plain,
% 19.29/3.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.29/3.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 19.29/3.00      | ~ v1_funct_1(X1)
% 19.29/3.00      | ~ v1_relat_1(X1) ),
% 19.29/3.00      inference(cnf_transformation,[],[f94]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_33,negated_conjecture,
% 19.29/3.00      ( v1_funct_1(sK11) ),
% 19.29/3.00      inference(cnf_transformation,[],[f74]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_712,plain,
% 19.29/3.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.29/3.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 19.29/3.00      | ~ v1_relat_1(X1)
% 19.29/3.00      | sK11 != X1 ),
% 19.29/3.00      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_713,plain,
% 19.29/3.00      ( ~ r2_hidden(X0,k1_relat_1(sK11))
% 19.29/3.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK11,X0)),sK11)
% 19.29/3.00      | ~ v1_relat_1(sK11) ),
% 19.29/3.00      inference(unflattening,[status(thm)],[c_712]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_34,negated_conjecture,
% 19.29/3.00      ( v1_relat_1(sK11) ),
% 19.29/3.00      inference(cnf_transformation,[],[f73]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_717,plain,
% 19.29/3.00      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK11,X0)),sK11)
% 19.29/3.00      | ~ r2_hidden(X0,k1_relat_1(sK11)) ),
% 19.29/3.00      inference(global_propositional_subsumption,
% 19.29/3.00                [status(thm)],
% 19.29/3.00                [c_713,c_34]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_718,plain,
% 19.29/3.00      ( ~ r2_hidden(X0,k1_relat_1(sK11))
% 19.29/3.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK11,X0)),sK11) ),
% 19.29/3.00      inference(renaming,[status(thm)],[c_717]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_2007,plain,
% 19.29/3.00      ( r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
% 19.29/3.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK11,X0)),sK11) = iProver_top ),
% 19.29/3.00      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_30,negated_conjecture,
% 19.29/3.00      ( k1_relat_1(sK11) = sK10 ),
% 19.29/3.00      inference(cnf_transformation,[],[f77]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_2039,plain,
% 19.29/3.00      ( r2_hidden(X0,sK10) != iProver_top
% 19.29/3.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK11,X0)),sK11) = iProver_top ),
% 19.29/3.00      inference(light_normalisation,[status(thm)],[c_2007,c_30]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_19,plain,
% 19.29/3.00      ( r2_hidden(sK9(k1_relat_1(X0),X0),k1_relat_1(X0))
% 19.29/3.00      | ~ v1_funct_1(X0)
% 19.29/3.00      | ~ v1_relat_1(X0)
% 19.29/3.00      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 19.29/3.00      inference(cnf_transformation,[],[f91]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_31,negated_conjecture,
% 19.29/3.00      ( v1_funct_1(sK12) ),
% 19.29/3.00      inference(cnf_transformation,[],[f76]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_828,plain,
% 19.29/3.00      ( r2_hidden(sK9(k1_relat_1(X0),X0),k1_relat_1(X0))
% 19.29/3.00      | ~ v1_relat_1(X0)
% 19.29/3.00      | k6_relat_1(k1_relat_1(X0)) = X0
% 19.29/3.00      | sK12 != X0 ),
% 19.29/3.00      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_829,plain,
% 19.29/3.00      ( r2_hidden(sK9(k1_relat_1(sK12),sK12),k1_relat_1(sK12))
% 19.29/3.00      | ~ v1_relat_1(sK12)
% 19.29/3.00      | k6_relat_1(k1_relat_1(sK12)) = sK12 ),
% 19.29/3.00      inference(unflattening,[status(thm)],[c_828]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_32,negated_conjecture,
% 19.29/3.00      ( v1_relat_1(sK12) ),
% 19.29/3.00      inference(cnf_transformation,[],[f75]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_831,plain,
% 19.29/3.00      ( r2_hidden(sK9(k1_relat_1(sK12),sK12),k1_relat_1(sK12))
% 19.29/3.00      | k6_relat_1(k1_relat_1(sK12)) = sK12 ),
% 19.29/3.00      inference(global_propositional_subsumption,
% 19.29/3.00                [status(thm)],
% 19.29/3.00                [c_829,c_32]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_2002,plain,
% 19.29/3.00      ( k6_relat_1(k1_relat_1(sK12)) = sK12
% 19.29/3.00      | r2_hidden(sK9(k1_relat_1(sK12),sK12),k1_relat_1(sK12)) = iProver_top ),
% 19.29/3.00      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_29,negated_conjecture,
% 19.29/3.00      ( k1_relat_1(sK12) = sK10 ),
% 19.29/3.00      inference(cnf_transformation,[],[f78]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_2032,plain,
% 19.29/3.00      ( k6_relat_1(sK10) = sK12
% 19.29/3.00      | r2_hidden(sK9(sK10,sK12),sK10) = iProver_top ),
% 19.29/3.00      inference(light_normalisation,[status(thm)],[c_2002,c_29]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_25,negated_conjecture,
% 19.29/3.00      ( k6_relat_1(sK10) != sK12 ),
% 19.29/3.00      inference(cnf_transformation,[],[f82]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_2590,plain,
% 19.29/3.00      ( r2_hidden(sK9(sK10,sK12),sK10) = iProver_top ),
% 19.29/3.00      inference(global_propositional_subsumption,
% 19.29/3.00                [status(thm)],
% 19.29/3.00                [c_2032,c_25]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_26,negated_conjecture,
% 19.29/3.00      ( k5_relat_1(sK12,sK11) = sK11 ),
% 19.29/3.00      inference(cnf_transformation,[],[f81]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_6,plain,
% 19.29/3.00      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 19.29/3.00      | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2)
% 19.29/3.00      | ~ v1_relat_1(X3)
% 19.29/3.00      | ~ v1_relat_1(X2)
% 19.29/3.00      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 19.29/3.00      inference(cnf_transformation,[],[f85]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_2023,plain,
% 19.29/3.00      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 19.29/3.00      | r2_hidden(k4_tarski(X0,sK3(X2,X3,X0,X1)),X2) = iProver_top
% 19.29/3.00      | v1_relat_1(X2) != iProver_top
% 19.29/3.00      | v1_relat_1(X3) != iProver_top
% 19.29/3.00      | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
% 19.29/3.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_23,plain,
% 19.29/3.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 19.29/3.00      | ~ v1_funct_1(X2)
% 19.29/3.00      | ~ v1_relat_1(X2)
% 19.29/3.00      | k1_funct_1(X2,X0) = X1 ),
% 19.29/3.00      inference(cnf_transformation,[],[f71]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_517,plain,
% 19.29/3.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 19.29/3.00      | ~ v1_relat_1(X2)
% 19.29/3.00      | k1_funct_1(X2,X0) = X1
% 19.29/3.00      | sK12 != X2 ),
% 19.29/3.00      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_518,plain,
% 19.29/3.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
% 19.29/3.00      | ~ v1_relat_1(sK12)
% 19.29/3.00      | k1_funct_1(sK12,X0) = X1 ),
% 19.29/3.00      inference(unflattening,[status(thm)],[c_517]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_522,plain,
% 19.29/3.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK12) | k1_funct_1(sK12,X0) = X1 ),
% 19.29/3.00      inference(global_propositional_subsumption,
% 19.29/3.00                [status(thm)],
% 19.29/3.00                [c_518,c_32]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_2017,plain,
% 19.29/3.00      ( k1_funct_1(sK12,X0) = X1
% 19.29/3.00      | r2_hidden(k4_tarski(X0,X1),sK12) != iProver_top ),
% 19.29/3.00      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_3711,plain,
% 19.29/3.00      ( sK3(sK12,X0,X1,X2) = k1_funct_1(sK12,X1)
% 19.29/3.00      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK12,X0)) != iProver_top
% 19.29/3.00      | v1_relat_1(X0) != iProver_top
% 19.29/3.00      | v1_relat_1(k5_relat_1(sK12,X0)) != iProver_top
% 19.29/3.00      | v1_relat_1(sK12) != iProver_top ),
% 19.29/3.00      inference(superposition,[status(thm)],[c_2023,c_2017]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_37,plain,
% 19.29/3.00      ( v1_relat_1(sK12) = iProver_top ),
% 19.29/3.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_47951,plain,
% 19.29/3.00      ( v1_relat_1(k5_relat_1(sK12,X0)) != iProver_top
% 19.29/3.00      | v1_relat_1(X0) != iProver_top
% 19.29/3.00      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK12,X0)) != iProver_top
% 19.29/3.00      | sK3(sK12,X0,X1,X2) = k1_funct_1(sK12,X1) ),
% 19.29/3.00      inference(global_propositional_subsumption,
% 19.29/3.00                [status(thm)],
% 19.29/3.00                [c_3711,c_37]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_47952,plain,
% 19.29/3.00      ( sK3(sK12,X0,X1,X2) = k1_funct_1(sK12,X1)
% 19.29/3.00      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(sK12,X0)) != iProver_top
% 19.29/3.00      | v1_relat_1(X0) != iProver_top
% 19.29/3.00      | v1_relat_1(k5_relat_1(sK12,X0)) != iProver_top ),
% 19.29/3.00      inference(renaming,[status(thm)],[c_47951]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_47981,plain,
% 19.29/3.00      ( sK3(sK12,sK11,X0,X1) = k1_funct_1(sK12,X0)
% 19.29/3.00      | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
% 19.29/3.00      | v1_relat_1(k5_relat_1(sK12,sK11)) != iProver_top
% 19.29/3.00      | v1_relat_1(sK11) != iProver_top ),
% 19.29/3.00      inference(superposition,[status(thm)],[c_26,c_47952]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_47982,plain,
% 19.29/3.00      ( sK3(sK12,sK11,X0,X1) = k1_funct_1(sK12,X0)
% 19.29/3.00      | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
% 19.29/3.00      | v1_relat_1(sK11) != iProver_top ),
% 19.29/3.00      inference(light_normalisation,[status(thm)],[c_47981,c_26]) ).
% 19.29/3.00  
% 19.29/3.00  cnf(c_35,plain,
% 19.29/3.01      ( v1_relat_1(sK11) = iProver_top ),
% 19.29/3.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_48050,plain,
% 19.29/3.01      ( r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
% 19.29/3.01      | sK3(sK12,sK11,X0,X1) = k1_funct_1(sK12,X0) ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_47982,c_35]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_48051,plain,
% 19.29/3.01      ( sK3(sK12,sK11,X0,X1) = k1_funct_1(sK12,X0)
% 19.29/3.01      | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
% 19.29/3.01      inference(renaming,[status(thm)],[c_48050]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_48064,plain,
% 19.29/3.01      ( sK3(sK12,sK11,X0,k1_funct_1(sK11,X0)) = k1_funct_1(sK12,X0)
% 19.29/3.01      | r2_hidden(X0,sK10) != iProver_top ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_2039,c_48051]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_48325,plain,
% 19.29/3.01      ( sK3(sK12,sK11,sK9(sK10,sK12),k1_funct_1(sK11,sK9(sK10,sK12))) = k1_funct_1(sK12,sK9(sK10,sK12)) ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_2590,c_48064]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_48609,plain,
% 19.29/3.01      ( r2_hidden(k4_tarski(sK9(sK10,sK12),k1_funct_1(sK11,sK9(sK10,sK12))),k5_relat_1(sK12,sK11)) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(sK9(sK10,sK12),k1_funct_1(sK12,sK9(sK10,sK12))),sK12) = iProver_top
% 19.29/3.01      | v1_relat_1(k5_relat_1(sK12,sK11)) != iProver_top
% 19.29/3.01      | v1_relat_1(sK11) != iProver_top
% 19.29/3.01      | v1_relat_1(sK12) != iProver_top ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_48325,c_2023]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_48613,plain,
% 19.29/3.01      ( r2_hidden(k4_tarski(sK9(sK10,sK12),k1_funct_1(sK11,sK9(sK10,sK12))),sK11) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(sK9(sK10,sK12),k1_funct_1(sK12,sK9(sK10,sK12))),sK12) = iProver_top
% 19.29/3.01      | v1_relat_1(sK11) != iProver_top
% 19.29/3.01      | v1_relat_1(sK12) != iProver_top ),
% 19.29/3.01      inference(light_normalisation,[status(thm)],[c_48609,c_26]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_18,plain,
% 19.29/3.01      ( ~ v1_funct_1(X0)
% 19.29/3.01      | ~ v1_relat_1(X0)
% 19.29/3.01      | k1_funct_1(X0,sK9(k1_relat_1(X0),X0)) != sK9(k1_relat_1(X0),X0)
% 19.29/3.01      | k6_relat_1(k1_relat_1(X0)) = X0 ),
% 19.29/3.01      inference(cnf_transformation,[],[f90]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_842,plain,
% 19.29/3.01      ( ~ v1_relat_1(X0)
% 19.29/3.01      | k1_funct_1(X0,sK9(k1_relat_1(X0),X0)) != sK9(k1_relat_1(X0),X0)
% 19.29/3.01      | k6_relat_1(k1_relat_1(X0)) = X0
% 19.29/3.01      | sK12 != X0 ),
% 19.29/3.01      inference(resolution_lifted,[status(thm)],[c_18,c_31]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_843,plain,
% 19.29/3.01      ( ~ v1_relat_1(sK12)
% 19.29/3.01      | k1_funct_1(sK12,sK9(k1_relat_1(sK12),sK12)) != sK9(k1_relat_1(sK12),sK12)
% 19.29/3.01      | k6_relat_1(k1_relat_1(sK12)) = sK12 ),
% 19.29/3.01      inference(unflattening,[status(thm)],[c_842]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_845,plain,
% 19.29/3.01      ( k1_funct_1(sK12,sK9(k1_relat_1(sK12),sK12)) != sK9(k1_relat_1(sK12),sK12)
% 19.29/3.01      | k6_relat_1(k1_relat_1(sK12)) = sK12 ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_843,c_32]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2042,plain,
% 19.29/3.01      ( k1_funct_1(sK12,sK9(sK10,sK12)) != sK9(sK10,sK12)
% 19.29/3.01      | k6_relat_1(sK10) = sK12 ),
% 19.29/3.01      inference(light_normalisation,[status(thm)],[c_845,c_29]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_571,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.29/3.01      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 19.29/3.01      | ~ v1_relat_1(X1)
% 19.29/3.01      | sK12 != X1 ),
% 19.29/3.01      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_572,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(sK12))
% 19.29/3.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK12,X0)),sK12)
% 19.29/3.01      | ~ v1_relat_1(sK12) ),
% 19.29/3.01      inference(unflattening,[status(thm)],[c_571]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_576,plain,
% 19.29/3.01      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK12,X0)),sK12)
% 19.29/3.01      | ~ r2_hidden(X0,k1_relat_1(sK12)) ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_572,c_32]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_577,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(sK12))
% 19.29/3.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK12,X0)),sK12) ),
% 19.29/3.01      inference(renaming,[status(thm)],[c_576]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2014,plain,
% 19.29/3.01      ( r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK12,X0)),sK12) = iProver_top ),
% 19.29/3.01      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2040,plain,
% 19.29/3.01      ( r2_hidden(X0,sK10) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X0,k1_funct_1(sK12,X0)),sK12) = iProver_top ),
% 19.29/3.01      inference(light_normalisation,[status(thm)],[c_2014,c_29]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_4,plain,
% 19.29/3.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 19.29/3.01      | ~ r2_hidden(k4_tarski(X3,X0),X4)
% 19.29/3.01      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
% 19.29/3.01      | ~ v1_relat_1(X2)
% 19.29/3.01      | ~ v1_relat_1(X4)
% 19.29/3.01      | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
% 19.29/3.01      inference(cnf_transformation,[],[f83]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2025,plain,
% 19.29/3.01      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X3,X0),X4) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2)) = iProver_top
% 19.29/3.01      | v1_relat_1(X2) != iProver_top
% 19.29/3.01      | v1_relat_1(X4) != iProver_top
% 19.29/3.01      | v1_relat_1(k5_relat_1(X4,X2)) != iProver_top ),
% 19.29/3.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_3616,plain,
% 19.29/3.01      ( r2_hidden(X0,sK10) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,k1_funct_1(sK11,X0)),k5_relat_1(X2,sK11)) = iProver_top
% 19.29/3.01      | v1_relat_1(X2) != iProver_top
% 19.29/3.01      | v1_relat_1(k5_relat_1(X2,sK11)) != iProver_top
% 19.29/3.01      | v1_relat_1(sK11) != iProver_top ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_2039,c_2025]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_17271,plain,
% 19.29/3.01      ( v1_relat_1(k5_relat_1(X2,sK11)) != iProver_top
% 19.29/3.01      | v1_relat_1(X2) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,k1_funct_1(sK11,X0)),k5_relat_1(X2,sK11)) = iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
% 19.29/3.01      | r2_hidden(X0,sK10) != iProver_top ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_3616,c_35]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_17272,plain,
% 19.29/3.01      ( r2_hidden(X0,sK10) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,X0),X2) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,k1_funct_1(sK11,X0)),k5_relat_1(X2,sK11)) = iProver_top
% 19.29/3.01      | v1_relat_1(X2) != iProver_top
% 19.29/3.01      | v1_relat_1(k5_relat_1(X2,sK11)) != iProver_top ),
% 19.29/3.01      inference(renaming,[status(thm)],[c_17271]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_17284,plain,
% 19.29/3.01      ( r2_hidden(X0,sK10) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,X0),sK12) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,k1_funct_1(sK11,X0)),sK11) = iProver_top
% 19.29/3.01      | v1_relat_1(k5_relat_1(sK12,sK11)) != iProver_top
% 19.29/3.01      | v1_relat_1(sK12) != iProver_top ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_26,c_17272]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_17292,plain,
% 19.29/3.01      ( r2_hidden(X0,sK10) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,X0),sK12) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,k1_funct_1(sK11,X0)),sK11) = iProver_top
% 19.29/3.01      | v1_relat_1(sK11) != iProver_top
% 19.29/3.01      | v1_relat_1(sK12) != iProver_top ),
% 19.29/3.01      inference(light_normalisation,[status(thm)],[c_17284,c_26]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_17330,plain,
% 19.29/3.01      ( r2_hidden(X0,sK10) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,X0),sK12) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,k1_funct_1(sK11,X0)),sK11) = iProver_top ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_17292,c_35,c_37]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_535,plain,
% 19.29/3.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 19.29/3.01      | ~ v1_relat_1(X2)
% 19.29/3.01      | k1_funct_1(X2,X0) = X1
% 19.29/3.01      | sK11 != X2 ),
% 19.29/3.01      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_536,plain,
% 19.29/3.01      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 19.29/3.01      | ~ v1_relat_1(sK11)
% 19.29/3.01      | k1_funct_1(sK11,X0) = X1 ),
% 19.29/3.01      inference(unflattening,[status(thm)],[c_535]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_540,plain,
% 19.29/3.01      ( ~ r2_hidden(k4_tarski(X0,X1),sK11) | k1_funct_1(sK11,X0) = X1 ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_536,c_34]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2016,plain,
% 19.29/3.01      ( k1_funct_1(sK11,X0) = X1
% 19.29/3.01      | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
% 19.29/3.01      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_17352,plain,
% 19.29/3.01      ( k1_funct_1(sK11,X0) = k1_funct_1(sK11,X1)
% 19.29/3.01      | r2_hidden(X1,sK10) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X0,X1),sK12) != iProver_top ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_17330,c_2016]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_17628,plain,
% 19.29/3.01      ( k1_funct_1(sK11,k1_funct_1(sK12,X0)) = k1_funct_1(sK11,X0)
% 19.29/3.01      | r2_hidden(X0,sK10) != iProver_top
% 19.29/3.01      | r2_hidden(k1_funct_1(sK12,X0),sK10) != iProver_top ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_2040,c_17352]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_10,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.29/3.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 19.29/3.01      | ~ v1_funct_1(X1)
% 19.29/3.01      | ~ v1_relat_1(X1) ),
% 19.29/3.01      inference(cnf_transformation,[],[f87]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_652,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.29/3.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 19.29/3.01      | ~ v1_relat_1(X1)
% 19.29/3.01      | sK12 != X1 ),
% 19.29/3.01      inference(resolution_lifted,[status(thm)],[c_10,c_31]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_653,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(sK12))
% 19.29/3.01      | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12))
% 19.29/3.01      | ~ v1_relat_1(sK12) ),
% 19.29/3.01      inference(unflattening,[status(thm)],[c_652]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_657,plain,
% 19.29/3.01      ( r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12))
% 19.29/3.01      | ~ r2_hidden(X0,k1_relat_1(sK12)) ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_653,c_32]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_658,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(sK12))
% 19.29/3.01      | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) ),
% 19.29/3.01      inference(renaming,[status(thm)],[c_657]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2010,plain,
% 19.29/3.01      ( r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
% 19.29/3.01      | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) = iProver_top ),
% 19.29/3.01      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2037,plain,
% 19.29/3.01      ( r2_hidden(X0,sK10) != iProver_top
% 19.29/3.01      | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) = iProver_top ),
% 19.29/3.01      inference(light_normalisation,[status(thm)],[c_2010,c_29]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_0,plain,
% 19.29/3.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 19.29/3.01      inference(cnf_transformation,[],[f48]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_28,negated_conjecture,
% 19.29/3.01      ( r1_tarski(k2_relat_1(sK12),sK10) ),
% 19.29/3.01      inference(cnf_transformation,[],[f79]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_338,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,X1)
% 19.29/3.01      | r2_hidden(X0,X2)
% 19.29/3.01      | k2_relat_1(sK12) != X1
% 19.29/3.01      | sK10 != X2 ),
% 19.29/3.01      inference(resolution_lifted,[status(thm)],[c_0,c_28]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_339,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k2_relat_1(sK12)) | r2_hidden(X0,sK10) ),
% 19.29/3.01      inference(unflattening,[status(thm)],[c_338]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2019,plain,
% 19.29/3.01      ( r2_hidden(X0,k2_relat_1(sK12)) != iProver_top
% 19.29/3.01      | r2_hidden(X0,sK10) = iProver_top ),
% 19.29/3.01      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_3425,plain,
% 19.29/3.01      ( r2_hidden(X0,sK10) != iProver_top
% 19.29/3.01      | r2_hidden(k1_funct_1(sK12,X0),sK10) = iProver_top ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_2037,c_2019]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_17679,plain,
% 19.29/3.01      ( r2_hidden(X0,sK10) != iProver_top
% 19.29/3.01      | k1_funct_1(sK11,k1_funct_1(sK12,X0)) = k1_funct_1(sK11,X0) ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_17628,c_3425]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_17680,plain,
% 19.29/3.01      ( k1_funct_1(sK11,k1_funct_1(sK12,X0)) = k1_funct_1(sK11,X0)
% 19.29/3.01      | r2_hidden(X0,sK10) != iProver_top ),
% 19.29/3.01      inference(renaming,[status(thm)],[c_17679]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_17704,plain,
% 19.29/3.01      ( k1_funct_1(sK11,k1_funct_1(sK12,sK9(sK10,sK12))) = k1_funct_1(sK11,sK9(sK10,sK12)) ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_2590,c_17680]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_17,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.29/3.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 19.29/3.01      | ~ v2_funct_1(X1)
% 19.29/3.01      | ~ v1_funct_1(X1)
% 19.29/3.01      | ~ v1_relat_1(X1)
% 19.29/3.01      | X2 = X0
% 19.29/3.01      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0) ),
% 19.29/3.01      inference(cnf_transformation,[],[f61]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_730,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.29/3.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 19.29/3.01      | ~ v2_funct_1(X1)
% 19.29/3.01      | ~ v1_relat_1(X1)
% 19.29/3.01      | X2 = X0
% 19.29/3.01      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 19.29/3.01      | sK11 != X1 ),
% 19.29/3.01      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_731,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(sK11))
% 19.29/3.01      | ~ r2_hidden(X1,k1_relat_1(sK11))
% 19.29/3.01      | ~ v2_funct_1(sK11)
% 19.29/3.01      | ~ v1_relat_1(sK11)
% 19.29/3.01      | X0 = X1
% 19.29/3.01      | k1_funct_1(sK11,X0) != k1_funct_1(sK11,X1) ),
% 19.29/3.01      inference(unflattening,[status(thm)],[c_730]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_27,negated_conjecture,
% 19.29/3.01      ( v2_funct_1(sK11) ),
% 19.29/3.01      inference(cnf_transformation,[],[f80]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_461,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.29/3.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 19.29/3.01      | ~ v1_funct_1(X1)
% 19.29/3.01      | ~ v1_relat_1(X1)
% 19.29/3.01      | X2 = X0
% 19.29/3.01      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 19.29/3.01      | sK11 != X1 ),
% 19.29/3.01      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_462,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(sK11))
% 19.29/3.01      | ~ r2_hidden(X1,k1_relat_1(sK11))
% 19.29/3.01      | ~ v1_funct_1(sK11)
% 19.29/3.01      | ~ v1_relat_1(sK11)
% 19.29/3.01      | X0 = X1
% 19.29/3.01      | k1_funct_1(sK11,X0) != k1_funct_1(sK11,X1) ),
% 19.29/3.01      inference(unflattening,[status(thm)],[c_461]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_466,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(sK11))
% 19.29/3.01      | ~ r2_hidden(X1,k1_relat_1(sK11))
% 19.29/3.01      | X0 = X1
% 19.29/3.01      | k1_funct_1(sK11,X0) != k1_funct_1(sK11,X1) ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_462,c_34,c_33]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_733,plain,
% 19.29/3.01      ( ~ r2_hidden(X0,k1_relat_1(sK11))
% 19.29/3.01      | ~ r2_hidden(X1,k1_relat_1(sK11))
% 19.29/3.01      | X0 = X1
% 19.29/3.01      | k1_funct_1(sK11,X0) != k1_funct_1(sK11,X1) ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_731,c_34,c_33,c_462]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2018,plain,
% 19.29/3.01      ( X0 = X1
% 19.29/3.01      | k1_funct_1(sK11,X0) != k1_funct_1(sK11,X1)
% 19.29/3.01      | r2_hidden(X0,k1_relat_1(sK11)) != iProver_top
% 19.29/3.01      | r2_hidden(X1,k1_relat_1(sK11)) != iProver_top ),
% 19.29/3.01      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2045,plain,
% 19.29/3.01      ( X0 = X1
% 19.29/3.01      | k1_funct_1(sK11,X0) != k1_funct_1(sK11,X1)
% 19.29/3.01      | r2_hidden(X1,sK10) != iProver_top
% 19.29/3.01      | r2_hidden(X0,sK10) != iProver_top ),
% 19.29/3.01      inference(light_normalisation,[status(thm)],[c_2018,c_30]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_17775,plain,
% 19.29/3.01      ( k1_funct_1(sK11,sK9(sK10,sK12)) != k1_funct_1(sK11,X0)
% 19.29/3.01      | k1_funct_1(sK12,sK9(sK10,sK12)) = X0
% 19.29/3.01      | r2_hidden(X0,sK10) != iProver_top
% 19.29/3.01      | r2_hidden(k1_funct_1(sK12,sK9(sK10,sK12)),sK10) != iProver_top ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_17704,c_2045]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_23603,plain,
% 19.29/3.01      ( k1_funct_1(sK12,sK9(sK10,sK12)) = sK9(sK10,sK12)
% 19.29/3.01      | r2_hidden(sK9(sK10,sK12),sK10) != iProver_top
% 19.29/3.01      | r2_hidden(k1_funct_1(sK12,sK9(sK10,sK12)),sK10) != iProver_top ),
% 19.29/3.01      inference(equality_resolution,[status(thm)],[c_17775]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_5,plain,
% 19.29/3.01      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 19.29/3.01      | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3)
% 19.29/3.01      | ~ v1_relat_1(X3)
% 19.29/3.01      | ~ v1_relat_1(X2)
% 19.29/3.01      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 19.29/3.01      inference(cnf_transformation,[],[f84]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2024,plain,
% 19.29/3.01      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(sK3(X2,X3,X0,X1),X1),X3) = iProver_top
% 19.29/3.01      | v1_relat_1(X2) != iProver_top
% 19.29/3.01      | v1_relat_1(X3) != iProver_top
% 19.29/3.01      | v1_relat_1(k5_relat_1(X2,X3)) != iProver_top ),
% 19.29/3.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_24,plain,
% 19.29/3.01      ( r2_hidden(X0,k1_relat_1(X1))
% 19.29/3.01      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 19.29/3.01      | ~ v1_funct_1(X1)
% 19.29/3.01      | ~ v1_relat_1(X1) ),
% 19.29/3.01      inference(cnf_transformation,[],[f70]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_694,plain,
% 19.29/3.01      ( r2_hidden(X0,k1_relat_1(X1))
% 19.29/3.01      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 19.29/3.01      | ~ v1_relat_1(X1)
% 19.29/3.01      | sK11 != X1 ),
% 19.29/3.01      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_695,plain,
% 19.29/3.01      ( r2_hidden(X0,k1_relat_1(sK11))
% 19.29/3.01      | ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 19.29/3.01      | ~ v1_relat_1(sK11) ),
% 19.29/3.01      inference(unflattening,[status(thm)],[c_694]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_699,plain,
% 19.29/3.01      ( ~ r2_hidden(k4_tarski(X0,X1),sK11)
% 19.29/3.01      | r2_hidden(X0,k1_relat_1(sK11)) ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_695,c_34]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_700,plain,
% 19.29/3.01      ( r2_hidden(X0,k1_relat_1(sK11))
% 19.29/3.01      | ~ r2_hidden(k4_tarski(X0,X1),sK11) ),
% 19.29/3.01      inference(renaming,[status(thm)],[c_699]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2008,plain,
% 19.29/3.01      ( r2_hidden(X0,k1_relat_1(sK11)) = iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
% 19.29/3.01      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_2033,plain,
% 19.29/3.01      ( r2_hidden(X0,sK10) = iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
% 19.29/3.01      inference(light_normalisation,[status(thm)],[c_2008,c_30]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_3599,plain,
% 19.29/3.01      ( r2_hidden(sK3(X0,sK11,X1,X2),sK10) = iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK11)) != iProver_top
% 19.29/3.01      | v1_relat_1(X0) != iProver_top
% 19.29/3.01      | v1_relat_1(k5_relat_1(X0,sK11)) != iProver_top
% 19.29/3.01      | v1_relat_1(sK11) != iProver_top ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_2024,c_2033]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_11562,plain,
% 19.29/3.01      ( v1_relat_1(k5_relat_1(X0,sK11)) != iProver_top
% 19.29/3.01      | v1_relat_1(X0) != iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK11)) != iProver_top
% 19.29/3.01      | r2_hidden(sK3(X0,sK11,X1,X2),sK10) = iProver_top ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_3599,c_35]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_11563,plain,
% 19.29/3.01      ( r2_hidden(sK3(X0,sK11,X1,X2),sK10) = iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,sK11)) != iProver_top
% 19.29/3.01      | v1_relat_1(X0) != iProver_top
% 19.29/3.01      | v1_relat_1(k5_relat_1(X0,sK11)) != iProver_top ),
% 19.29/3.01      inference(renaming,[status(thm)],[c_11562]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_11572,plain,
% 19.29/3.01      ( r2_hidden(sK3(sK12,sK11,X0,X1),sK10) = iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
% 19.29/3.01      | v1_relat_1(k5_relat_1(sK12,sK11)) != iProver_top
% 19.29/3.01      | v1_relat_1(sK12) != iProver_top ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_26,c_11563]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_11573,plain,
% 19.29/3.01      ( r2_hidden(sK3(sK12,sK11,X0,X1),sK10) = iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top
% 19.29/3.01      | v1_relat_1(sK11) != iProver_top
% 19.29/3.01      | v1_relat_1(sK12) != iProver_top ),
% 19.29/3.01      inference(light_normalisation,[status(thm)],[c_11572,c_26]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_11741,plain,
% 19.29/3.01      ( r2_hidden(sK3(sK12,sK11,X0,X1),sK10) = iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(X0,X1),sK11) != iProver_top ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_11573,c_35,c_37]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_48611,plain,
% 19.29/3.01      ( r2_hidden(k1_funct_1(sK12,sK9(sK10,sK12)),sK10) = iProver_top
% 19.29/3.01      | r2_hidden(k4_tarski(sK9(sK10,sK12),k1_funct_1(sK11,sK9(sK10,sK12))),sK11) != iProver_top ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_48325,c_11741]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_48626,plain,
% 19.29/3.01      ( r2_hidden(k4_tarski(sK9(sK10,sK12),k1_funct_1(sK11,sK9(sK10,sK12))),sK11) != iProver_top ),
% 19.29/3.01      inference(global_propositional_subsumption,
% 19.29/3.01                [status(thm)],
% 19.29/3.01                [c_48613,c_25,c_2042,c_2032,c_23603,c_48611]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(c_48630,plain,
% 19.29/3.01      ( r2_hidden(sK9(sK10,sK12),sK10) != iProver_top ),
% 19.29/3.01      inference(superposition,[status(thm)],[c_2039,c_48626]) ).
% 19.29/3.01  
% 19.29/3.01  cnf(contradiction,plain,
% 19.29/3.01      ( $false ),
% 19.29/3.01      inference(minisat,[status(thm)],[c_48630,c_2032,c_25]) ).
% 19.29/3.01  
% 19.29/3.01  
% 19.29/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.29/3.01  
% 19.29/3.01  ------                               Statistics
% 19.29/3.01  
% 19.29/3.01  ------ General
% 19.29/3.01  
% 19.29/3.01  abstr_ref_over_cycles:                  0
% 19.29/3.01  abstr_ref_under_cycles:                 0
% 19.29/3.01  gc_basic_clause_elim:                   0
% 19.29/3.01  forced_gc_time:                         0
% 19.29/3.01  parsing_time:                           0.021
% 19.29/3.01  unif_index_cands_time:                  0.
% 19.29/3.01  unif_index_add_time:                    0.
% 19.29/3.01  orderings_time:                         0.
% 19.29/3.01  out_proof_time:                         0.021
% 19.29/3.01  total_time:                             2.28
% 19.29/3.01  num_of_symbols:                         55
% 19.29/3.01  num_of_terms:                           58059
% 19.29/3.01  
% 19.29/3.01  ------ Preprocessing
% 19.29/3.01  
% 19.29/3.01  num_of_splits:                          0
% 19.29/3.01  num_of_split_atoms:                     0
% 19.29/3.01  num_of_reused_defs:                     0
% 19.29/3.01  num_eq_ax_congr_red:                    38
% 19.29/3.01  num_of_sem_filtered_clauses:            1
% 19.29/3.01  num_of_subtypes:                        0
% 19.29/3.01  monotx_restored_types:                  0
% 19.29/3.01  sat_num_of_epr_types:                   0
% 19.29/3.01  sat_num_of_non_cyclic_types:            0
% 19.29/3.01  sat_guarded_non_collapsed_types:        0
% 19.29/3.01  num_pure_diseq_elim:                    0
% 19.29/3.01  simp_replaced_by:                       0
% 19.29/3.01  res_preprocessed:                       162
% 19.29/3.01  prep_upred:                             0
% 19.29/3.01  prep_unflattend:                        39
% 19.29/3.01  smt_new_axioms:                         0
% 19.29/3.01  pred_elim_cands:                        5
% 19.29/3.01  pred_elim:                              2
% 19.29/3.01  pred_elim_cl:                           -11
% 19.29/3.01  pred_elim_cycles:                       4
% 19.29/3.01  merged_defs:                            0
% 19.29/3.01  merged_defs_ncl:                        0
% 19.29/3.01  bin_hyper_res:                          0
% 19.29/3.01  prep_cycles:                            3
% 19.29/3.01  pred_elim_time:                         0.025
% 19.29/3.01  splitting_time:                         0.
% 19.29/3.01  sem_filter_time:                        0.
% 19.29/3.01  monotx_time:                            0.001
% 19.29/3.01  subtype_inf_time:                       0.
% 19.29/3.01  
% 19.29/3.01  ------ Problem properties
% 19.29/3.01  
% 19.29/3.01  clauses:                                46
% 19.29/3.01  conjectures:                            7
% 19.29/3.01  epr:                                    3
% 19.29/3.01  horn:                                   35
% 19.29/3.01  ground:                                 15
% 19.29/3.01  unary:                                  7
% 19.29/3.01  binary:                                 21
% 19.29/3.01  lits:                                   127
% 19.29/3.01  lits_eq:                                41
% 19.29/3.01  fd_pure:                                0
% 19.29/3.01  fd_pseudo:                              0
% 19.29/3.01  fd_cond:                                6
% 19.29/3.01  fd_pseudo_cond:                         7
% 19.29/3.01  ac_symbols:                             0
% 19.29/3.01  
% 19.29/3.01  ------ Propositional Solver
% 19.29/3.01  
% 19.29/3.01  prop_solver_calls:                      32
% 19.29/3.01  prop_fast_solver_calls:                 2291
% 19.29/3.01  smt_solver_calls:                       0
% 19.29/3.01  smt_fast_solver_calls:                  0
% 19.29/3.01  prop_num_of_clauses:                    31719
% 19.29/3.01  prop_preprocess_simplified:             26822
% 19.29/3.01  prop_fo_subsumed:                       79
% 19.29/3.01  prop_solver_time:                       0.
% 19.29/3.01  smt_solver_time:                        0.
% 19.29/3.01  smt_fast_solver_time:                   0.
% 19.29/3.01  prop_fast_solver_time:                  0.
% 19.29/3.01  prop_unsat_core_time:                   0.002
% 19.29/3.01  
% 19.29/3.01  ------ QBF
% 19.29/3.01  
% 19.29/3.01  qbf_q_res:                              0
% 19.29/3.01  qbf_num_tautologies:                    0
% 19.29/3.01  qbf_prep_cycles:                        0
% 19.29/3.01  
% 19.29/3.01  ------ BMC1
% 19.29/3.01  
% 19.29/3.01  bmc1_current_bound:                     -1
% 19.29/3.01  bmc1_last_solved_bound:                 -1
% 19.29/3.01  bmc1_unsat_core_size:                   -1
% 19.29/3.01  bmc1_unsat_core_parents_size:           -1
% 19.29/3.01  bmc1_merge_next_fun:                    0
% 19.29/3.01  bmc1_unsat_core_clauses_time:           0.
% 19.29/3.01  
% 19.29/3.01  ------ Instantiation
% 19.29/3.01  
% 19.29/3.01  inst_num_of_clauses:                    3783
% 19.29/3.01  inst_num_in_passive:                    1599
% 19.29/3.01  inst_num_in_active:                     1351
% 19.29/3.01  inst_num_in_unprocessed:                833
% 19.29/3.01  inst_num_of_loops:                      1880
% 19.29/3.01  inst_num_of_learning_restarts:          0
% 19.29/3.01  inst_num_moves_active_passive:          526
% 19.29/3.01  inst_lit_activity:                      0
% 19.29/3.01  inst_lit_activity_moves:                1
% 19.29/3.01  inst_num_tautologies:                   0
% 19.29/3.01  inst_num_prop_implied:                  0
% 19.29/3.01  inst_num_existing_simplified:           0
% 19.29/3.01  inst_num_eq_res_simplified:             0
% 19.29/3.01  inst_num_child_elim:                    0
% 19.29/3.01  inst_num_of_dismatching_blockings:      2437
% 19.29/3.01  inst_num_of_non_proper_insts:           4682
% 19.29/3.01  inst_num_of_duplicates:                 0
% 19.29/3.01  inst_inst_num_from_inst_to_res:         0
% 19.29/3.01  inst_dismatching_checking_time:         0.
% 19.29/3.01  
% 19.29/3.01  ------ Resolution
% 19.29/3.01  
% 19.29/3.01  res_num_of_clauses:                     0
% 19.29/3.01  res_num_in_passive:                     0
% 19.29/3.01  res_num_in_active:                      0
% 19.29/3.01  res_num_of_loops:                       165
% 19.29/3.01  res_forward_subset_subsumed:            93
% 19.29/3.01  res_backward_subset_subsumed:           0
% 19.29/3.01  res_forward_subsumed:                   0
% 19.29/3.01  res_backward_subsumed:                  0
% 19.29/3.01  res_forward_subsumption_resolution:     0
% 19.29/3.01  res_backward_subsumption_resolution:    0
% 19.29/3.01  res_clause_to_clause_subsumption:       13868
% 19.29/3.01  res_orphan_elimination:                 0
% 19.29/3.01  res_tautology_del:                      428
% 19.29/3.01  res_num_eq_res_simplified:              0
% 19.29/3.01  res_num_sel_changes:                    0
% 19.29/3.01  res_moves_from_active_to_pass:          0
% 19.29/3.01  
% 19.29/3.01  ------ Superposition
% 19.29/3.01  
% 19.29/3.01  sup_time_total:                         0.
% 19.29/3.01  sup_time_generating:                    0.
% 19.29/3.01  sup_time_sim_full:                      0.
% 19.29/3.01  sup_time_sim_immed:                     0.
% 19.29/3.01  
% 19.29/3.01  sup_num_of_clauses:                     6859
% 19.29/3.01  sup_num_in_active:                      369
% 19.29/3.01  sup_num_in_passive:                     6490
% 19.29/3.01  sup_num_of_loops:                       375
% 19.29/3.01  sup_fw_superposition:                   4864
% 19.29/3.01  sup_bw_superposition:                   2777
% 19.29/3.01  sup_immediate_simplified:               327
% 19.29/3.01  sup_given_eliminated:                   0
% 19.29/3.01  comparisons_done:                       0
% 19.29/3.01  comparisons_avoided:                    93
% 19.29/3.01  
% 19.29/3.01  ------ Simplifications
% 19.29/3.01  
% 19.29/3.01  
% 19.29/3.01  sim_fw_subset_subsumed:                 153
% 19.29/3.01  sim_bw_subset_subsumed:                 34
% 19.29/3.01  sim_fw_subsumed:                        39
% 19.29/3.01  sim_bw_subsumed:                        5
% 19.29/3.01  sim_fw_subsumption_res:                 0
% 19.29/3.01  sim_bw_subsumption_res:                 0
% 19.29/3.01  sim_tautology_del:                      17
% 19.29/3.01  sim_eq_tautology_del:                   507
% 19.29/3.01  sim_eq_res_simp:                        4
% 19.29/3.01  sim_fw_demodulated:                     3
% 19.29/3.01  sim_bw_demodulated:                     6
% 19.29/3.01  sim_light_normalised:                   155
% 19.29/3.01  sim_joinable_taut:                      0
% 19.29/3.01  sim_joinable_simp:                      0
% 19.29/3.01  sim_ac_normalised:                      0
% 19.29/3.01  sim_smt_subsumption:                    0
% 19.29/3.01  
%------------------------------------------------------------------------------
