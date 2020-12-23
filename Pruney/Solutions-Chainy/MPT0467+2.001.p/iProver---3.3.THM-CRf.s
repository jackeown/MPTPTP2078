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
% DateTime   : Thu Dec  3 11:43:38 EST 2020

% Result     : Theorem 35.15s
% Output     : CNFRefutation 35.15s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 201 expanded)
%              Number of clauses        :   32 (  40 expanded)
%              Number of leaves         :    9 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  339 (1508 expanded)
%              Number of equality atoms :   33 ( 157 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   17 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
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
    inference(rectify,[],[f21])).

fof(f25,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f40,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f43,plain,(
    ! [X2,X0,X5,X1] :
      ( k5_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f39,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(k5_relat_1(X0,X1),X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(k5_relat_1(X0,X1),X2)
          & v1_relat_1(X2) )
     => ( k5_relat_1(X0,k5_relat_1(X1,sK8)) != k5_relat_1(k5_relat_1(X0,X1),sK8)
        & v1_relat_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(k5_relat_1(X0,X1),X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( k5_relat_1(X0,k5_relat_1(sK7,X2)) != k5_relat_1(k5_relat_1(X0,sK7),X2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k5_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(k5_relat_1(X0,X1),X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(k5_relat_1(sK6,X1),X2) != k5_relat_1(sK6,k5_relat_1(X1,X2))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k5_relat_1(k5_relat_1(sK6,sK7),sK8) != k5_relat_1(sK6,k5_relat_1(sK7,sK8))
    & v1_relat_1(sK8)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f14,f29,f28,f27])).

fof(f48,plain,(
    k5_relat_1(k5_relat_1(sK6,sK7),sK8) != k5_relat_1(sK6,k5_relat_1(sK7,sK8)) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X3,X0),X4)
    | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_34291,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),X1)
    | r2_hidden(k4_tarski(X0,sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(X1,k5_relat_1(sK7,sK8)))
    | ~ r2_hidden(k4_tarski(sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(X1,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_176091,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK6)
    | r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_34291])).

cnf(c_4757,plain,
    ( r2_hidden(k4_tarski(X0,sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),k5_relat_1(X1,sK7))
    | ~ r2_hidden(k4_tarski(X0,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),X1)
    | ~ r2_hidden(k4_tarski(sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK7)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(X1,sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_27210,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK7)
    | r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),k5_relat_1(sK6,sK7))
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK6)
    | ~ v1_relat_1(k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_4757])).

cnf(c_2985,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),X1)
    | r2_hidden(k4_tarski(X0,sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(X1,sK8))
    | ~ r2_hidden(k4_tarski(sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k5_relat_1(X1,sK8))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4077,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK7)
    | r2_hidden(k4_tarski(X0,sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
    | ~ r2_hidden(k4_tarski(sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
    | ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2985])).

cnf(c_13482,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK7)
    | r2_hidden(k4_tarski(sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
    | ~ r2_hidden(k4_tarski(sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
    | ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4077])).

cnf(c_7,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK3(X1,X2,X3)),X2)
    | ~ r2_hidden(k4_tarski(sK2(X1,X2,X3),X0),X1)
    | ~ r2_hidden(k4_tarski(sK2(X1,X2,X3),sK3(X1,X2,X3)),X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X1,X2) = X3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_738,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),X0),k5_relat_1(sK6,sK7))
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK8)
    | k5_relat_1(k5_relat_1(sK6,sK7),sK8) = k5_relat_1(sK6,k5_relat_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4787,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),k5_relat_1(sK6,sK7))
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK8)
    | k5_relat_1(k5_relat_1(sK6,sK7),sK8) = k5_relat_1(sK6,k5_relat_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_12,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3014,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK6)
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3015,plain,
    ( r2_hidden(k4_tarski(sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK7)
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2655,plain,
    ( r2_hidden(k4_tarski(sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK7)
    | ~ r2_hidden(k4_tarski(sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2656,plain,
    ( r2_hidden(k4_tarski(sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
    | ~ r2_hidden(k4_tarski(sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1357,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK6)
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1358,plain,
    ( r2_hidden(k4_tarski(sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
    | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_976,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_822,plain,
    ( ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_801,plain,
    ( v1_relat_1(k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_731,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,sK7))
    | r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK8)
    | k5_relat_1(k5_relat_1(sK6,sK7),sK8) = k5_relat_1(sK6,k5_relat_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_728,plain,
    ( r2_hidden(k4_tarski(sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
    | r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
    | ~ v1_relat_1(k5_relat_1(sK6,sK7))
    | ~ v1_relat_1(sK8)
    | k5_relat_1(k5_relat_1(sK6,sK7),sK8) = k5_relat_1(sK6,k5_relat_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_14,negated_conjecture,
    ( k5_relat_1(k5_relat_1(sK6,sK7),sK8) != k5_relat_1(sK6,k5_relat_1(sK7,sK8)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_176091,c_27210,c_13482,c_4787,c_3014,c_3015,c_2655,c_2656,c_1357,c_1358,c_976,c_822,c_801,c_731,c_728,c_14,c_15,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 35.15/5.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.15/5.01  
% 35.15/5.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.15/5.01  
% 35.15/5.01  ------  iProver source info
% 35.15/5.01  
% 35.15/5.01  git: date: 2020-06-30 10:37:57 +0100
% 35.15/5.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.15/5.01  git: non_committed_changes: false
% 35.15/5.01  git: last_make_outside_of_git: false
% 35.15/5.01  
% 35.15/5.01  ------ 
% 35.15/5.01  
% 35.15/5.01  ------ Input Options
% 35.15/5.01  
% 35.15/5.01  --out_options                           all
% 35.15/5.01  --tptp_safe_out                         true
% 35.15/5.01  --problem_path                          ""
% 35.15/5.01  --include_path                          ""
% 35.15/5.01  --clausifier                            res/vclausify_rel
% 35.15/5.01  --clausifier_options                    --mode clausify
% 35.15/5.01  --stdin                                 false
% 35.15/5.01  --stats_out                             all
% 35.15/5.01  
% 35.15/5.01  ------ General Options
% 35.15/5.01  
% 35.15/5.01  --fof                                   false
% 35.15/5.01  --time_out_real                         305.
% 35.15/5.01  --time_out_virtual                      -1.
% 35.15/5.01  --symbol_type_check                     false
% 35.15/5.01  --clausify_out                          false
% 35.15/5.01  --sig_cnt_out                           false
% 35.15/5.01  --trig_cnt_out                          false
% 35.15/5.01  --trig_cnt_out_tolerance                1.
% 35.15/5.01  --trig_cnt_out_sk_spl                   false
% 35.15/5.01  --abstr_cl_out                          false
% 35.15/5.01  
% 35.15/5.01  ------ Global Options
% 35.15/5.01  
% 35.15/5.01  --schedule                              default
% 35.15/5.01  --add_important_lit                     false
% 35.15/5.01  --prop_solver_per_cl                    1000
% 35.15/5.01  --min_unsat_core                        false
% 35.15/5.01  --soft_assumptions                      false
% 35.15/5.01  --soft_lemma_size                       3
% 35.15/5.01  --prop_impl_unit_size                   0
% 35.15/5.01  --prop_impl_unit                        []
% 35.15/5.01  --share_sel_clauses                     true
% 35.15/5.01  --reset_solvers                         false
% 35.15/5.01  --bc_imp_inh                            [conj_cone]
% 35.15/5.01  --conj_cone_tolerance                   3.
% 35.15/5.01  --extra_neg_conj                        none
% 35.15/5.01  --large_theory_mode                     true
% 35.15/5.01  --prolific_symb_bound                   200
% 35.15/5.01  --lt_threshold                          2000
% 35.15/5.01  --clause_weak_htbl                      true
% 35.15/5.01  --gc_record_bc_elim                     false
% 35.15/5.01  
% 35.15/5.01  ------ Preprocessing Options
% 35.15/5.01  
% 35.15/5.01  --preprocessing_flag                    true
% 35.15/5.01  --time_out_prep_mult                    0.1
% 35.15/5.01  --splitting_mode                        input
% 35.15/5.01  --splitting_grd                         true
% 35.15/5.01  --splitting_cvd                         false
% 35.15/5.01  --splitting_cvd_svl                     false
% 35.15/5.01  --splitting_nvd                         32
% 35.15/5.01  --sub_typing                            true
% 35.15/5.01  --prep_gs_sim                           true
% 35.15/5.01  --prep_unflatten                        true
% 35.15/5.01  --prep_res_sim                          true
% 35.15/5.01  --prep_upred                            true
% 35.15/5.01  --prep_sem_filter                       exhaustive
% 35.15/5.01  --prep_sem_filter_out                   false
% 35.15/5.01  --pred_elim                             true
% 35.15/5.01  --res_sim_input                         true
% 35.15/5.01  --eq_ax_congr_red                       true
% 35.15/5.01  --pure_diseq_elim                       true
% 35.15/5.01  --brand_transform                       false
% 35.15/5.01  --non_eq_to_eq                          false
% 35.15/5.01  --prep_def_merge                        true
% 35.15/5.01  --prep_def_merge_prop_impl              false
% 35.15/5.01  --prep_def_merge_mbd                    true
% 35.15/5.01  --prep_def_merge_tr_red                 false
% 35.15/5.01  --prep_def_merge_tr_cl                  false
% 35.15/5.01  --smt_preprocessing                     true
% 35.15/5.01  --smt_ac_axioms                         fast
% 35.15/5.01  --preprocessed_out                      false
% 35.15/5.01  --preprocessed_stats                    false
% 35.15/5.01  
% 35.15/5.01  ------ Abstraction refinement Options
% 35.15/5.01  
% 35.15/5.01  --abstr_ref                             []
% 35.15/5.01  --abstr_ref_prep                        false
% 35.15/5.01  --abstr_ref_until_sat                   false
% 35.15/5.01  --abstr_ref_sig_restrict                funpre
% 35.15/5.01  --abstr_ref_af_restrict_to_split_sk     false
% 35.15/5.01  --abstr_ref_under                       []
% 35.15/5.01  
% 35.15/5.01  ------ SAT Options
% 35.15/5.01  
% 35.15/5.01  --sat_mode                              false
% 35.15/5.01  --sat_fm_restart_options                ""
% 35.15/5.01  --sat_gr_def                            false
% 35.15/5.01  --sat_epr_types                         true
% 35.15/5.01  --sat_non_cyclic_types                  false
% 35.15/5.01  --sat_finite_models                     false
% 35.15/5.01  --sat_fm_lemmas                         false
% 35.15/5.01  --sat_fm_prep                           false
% 35.15/5.01  --sat_fm_uc_incr                        true
% 35.15/5.01  --sat_out_model                         small
% 35.15/5.01  --sat_out_clauses                       false
% 35.15/5.01  
% 35.15/5.01  ------ QBF Options
% 35.15/5.01  
% 35.15/5.01  --qbf_mode                              false
% 35.15/5.01  --qbf_elim_univ                         false
% 35.15/5.01  --qbf_dom_inst                          none
% 35.15/5.01  --qbf_dom_pre_inst                      false
% 35.15/5.01  --qbf_sk_in                             false
% 35.15/5.01  --qbf_pred_elim                         true
% 35.15/5.01  --qbf_split                             512
% 35.15/5.01  
% 35.15/5.01  ------ BMC1 Options
% 35.15/5.01  
% 35.15/5.01  --bmc1_incremental                      false
% 35.15/5.01  --bmc1_axioms                           reachable_all
% 35.15/5.01  --bmc1_min_bound                        0
% 35.15/5.01  --bmc1_max_bound                        -1
% 35.15/5.01  --bmc1_max_bound_default                -1
% 35.15/5.01  --bmc1_symbol_reachability              true
% 35.15/5.01  --bmc1_property_lemmas                  false
% 35.15/5.01  --bmc1_k_induction                      false
% 35.15/5.01  --bmc1_non_equiv_states                 false
% 35.15/5.01  --bmc1_deadlock                         false
% 35.15/5.01  --bmc1_ucm                              false
% 35.15/5.01  --bmc1_add_unsat_core                   none
% 35.15/5.01  --bmc1_unsat_core_children              false
% 35.15/5.01  --bmc1_unsat_core_extrapolate_axioms    false
% 35.15/5.01  --bmc1_out_stat                         full
% 35.15/5.01  --bmc1_ground_init                      false
% 35.15/5.01  --bmc1_pre_inst_next_state              false
% 35.15/5.01  --bmc1_pre_inst_state                   false
% 35.15/5.01  --bmc1_pre_inst_reach_state             false
% 35.15/5.01  --bmc1_out_unsat_core                   false
% 35.15/5.01  --bmc1_aig_witness_out                  false
% 35.15/5.01  --bmc1_verbose                          false
% 35.15/5.01  --bmc1_dump_clauses_tptp                false
% 35.15/5.01  --bmc1_dump_unsat_core_tptp             false
% 35.15/5.01  --bmc1_dump_file                        -
% 35.15/5.01  --bmc1_ucm_expand_uc_limit              128
% 35.15/5.01  --bmc1_ucm_n_expand_iterations          6
% 35.15/5.01  --bmc1_ucm_extend_mode                  1
% 35.15/5.01  --bmc1_ucm_init_mode                    2
% 35.15/5.01  --bmc1_ucm_cone_mode                    none
% 35.15/5.01  --bmc1_ucm_reduced_relation_type        0
% 35.15/5.01  --bmc1_ucm_relax_model                  4
% 35.15/5.01  --bmc1_ucm_full_tr_after_sat            true
% 35.15/5.01  --bmc1_ucm_expand_neg_assumptions       false
% 35.15/5.01  --bmc1_ucm_layered_model                none
% 35.15/5.01  --bmc1_ucm_max_lemma_size               10
% 35.15/5.01  
% 35.15/5.01  ------ AIG Options
% 35.15/5.01  
% 35.15/5.01  --aig_mode                              false
% 35.15/5.01  
% 35.15/5.01  ------ Instantiation Options
% 35.15/5.01  
% 35.15/5.01  --instantiation_flag                    true
% 35.15/5.01  --inst_sos_flag                         false
% 35.15/5.01  --inst_sos_phase                        true
% 35.15/5.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.15/5.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.15/5.01  --inst_lit_sel_side                     num_symb
% 35.15/5.01  --inst_solver_per_active                1400
% 35.15/5.01  --inst_solver_calls_frac                1.
% 35.15/5.01  --inst_passive_queue_type               priority_queues
% 35.15/5.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.15/5.01  --inst_passive_queues_freq              [25;2]
% 35.15/5.01  --inst_dismatching                      true
% 35.15/5.01  --inst_eager_unprocessed_to_passive     true
% 35.15/5.01  --inst_prop_sim_given                   true
% 35.15/5.01  --inst_prop_sim_new                     false
% 35.15/5.01  --inst_subs_new                         false
% 35.15/5.01  --inst_eq_res_simp                      false
% 35.15/5.01  --inst_subs_given                       false
% 35.15/5.01  --inst_orphan_elimination               true
% 35.15/5.01  --inst_learning_loop_flag               true
% 35.15/5.01  --inst_learning_start                   3000
% 35.15/5.01  --inst_learning_factor                  2
% 35.15/5.01  --inst_start_prop_sim_after_learn       3
% 35.15/5.01  --inst_sel_renew                        solver
% 35.15/5.01  --inst_lit_activity_flag                true
% 35.15/5.01  --inst_restr_to_given                   false
% 35.15/5.01  --inst_activity_threshold               500
% 35.15/5.01  --inst_out_proof                        true
% 35.15/5.01  
% 35.15/5.01  ------ Resolution Options
% 35.15/5.01  
% 35.15/5.01  --resolution_flag                       true
% 35.15/5.01  --res_lit_sel                           adaptive
% 35.15/5.01  --res_lit_sel_side                      none
% 35.15/5.01  --res_ordering                          kbo
% 35.15/5.01  --res_to_prop_solver                    active
% 35.15/5.01  --res_prop_simpl_new                    false
% 35.15/5.01  --res_prop_simpl_given                  true
% 35.15/5.01  --res_passive_queue_type                priority_queues
% 35.15/5.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.15/5.01  --res_passive_queues_freq               [15;5]
% 35.15/5.01  --res_forward_subs                      full
% 35.15/5.01  --res_backward_subs                     full
% 35.15/5.01  --res_forward_subs_resolution           true
% 35.15/5.01  --res_backward_subs_resolution          true
% 35.15/5.01  --res_orphan_elimination                true
% 35.15/5.01  --res_time_limit                        2.
% 35.15/5.01  --res_out_proof                         true
% 35.15/5.01  
% 35.15/5.01  ------ Superposition Options
% 35.15/5.01  
% 35.15/5.01  --superposition_flag                    true
% 35.15/5.01  --sup_passive_queue_type                priority_queues
% 35.15/5.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.15/5.01  --sup_passive_queues_freq               [8;1;4]
% 35.15/5.01  --demod_completeness_check              fast
% 35.15/5.01  --demod_use_ground                      true
% 35.15/5.01  --sup_to_prop_solver                    passive
% 35.15/5.01  --sup_prop_simpl_new                    true
% 35.15/5.01  --sup_prop_simpl_given                  true
% 35.15/5.01  --sup_fun_splitting                     false
% 35.15/5.01  --sup_smt_interval                      50000
% 35.15/5.01  
% 35.15/5.01  ------ Superposition Simplification Setup
% 35.15/5.01  
% 35.15/5.01  --sup_indices_passive                   []
% 35.15/5.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.15/5.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.15/5.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.15/5.01  --sup_full_triv                         [TrivRules;PropSubs]
% 35.15/5.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.15/5.01  --sup_full_bw                           [BwDemod]
% 35.15/5.01  --sup_immed_triv                        [TrivRules]
% 35.15/5.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.15/5.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.15/5.01  --sup_immed_bw_main                     []
% 35.15/5.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.15/5.01  --sup_input_triv                        [Unflattening;TrivRules]
% 35.15/5.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.15/5.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.15/5.01  
% 35.15/5.01  ------ Combination Options
% 35.15/5.01  
% 35.15/5.01  --comb_res_mult                         3
% 35.15/5.01  --comb_sup_mult                         2
% 35.15/5.01  --comb_inst_mult                        10
% 35.15/5.01  
% 35.15/5.01  ------ Debug Options
% 35.15/5.01  
% 35.15/5.01  --dbg_backtrace                         false
% 35.15/5.01  --dbg_dump_prop_clauses                 false
% 35.15/5.01  --dbg_dump_prop_clauses_file            -
% 35.15/5.01  --dbg_out_stat                          false
% 35.15/5.01  ------ Parsing...
% 35.15/5.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.15/5.01  
% 35.15/5.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.15/5.01  
% 35.15/5.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.15/5.01  
% 35.15/5.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.15/5.01  ------ Proving...
% 35.15/5.01  ------ Problem Properties 
% 35.15/5.01  
% 35.15/5.01  
% 35.15/5.01  clauses                                 17
% 35.15/5.01  conjectures                             4
% 35.15/5.01  EPR                                     6
% 35.15/5.01  Horn                                    14
% 35.15/5.01  unary                                   5
% 35.15/5.01  binary                                  0
% 35.15/5.01  lits                                    59
% 35.15/5.01  lits eq                                 5
% 35.15/5.01  fd_pure                                 0
% 35.15/5.01  fd_pseudo                               0
% 35.15/5.01  fd_cond                                 0
% 35.15/5.01  fd_pseudo_cond                          4
% 35.15/5.01  AC symbols                              0
% 35.15/5.01  
% 35.15/5.01  ------ Schedule dynamic 5 is on 
% 35.15/5.01  
% 35.15/5.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.15/5.01  
% 35.15/5.01  
% 35.15/5.01  ------ 
% 35.15/5.01  Current options:
% 35.15/5.01  ------ 
% 35.15/5.01  
% 35.15/5.01  ------ Input Options
% 35.15/5.01  
% 35.15/5.01  --out_options                           all
% 35.15/5.01  --tptp_safe_out                         true
% 35.15/5.01  --problem_path                          ""
% 35.15/5.01  --include_path                          ""
% 35.15/5.01  --clausifier                            res/vclausify_rel
% 35.15/5.01  --clausifier_options                    --mode clausify
% 35.15/5.01  --stdin                                 false
% 35.15/5.01  --stats_out                             all
% 35.15/5.01  
% 35.15/5.01  ------ General Options
% 35.15/5.01  
% 35.15/5.01  --fof                                   false
% 35.15/5.01  --time_out_real                         305.
% 35.15/5.01  --time_out_virtual                      -1.
% 35.15/5.01  --symbol_type_check                     false
% 35.15/5.01  --clausify_out                          false
% 35.15/5.01  --sig_cnt_out                           false
% 35.15/5.01  --trig_cnt_out                          false
% 35.15/5.01  --trig_cnt_out_tolerance                1.
% 35.15/5.01  --trig_cnt_out_sk_spl                   false
% 35.15/5.01  --abstr_cl_out                          false
% 35.15/5.01  
% 35.15/5.01  ------ Global Options
% 35.15/5.01  
% 35.15/5.01  --schedule                              default
% 35.15/5.01  --add_important_lit                     false
% 35.15/5.01  --prop_solver_per_cl                    1000
% 35.15/5.01  --min_unsat_core                        false
% 35.15/5.01  --soft_assumptions                      false
% 35.15/5.01  --soft_lemma_size                       3
% 35.15/5.01  --prop_impl_unit_size                   0
% 35.15/5.01  --prop_impl_unit                        []
% 35.15/5.01  --share_sel_clauses                     true
% 35.15/5.01  --reset_solvers                         false
% 35.15/5.01  --bc_imp_inh                            [conj_cone]
% 35.15/5.01  --conj_cone_tolerance                   3.
% 35.15/5.01  --extra_neg_conj                        none
% 35.15/5.01  --large_theory_mode                     true
% 35.15/5.01  --prolific_symb_bound                   200
% 35.15/5.01  --lt_threshold                          2000
% 35.15/5.01  --clause_weak_htbl                      true
% 35.15/5.01  --gc_record_bc_elim                     false
% 35.15/5.01  
% 35.15/5.01  ------ Preprocessing Options
% 35.15/5.01  
% 35.15/5.01  --preprocessing_flag                    true
% 35.15/5.01  --time_out_prep_mult                    0.1
% 35.15/5.01  --splitting_mode                        input
% 35.15/5.01  --splitting_grd                         true
% 35.15/5.01  --splitting_cvd                         false
% 35.15/5.01  --splitting_cvd_svl                     false
% 35.15/5.01  --splitting_nvd                         32
% 35.15/5.01  --sub_typing                            true
% 35.15/5.01  --prep_gs_sim                           true
% 35.15/5.01  --prep_unflatten                        true
% 35.15/5.01  --prep_res_sim                          true
% 35.15/5.01  --prep_upred                            true
% 35.15/5.01  --prep_sem_filter                       exhaustive
% 35.15/5.01  --prep_sem_filter_out                   false
% 35.15/5.01  --pred_elim                             true
% 35.15/5.01  --res_sim_input                         true
% 35.15/5.01  --eq_ax_congr_red                       true
% 35.15/5.01  --pure_diseq_elim                       true
% 35.15/5.01  --brand_transform                       false
% 35.15/5.01  --non_eq_to_eq                          false
% 35.15/5.01  --prep_def_merge                        true
% 35.15/5.01  --prep_def_merge_prop_impl              false
% 35.15/5.01  --prep_def_merge_mbd                    true
% 35.15/5.01  --prep_def_merge_tr_red                 false
% 35.15/5.01  --prep_def_merge_tr_cl                  false
% 35.15/5.01  --smt_preprocessing                     true
% 35.15/5.01  --smt_ac_axioms                         fast
% 35.15/5.01  --preprocessed_out                      false
% 35.15/5.01  --preprocessed_stats                    false
% 35.15/5.01  
% 35.15/5.01  ------ Abstraction refinement Options
% 35.15/5.01  
% 35.15/5.01  --abstr_ref                             []
% 35.15/5.01  --abstr_ref_prep                        false
% 35.15/5.01  --abstr_ref_until_sat                   false
% 35.15/5.01  --abstr_ref_sig_restrict                funpre
% 35.15/5.01  --abstr_ref_af_restrict_to_split_sk     false
% 35.15/5.01  --abstr_ref_under                       []
% 35.15/5.01  
% 35.15/5.01  ------ SAT Options
% 35.15/5.01  
% 35.15/5.01  --sat_mode                              false
% 35.15/5.01  --sat_fm_restart_options                ""
% 35.15/5.01  --sat_gr_def                            false
% 35.15/5.01  --sat_epr_types                         true
% 35.15/5.01  --sat_non_cyclic_types                  false
% 35.15/5.01  --sat_finite_models                     false
% 35.15/5.01  --sat_fm_lemmas                         false
% 35.15/5.01  --sat_fm_prep                           false
% 35.15/5.01  --sat_fm_uc_incr                        true
% 35.15/5.01  --sat_out_model                         small
% 35.15/5.01  --sat_out_clauses                       false
% 35.15/5.01  
% 35.15/5.01  ------ QBF Options
% 35.15/5.01  
% 35.15/5.01  --qbf_mode                              false
% 35.15/5.01  --qbf_elim_univ                         false
% 35.15/5.01  --qbf_dom_inst                          none
% 35.15/5.01  --qbf_dom_pre_inst                      false
% 35.15/5.01  --qbf_sk_in                             false
% 35.15/5.01  --qbf_pred_elim                         true
% 35.15/5.01  --qbf_split                             512
% 35.15/5.01  
% 35.15/5.01  ------ BMC1 Options
% 35.15/5.01  
% 35.15/5.01  --bmc1_incremental                      false
% 35.15/5.01  --bmc1_axioms                           reachable_all
% 35.15/5.01  --bmc1_min_bound                        0
% 35.15/5.01  --bmc1_max_bound                        -1
% 35.15/5.01  --bmc1_max_bound_default                -1
% 35.15/5.01  --bmc1_symbol_reachability              true
% 35.15/5.01  --bmc1_property_lemmas                  false
% 35.15/5.01  --bmc1_k_induction                      false
% 35.15/5.01  --bmc1_non_equiv_states                 false
% 35.15/5.01  --bmc1_deadlock                         false
% 35.15/5.01  --bmc1_ucm                              false
% 35.15/5.01  --bmc1_add_unsat_core                   none
% 35.15/5.01  --bmc1_unsat_core_children              false
% 35.15/5.01  --bmc1_unsat_core_extrapolate_axioms    false
% 35.15/5.01  --bmc1_out_stat                         full
% 35.15/5.01  --bmc1_ground_init                      false
% 35.15/5.01  --bmc1_pre_inst_next_state              false
% 35.15/5.01  --bmc1_pre_inst_state                   false
% 35.15/5.01  --bmc1_pre_inst_reach_state             false
% 35.15/5.01  --bmc1_out_unsat_core                   false
% 35.15/5.01  --bmc1_aig_witness_out                  false
% 35.15/5.01  --bmc1_verbose                          false
% 35.15/5.01  --bmc1_dump_clauses_tptp                false
% 35.15/5.01  --bmc1_dump_unsat_core_tptp             false
% 35.15/5.01  --bmc1_dump_file                        -
% 35.15/5.01  --bmc1_ucm_expand_uc_limit              128
% 35.15/5.01  --bmc1_ucm_n_expand_iterations          6
% 35.15/5.01  --bmc1_ucm_extend_mode                  1
% 35.15/5.01  --bmc1_ucm_init_mode                    2
% 35.15/5.01  --bmc1_ucm_cone_mode                    none
% 35.15/5.01  --bmc1_ucm_reduced_relation_type        0
% 35.15/5.01  --bmc1_ucm_relax_model                  4
% 35.15/5.01  --bmc1_ucm_full_tr_after_sat            true
% 35.15/5.01  --bmc1_ucm_expand_neg_assumptions       false
% 35.15/5.01  --bmc1_ucm_layered_model                none
% 35.15/5.01  --bmc1_ucm_max_lemma_size               10
% 35.15/5.01  
% 35.15/5.01  ------ AIG Options
% 35.15/5.01  
% 35.15/5.01  --aig_mode                              false
% 35.15/5.01  
% 35.15/5.01  ------ Instantiation Options
% 35.15/5.01  
% 35.15/5.01  --instantiation_flag                    true
% 35.15/5.01  --inst_sos_flag                         false
% 35.15/5.01  --inst_sos_phase                        true
% 35.15/5.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.15/5.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.15/5.01  --inst_lit_sel_side                     none
% 35.15/5.01  --inst_solver_per_active                1400
% 35.15/5.01  --inst_solver_calls_frac                1.
% 35.15/5.01  --inst_passive_queue_type               priority_queues
% 35.15/5.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.15/5.01  --inst_passive_queues_freq              [25;2]
% 35.15/5.01  --inst_dismatching                      true
% 35.15/5.01  --inst_eager_unprocessed_to_passive     true
% 35.15/5.01  --inst_prop_sim_given                   true
% 35.15/5.01  --inst_prop_sim_new                     false
% 35.15/5.01  --inst_subs_new                         false
% 35.15/5.01  --inst_eq_res_simp                      false
% 35.15/5.01  --inst_subs_given                       false
% 35.15/5.01  --inst_orphan_elimination               true
% 35.15/5.01  --inst_learning_loop_flag               true
% 35.15/5.01  --inst_learning_start                   3000
% 35.15/5.01  --inst_learning_factor                  2
% 35.15/5.01  --inst_start_prop_sim_after_learn       3
% 35.15/5.01  --inst_sel_renew                        solver
% 35.15/5.01  --inst_lit_activity_flag                true
% 35.15/5.01  --inst_restr_to_given                   false
% 35.15/5.01  --inst_activity_threshold               500
% 35.15/5.01  --inst_out_proof                        true
% 35.15/5.01  
% 35.15/5.01  ------ Resolution Options
% 35.15/5.01  
% 35.15/5.01  --resolution_flag                       false
% 35.15/5.01  --res_lit_sel                           adaptive
% 35.15/5.01  --res_lit_sel_side                      none
% 35.15/5.01  --res_ordering                          kbo
% 35.15/5.01  --res_to_prop_solver                    active
% 35.15/5.01  --res_prop_simpl_new                    false
% 35.15/5.01  --res_prop_simpl_given                  true
% 35.15/5.01  --res_passive_queue_type                priority_queues
% 35.15/5.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.15/5.01  --res_passive_queues_freq               [15;5]
% 35.15/5.01  --res_forward_subs                      full
% 35.15/5.01  --res_backward_subs                     full
% 35.15/5.01  --res_forward_subs_resolution           true
% 35.15/5.01  --res_backward_subs_resolution          true
% 35.15/5.01  --res_orphan_elimination                true
% 35.15/5.01  --res_time_limit                        2.
% 35.15/5.01  --res_out_proof                         true
% 35.15/5.01  
% 35.15/5.01  ------ Superposition Options
% 35.15/5.01  
% 35.15/5.01  --superposition_flag                    true
% 35.15/5.01  --sup_passive_queue_type                priority_queues
% 35.15/5.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.15/5.01  --sup_passive_queues_freq               [8;1;4]
% 35.15/5.01  --demod_completeness_check              fast
% 35.15/5.01  --demod_use_ground                      true
% 35.15/5.01  --sup_to_prop_solver                    passive
% 35.15/5.01  --sup_prop_simpl_new                    true
% 35.15/5.01  --sup_prop_simpl_given                  true
% 35.15/5.01  --sup_fun_splitting                     false
% 35.15/5.01  --sup_smt_interval                      50000
% 35.15/5.01  
% 35.15/5.01  ------ Superposition Simplification Setup
% 35.15/5.01  
% 35.15/5.01  --sup_indices_passive                   []
% 35.15/5.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.15/5.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.15/5.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.15/5.01  --sup_full_triv                         [TrivRules;PropSubs]
% 35.15/5.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.15/5.01  --sup_full_bw                           [BwDemod]
% 35.15/5.01  --sup_immed_triv                        [TrivRules]
% 35.15/5.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.15/5.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.15/5.01  --sup_immed_bw_main                     []
% 35.15/5.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.15/5.01  --sup_input_triv                        [Unflattening;TrivRules]
% 35.15/5.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.15/5.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.15/5.01  
% 35.15/5.01  ------ Combination Options
% 35.15/5.01  
% 35.15/5.01  --comb_res_mult                         3
% 35.15/5.01  --comb_sup_mult                         2
% 35.15/5.01  --comb_inst_mult                        10
% 35.15/5.01  
% 35.15/5.01  ------ Debug Options
% 35.15/5.01  
% 35.15/5.01  --dbg_backtrace                         false
% 35.15/5.01  --dbg_dump_prop_clauses                 false
% 35.15/5.01  --dbg_dump_prop_clauses_file            -
% 35.15/5.01  --dbg_out_stat                          false
% 35.15/5.01  
% 35.15/5.01  
% 35.15/5.01  
% 35.15/5.01  
% 35.15/5.01  ------ Proving...
% 35.15/5.01  
% 35.15/5.01  
% 35.15/5.01  % SZS status Theorem for theBenchmark.p
% 35.15/5.01  
% 35.15/5.01  % SZS output start CNFRefutation for theBenchmark.p
% 35.15/5.01  
% 35.15/5.01  fof(f4,axiom,(
% 35.15/5.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 35.15/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.15/5.01  
% 35.15/5.01  fof(f11,plain,(
% 35.15/5.01    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.15/5.01    inference(ennf_transformation,[],[f4])).
% 35.15/5.01  
% 35.15/5.01  fof(f21,plain,(
% 35.15/5.01    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.15/5.01    inference(nnf_transformation,[],[f11])).
% 35.15/5.01  
% 35.15/5.01  fof(f22,plain,(
% 35.15/5.01    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.15/5.01    inference(rectify,[],[f21])).
% 35.15/5.01  
% 35.15/5.01  fof(f25,plain,(
% 35.15/5.01    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 35.15/5.01    introduced(choice_axiom,[])).
% 35.15/5.01  
% 35.15/5.01  fof(f24,plain,(
% 35.15/5.01    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 35.15/5.01    introduced(choice_axiom,[])).
% 35.15/5.01  
% 35.15/5.01  fof(f23,plain,(
% 35.15/5.01    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 35.15/5.01    introduced(choice_axiom,[])).
% 35.15/5.01  
% 35.15/5.01  fof(f26,plain,(
% 35.15/5.01    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.15/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 35.15/5.01  
% 35.15/5.01  fof(f40,plain,(
% 35.15/5.01    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.15/5.01    inference(cnf_transformation,[],[f26])).
% 35.15/5.01  
% 35.15/5.01  fof(f51,plain,(
% 35.15/5.01    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.15/5.01    inference(equality_resolution,[],[f40])).
% 35.15/5.01  
% 35.15/5.01  fof(f43,plain,(
% 35.15/5.01    ( ! [X2,X0,X5,X1] : (k5_relat_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.15/5.01    inference(cnf_transformation,[],[f26])).
% 35.15/5.01  
% 35.15/5.01  fof(f38,plain,(
% 35.15/5.01    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.15/5.01    inference(cnf_transformation,[],[f26])).
% 35.15/5.01  
% 35.15/5.01  fof(f53,plain,(
% 35.15/5.01    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.15/5.01    inference(equality_resolution,[],[f38])).
% 35.15/5.01  
% 35.15/5.01  fof(f39,plain,(
% 35.15/5.01    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.15/5.01    inference(cnf_transformation,[],[f26])).
% 35.15/5.01  
% 35.15/5.01  fof(f52,plain,(
% 35.15/5.01    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.15/5.01    inference(equality_resolution,[],[f39])).
% 35.15/5.01  
% 35.15/5.01  fof(f5,axiom,(
% 35.15/5.01    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 35.15/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.15/5.01  
% 35.15/5.01  fof(f12,plain,(
% 35.15/5.01    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 35.15/5.01    inference(ennf_transformation,[],[f5])).
% 35.15/5.01  
% 35.15/5.01  fof(f13,plain,(
% 35.15/5.01    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 35.15/5.01    inference(flattening,[],[f12])).
% 35.15/5.01  
% 35.15/5.01  fof(f44,plain,(
% 35.15/5.01    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.15/5.01    inference(cnf_transformation,[],[f13])).
% 35.15/5.01  
% 35.15/5.01  fof(f41,plain,(
% 35.15/5.01    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.15/5.01    inference(cnf_transformation,[],[f26])).
% 35.15/5.01  
% 35.15/5.01  fof(f42,plain,(
% 35.15/5.01    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.15/5.01    inference(cnf_transformation,[],[f26])).
% 35.15/5.01  
% 35.15/5.01  fof(f6,conjecture,(
% 35.15/5.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 35.15/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.15/5.01  
% 35.15/5.01  fof(f7,negated_conjecture,(
% 35.15/5.01    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 35.15/5.01    inference(negated_conjecture,[],[f6])).
% 35.15/5.01  
% 35.15/5.01  fof(f14,plain,(
% 35.15/5.01    ? [X0] : (? [X1] : (? [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(k5_relat_1(X0,X1),X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 35.15/5.01    inference(ennf_transformation,[],[f7])).
% 35.15/5.01  
% 35.15/5.01  fof(f29,plain,(
% 35.15/5.01    ( ! [X0,X1] : (? [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(k5_relat_1(X0,X1),X2) & v1_relat_1(X2)) => (k5_relat_1(X0,k5_relat_1(X1,sK8)) != k5_relat_1(k5_relat_1(X0,X1),sK8) & v1_relat_1(sK8))) )),
% 35.15/5.01    introduced(choice_axiom,[])).
% 35.15/5.01  
% 35.15/5.01  fof(f28,plain,(
% 35.15/5.01    ( ! [X0] : (? [X1] : (? [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(k5_relat_1(X0,X1),X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (k5_relat_1(X0,k5_relat_1(sK7,X2)) != k5_relat_1(k5_relat_1(X0,sK7),X2) & v1_relat_1(X2)) & v1_relat_1(sK7))) )),
% 35.15/5.01    introduced(choice_axiom,[])).
% 35.15/5.01  
% 35.15/5.01  fof(f27,plain,(
% 35.15/5.01    ? [X0] : (? [X1] : (? [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(k5_relat_1(X0,X1),X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k5_relat_1(k5_relat_1(sK6,X1),X2) != k5_relat_1(sK6,k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK6))),
% 35.15/5.01    introduced(choice_axiom,[])).
% 35.15/5.01  
% 35.15/5.01  fof(f30,plain,(
% 35.15/5.01    ((k5_relat_1(k5_relat_1(sK6,sK7),sK8) != k5_relat_1(sK6,k5_relat_1(sK7,sK8)) & v1_relat_1(sK8)) & v1_relat_1(sK7)) & v1_relat_1(sK6)),
% 35.15/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f14,f29,f28,f27])).
% 35.15/5.01  
% 35.15/5.01  fof(f48,plain,(
% 35.15/5.01    k5_relat_1(k5_relat_1(sK6,sK7),sK8) != k5_relat_1(sK6,k5_relat_1(sK7,sK8))),
% 35.15/5.01    inference(cnf_transformation,[],[f30])).
% 35.15/5.01  
% 35.15/5.01  fof(f47,plain,(
% 35.15/5.01    v1_relat_1(sK8)),
% 35.15/5.01    inference(cnf_transformation,[],[f30])).
% 35.15/5.01  
% 35.15/5.01  fof(f46,plain,(
% 35.15/5.01    v1_relat_1(sK7)),
% 35.15/5.01    inference(cnf_transformation,[],[f30])).
% 35.15/5.01  
% 35.15/5.01  fof(f45,plain,(
% 35.15/5.01    v1_relat_1(sK6)),
% 35.15/5.01    inference(cnf_transformation,[],[f30])).
% 35.15/5.01  
% 35.15/5.01  cnf(c_10,plain,
% 35.15/5.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 35.15/5.01      | ~ r2_hidden(k4_tarski(X3,X0),X4)
% 35.15/5.01      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,X2))
% 35.15/5.01      | ~ v1_relat_1(X4)
% 35.15/5.01      | ~ v1_relat_1(X2)
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(X4,X2)) ),
% 35.15/5.01      inference(cnf_transformation,[],[f51]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_34291,plain,
% 35.15/5.01      ( ~ r2_hidden(k4_tarski(X0,sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),X1)
% 35.15/5.01      | r2_hidden(k4_tarski(X0,sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(X1,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ v1_relat_1(X1)
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(X1,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK7,sK8)) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_10]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_176091,plain,
% 35.15/5.01      ( ~ r2_hidden(k4_tarski(sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK6)
% 35.15/5.01      | r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(sK6) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_34291]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_4757,plain,
% 35.15/5.01      ( r2_hidden(k4_tarski(X0,sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),k5_relat_1(X1,sK7))
% 35.15/5.01      | ~ r2_hidden(k4_tarski(X0,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),X1)
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK7)
% 35.15/5.01      | ~ v1_relat_1(X1)
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(X1,sK7))
% 35.15/5.01      | ~ v1_relat_1(sK7) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_10]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_27210,plain,
% 35.15/5.01      ( ~ r2_hidden(k4_tarski(sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK7)
% 35.15/5.01      | r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK6)
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ v1_relat_1(sK7)
% 35.15/5.01      | ~ v1_relat_1(sK6) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_4757]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_2985,plain,
% 35.15/5.01      ( ~ r2_hidden(k4_tarski(X0,sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),X1)
% 35.15/5.01      | r2_hidden(k4_tarski(X0,sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(X1,sK8))
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
% 35.15/5.01      | ~ v1_relat_1(X1)
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(X1,sK8))
% 35.15/5.01      | ~ v1_relat_1(sK8) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_10]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_4077,plain,
% 35.15/5.01      ( ~ r2_hidden(k4_tarski(X0,sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK7)
% 35.15/5.01      | r2_hidden(k4_tarski(X0,sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ v1_relat_1(sK8)
% 35.15/5.01      | ~ v1_relat_1(sK7) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_2985]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_13482,plain,
% 35.15/5.01      ( ~ r2_hidden(k4_tarski(sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK7)
% 35.15/5.01      | r2_hidden(k4_tarski(sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ v1_relat_1(sK8)
% 35.15/5.01      | ~ v1_relat_1(sK7) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_4077]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_7,plain,
% 35.15/5.01      ( ~ r2_hidden(k4_tarski(X0,sK3(X1,X2,X3)),X2)
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK2(X1,X2,X3),X0),X1)
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK2(X1,X2,X3),sK3(X1,X2,X3)),X3)
% 35.15/5.01      | ~ v1_relat_1(X1)
% 35.15/5.01      | ~ v1_relat_1(X3)
% 35.15/5.01      | ~ v1_relat_1(X2)
% 35.15/5.01      | k5_relat_1(X1,X2) = X3 ),
% 35.15/5.01      inference(cnf_transformation,[],[f43]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_738,plain,
% 35.15/5.01      ( ~ r2_hidden(k4_tarski(X0,sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),X0),k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ v1_relat_1(sK8)
% 35.15/5.01      | k5_relat_1(k5_relat_1(sK6,sK7),sK8) = k5_relat_1(sK6,k5_relat_1(sK7,sK8)) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_7]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_4787,plain,
% 35.15/5.01      ( ~ r2_hidden(k4_tarski(sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ v1_relat_1(sK8)
% 35.15/5.01      | k5_relat_1(k5_relat_1(sK6,sK7),sK8) = k5_relat_1(sK6,k5_relat_1(sK7,sK8)) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_738]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_12,plain,
% 35.15/5.01      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 35.15/5.01      | r2_hidden(k4_tarski(X0,sK5(X2,X3,X0,X1)),X2)
% 35.15/5.01      | ~ v1_relat_1(X2)
% 35.15/5.01      | ~ v1_relat_1(X3)
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 35.15/5.01      inference(cnf_transformation,[],[f53]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_3014,plain,
% 35.15/5.01      ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK6)
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ v1_relat_1(sK7)
% 35.15/5.01      | ~ v1_relat_1(sK6) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_12]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_11,plain,
% 35.15/5.01      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
% 35.15/5.01      | r2_hidden(k4_tarski(sK5(X2,X3,X0,X1),X1),X3)
% 35.15/5.01      | ~ v1_relat_1(X2)
% 35.15/5.01      | ~ v1_relat_1(X3)
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
% 35.15/5.01      inference(cnf_transformation,[],[f52]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_3015,plain,
% 35.15/5.01      ( r2_hidden(k4_tarski(sK5(sK6,sK7,sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK7)
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ v1_relat_1(sK7)
% 35.15/5.01      | ~ v1_relat_1(sK6) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_11]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_2655,plain,
% 35.15/5.01      ( r2_hidden(k4_tarski(sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK7)
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ v1_relat_1(sK8)
% 35.15/5.01      | ~ v1_relat_1(sK7) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_12]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_2656,plain,
% 35.15/5.01      ( r2_hidden(k4_tarski(sK5(sK7,sK8,sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ v1_relat_1(sK8)
% 35.15/5.01      | ~ v1_relat_1(sK7) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_11]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_1357,plain,
% 35.15/5.01      ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))))),sK6)
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(sK6) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_12]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_1358,plain,
% 35.15/5.01      ( r2_hidden(k4_tarski(sK5(sK6,k5_relat_1(sK7,sK8),sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(sK6) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_11]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_13,plain,
% 35.15/5.01      ( ~ v1_relat_1(X0)
% 35.15/5.01      | ~ v1_relat_1(X1)
% 35.15/5.01      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 35.15/5.01      inference(cnf_transformation,[],[f44]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_976,plain,
% 35.15/5.01      ( v1_relat_1(k5_relat_1(sK7,sK8))
% 35.15/5.01      | ~ v1_relat_1(sK8)
% 35.15/5.01      | ~ v1_relat_1(sK7) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_13]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_822,plain,
% 35.15/5.01      ( ~ v1_relat_1(k5_relat_1(sK7,sK8))
% 35.15/5.01      | v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(sK6) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_13]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_801,plain,
% 35.15/5.01      ( v1_relat_1(k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ v1_relat_1(sK7)
% 35.15/5.01      | ~ v1_relat_1(sK6) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_13]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_9,plain,
% 35.15/5.01      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
% 35.15/5.01      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
% 35.15/5.01      | ~ v1_relat_1(X0)
% 35.15/5.01      | ~ v1_relat_1(X2)
% 35.15/5.01      | ~ v1_relat_1(X1)
% 35.15/5.01      | k5_relat_1(X0,X1) = X2 ),
% 35.15/5.01      inference(cnf_transformation,[],[f41]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_731,plain,
% 35.15/5.01      ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,sK7))
% 35.15/5.01      | r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ v1_relat_1(sK8)
% 35.15/5.01      | k5_relat_1(k5_relat_1(sK6,sK7),sK8) = k5_relat_1(sK6,k5_relat_1(sK7,sK8)) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_9]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_8,plain,
% 35.15/5.01      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
% 35.15/5.01      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
% 35.15/5.01      | ~ v1_relat_1(X0)
% 35.15/5.01      | ~ v1_relat_1(X2)
% 35.15/5.01      | ~ v1_relat_1(X1)
% 35.15/5.01      | k5_relat_1(X0,X1) = X2 ),
% 35.15/5.01      inference(cnf_transformation,[],[f42]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_728,plain,
% 35.15/5.01      ( r2_hidden(k4_tarski(sK4(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),sK8)
% 35.15/5.01      | r2_hidden(k4_tarski(sK2(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8))),sK3(k5_relat_1(sK6,sK7),sK8,k5_relat_1(sK6,k5_relat_1(sK7,sK8)))),k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,k5_relat_1(sK7,sK8)))
% 35.15/5.01      | ~ v1_relat_1(k5_relat_1(sK6,sK7))
% 35.15/5.01      | ~ v1_relat_1(sK8)
% 35.15/5.01      | k5_relat_1(k5_relat_1(sK6,sK7),sK8) = k5_relat_1(sK6,k5_relat_1(sK7,sK8)) ),
% 35.15/5.01      inference(instantiation,[status(thm)],[c_8]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_14,negated_conjecture,
% 35.15/5.01      ( k5_relat_1(k5_relat_1(sK6,sK7),sK8) != k5_relat_1(sK6,k5_relat_1(sK7,sK8)) ),
% 35.15/5.01      inference(cnf_transformation,[],[f48]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_15,negated_conjecture,
% 35.15/5.01      ( v1_relat_1(sK8) ),
% 35.15/5.01      inference(cnf_transformation,[],[f47]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_16,negated_conjecture,
% 35.15/5.01      ( v1_relat_1(sK7) ),
% 35.15/5.01      inference(cnf_transformation,[],[f46]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(c_17,negated_conjecture,
% 35.15/5.01      ( v1_relat_1(sK6) ),
% 35.15/5.01      inference(cnf_transformation,[],[f45]) ).
% 35.15/5.01  
% 35.15/5.01  cnf(contradiction,plain,
% 35.15/5.01      ( $false ),
% 35.15/5.01      inference(minisat,
% 35.15/5.01                [status(thm)],
% 35.15/5.01                [c_176091,c_27210,c_13482,c_4787,c_3014,c_3015,c_2655,
% 35.15/5.01                 c_2656,c_1357,c_1358,c_976,c_822,c_801,c_731,c_728,c_14,
% 35.15/5.01                 c_15,c_16,c_17]) ).
% 35.15/5.01  
% 35.15/5.01  
% 35.15/5.01  % SZS output end CNFRefutation for theBenchmark.p
% 35.15/5.01  
% 35.15/5.01  ------                               Statistics
% 35.15/5.01  
% 35.15/5.01  ------ General
% 35.15/5.01  
% 35.15/5.01  abstr_ref_over_cycles:                  0
% 35.15/5.01  abstr_ref_under_cycles:                 0
% 35.15/5.01  gc_basic_clause_elim:                   0
% 35.15/5.01  forced_gc_time:                         0
% 35.15/5.01  parsing_time:                           0.013
% 35.15/5.01  unif_index_cands_time:                  0.
% 35.15/5.01  unif_index_add_time:                    0.
% 35.15/5.01  orderings_time:                         0.
% 35.15/5.01  out_proof_time:                         0.014
% 35.15/5.01  total_time:                             4.115
% 35.15/5.01  num_of_symbols:                         45
% 35.15/5.01  num_of_terms:                           63139
% 35.15/5.01  
% 35.15/5.01  ------ Preprocessing
% 35.15/5.01  
% 35.15/5.01  num_of_splits:                          0
% 35.15/5.01  num_of_split_atoms:                     0
% 35.15/5.01  num_of_reused_defs:                     0
% 35.15/5.01  num_eq_ax_congr_red:                    57
% 35.15/5.01  num_of_sem_filtered_clauses:            1
% 35.15/5.01  num_of_subtypes:                        0
% 35.15/5.01  monotx_restored_types:                  0
% 35.15/5.01  sat_num_of_epr_types:                   0
% 35.15/5.01  sat_num_of_non_cyclic_types:            0
% 35.15/5.01  sat_guarded_non_collapsed_types:        0
% 35.15/5.01  num_pure_diseq_elim:                    0
% 35.15/5.01  simp_replaced_by:                       0
% 35.15/5.01  res_preprocessed:                       81
% 35.15/5.01  prep_upred:                             0
% 35.15/5.01  prep_unflattend:                        0
% 35.15/5.01  smt_new_axioms:                         0
% 35.15/5.01  pred_elim_cands:                        3
% 35.15/5.01  pred_elim:                              0
% 35.15/5.01  pred_elim_cl:                           0
% 35.15/5.01  pred_elim_cycles:                       2
% 35.15/5.01  merged_defs:                            0
% 35.15/5.01  merged_defs_ncl:                        0
% 35.15/5.01  bin_hyper_res:                          0
% 35.15/5.01  prep_cycles:                            4
% 35.15/5.01  pred_elim_time:                         0.001
% 35.15/5.01  splitting_time:                         0.
% 35.15/5.01  sem_filter_time:                        0.
% 35.15/5.01  monotx_time:                            0.001
% 35.15/5.01  subtype_inf_time:                       0.
% 35.15/5.01  
% 35.15/5.01  ------ Problem properties
% 35.15/5.01  
% 35.15/5.01  clauses:                                17
% 35.15/5.01  conjectures:                            4
% 35.15/5.01  epr:                                    6
% 35.15/5.01  horn:                                   14
% 35.15/5.01  ground:                                 4
% 35.15/5.01  unary:                                  5
% 35.15/5.01  binary:                                 0
% 35.15/5.01  lits:                                   59
% 35.15/5.01  lits_eq:                                5
% 35.15/5.01  fd_pure:                                0
% 35.15/5.01  fd_pseudo:                              0
% 35.15/5.01  fd_cond:                                0
% 35.15/5.01  fd_pseudo_cond:                         4
% 35.15/5.01  ac_symbols:                             0
% 35.15/5.01  
% 35.15/5.01  ------ Propositional Solver
% 35.15/5.01  
% 35.15/5.01  prop_solver_calls:                      31
% 35.15/5.01  prop_fast_solver_calls:                 4203
% 35.15/5.01  smt_solver_calls:                       0
% 35.15/5.01  smt_fast_solver_calls:                  0
% 35.15/5.01  prop_num_of_clauses:                    21746
% 35.15/5.01  prop_preprocess_simplified:             23398
% 35.15/5.01  prop_fo_subsumed:                       55
% 35.15/5.01  prop_solver_time:                       0.
% 35.15/5.01  smt_solver_time:                        0.
% 35.15/5.01  smt_fast_solver_time:                   0.
% 35.15/5.01  prop_fast_solver_time:                  0.
% 35.15/5.01  prop_unsat_core_time:                   0.003
% 35.15/5.01  
% 35.15/5.01  ------ QBF
% 35.15/5.01  
% 35.15/5.01  qbf_q_res:                              0
% 35.15/5.01  qbf_num_tautologies:                    0
% 35.15/5.01  qbf_prep_cycles:                        0
% 35.15/5.01  
% 35.15/5.01  ------ BMC1
% 35.15/5.01  
% 35.15/5.01  bmc1_current_bound:                     -1
% 35.15/5.01  bmc1_last_solved_bound:                 -1
% 35.15/5.01  bmc1_unsat_core_size:                   -1
% 35.15/5.01  bmc1_unsat_core_parents_size:           -1
% 35.15/5.01  bmc1_merge_next_fun:                    0
% 35.15/5.01  bmc1_unsat_core_clauses_time:           0.
% 35.15/5.01  
% 35.15/5.01  ------ Instantiation
% 35.15/5.01  
% 35.15/5.01  inst_num_of_clauses:                    2560
% 35.15/5.01  inst_num_in_passive:                    638
% 35.15/5.01  inst_num_in_active:                     1083
% 35.15/5.01  inst_num_in_unprocessed:                838
% 35.15/5.01  inst_num_of_loops:                      1597
% 35.15/5.01  inst_num_of_learning_restarts:          0
% 35.15/5.01  inst_num_moves_active_passive:          510
% 35.15/5.01  inst_lit_activity:                      0
% 35.15/5.01  inst_lit_activity_moves:                0
% 35.15/5.01  inst_num_tautologies:                   0
% 35.15/5.01  inst_num_prop_implied:                  0
% 35.15/5.01  inst_num_existing_simplified:           0
% 35.15/5.01  inst_num_eq_res_simplified:             0
% 35.15/5.01  inst_num_child_elim:                    0
% 35.15/5.01  inst_num_of_dismatching_blockings:      1861
% 35.15/5.01  inst_num_of_non_proper_insts:           3592
% 35.15/5.01  inst_num_of_duplicates:                 0
% 35.15/5.01  inst_inst_num_from_inst_to_res:         0
% 35.15/5.01  inst_dismatching_checking_time:         0.
% 35.15/5.01  
% 35.15/5.01  ------ Resolution
% 35.15/5.01  
% 35.15/5.01  res_num_of_clauses:                     0
% 35.15/5.01  res_num_in_passive:                     0
% 35.15/5.01  res_num_in_active:                      0
% 35.15/5.01  res_num_of_loops:                       85
% 35.15/5.01  res_forward_subset_subsumed:            313
% 35.15/5.01  res_backward_subset_subsumed:           0
% 35.15/5.01  res_forward_subsumed:                   0
% 35.15/5.01  res_backward_subsumed:                  0
% 35.15/5.01  res_forward_subsumption_resolution:     0
% 35.15/5.01  res_backward_subsumption_resolution:    0
% 35.15/5.01  res_clause_to_clause_subsumption:       251510
% 35.15/5.01  res_orphan_elimination:                 0
% 35.15/5.01  res_tautology_del:                      505
% 35.15/5.01  res_num_eq_res_simplified:              0
% 35.15/5.01  res_num_sel_changes:                    0
% 35.15/5.01  res_moves_from_active_to_pass:          0
% 35.15/5.01  
% 35.15/5.01  ------ Superposition
% 35.15/5.01  
% 35.15/5.01  sup_time_total:                         0.
% 35.15/5.01  sup_time_generating:                    0.
% 35.15/5.01  sup_time_sim_full:                      0.
% 35.15/5.01  sup_time_sim_immed:                     0.
% 35.15/5.01  
% 35.15/5.01  sup_num_of_clauses:                     4951
% 35.15/5.01  sup_num_in_active:                      290
% 35.15/5.01  sup_num_in_passive:                     4661
% 35.15/5.01  sup_num_of_loops:                       318
% 35.15/5.01  sup_fw_superposition:                   3101
% 35.15/5.01  sup_bw_superposition:                   3280
% 35.15/5.01  sup_immediate_simplified:               321
% 35.15/5.01  sup_given_eliminated:                   0
% 35.15/5.01  comparisons_done:                       0
% 35.15/5.01  comparisons_avoided:                    0
% 35.15/5.01  
% 35.15/5.01  ------ Simplifications
% 35.15/5.01  
% 35.15/5.01  
% 35.15/5.01  sim_fw_subset_subsumed:                 64
% 35.15/5.01  sim_bw_subset_subsumed:                 600
% 35.15/5.01  sim_fw_subsumed:                        164
% 35.15/5.01  sim_bw_subsumed:                        75
% 35.15/5.01  sim_fw_subsumption_res:                 86
% 35.15/5.01  sim_bw_subsumption_res:                 0
% 35.15/5.01  sim_tautology_del:                      11
% 35.15/5.01  sim_eq_tautology_del:                   56
% 35.15/5.01  sim_eq_res_simp:                        4
% 35.15/5.01  sim_fw_demodulated:                     0
% 35.15/5.01  sim_bw_demodulated:                     0
% 35.15/5.01  sim_light_normalised:                   0
% 35.15/5.01  sim_joinable_taut:                      0
% 35.15/5.01  sim_joinable_simp:                      0
% 35.15/5.01  sim_ac_normalised:                      0
% 35.15/5.01  sim_smt_subsumption:                    0
% 35.15/5.01  
%------------------------------------------------------------------------------
