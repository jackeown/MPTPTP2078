%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0456+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:40 EST 2020

% Result     : Theorem 43.39s
% Output     : CNFRefutation 43.39s
% Verified   : 
% Statistics : Number of formulae       :   58 (  83 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  256 ( 373 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f642,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1549,plain,(
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
    inference(nnf_transformation,[],[f642])).

fof(f1550,plain,(
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
    inference(rectify,[],[f1549])).

fof(f1553,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK131(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1552,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK130(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1551,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK129(X0,X1),X3),X0)
          | ~ r2_hidden(sK129(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK129(X0,X1),X4),X0)
          | r2_hidden(sK129(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1554,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK129(X0,X1),X3),X0)
            | ~ r2_hidden(sK129(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK129(X0,X1),sK130(X0,X1)),X0)
            | r2_hidden(sK129(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK131(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK129,sK130,sK131])],[f1550,f1553,f1552,f1551])).

fof(f2592,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1554])).

fof(f3331,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f2592])).

fof(f651,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1129,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f651])).

fof(f1130,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1129])).

fof(f2611,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1130])).

fof(f646,axiom,(
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

fof(f1127,plain,(
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
    inference(ennf_transformation,[],[f646])).

fof(f1565,plain,(
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
    inference(nnf_transformation,[],[f1127])).

fof(f1566,plain,(
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
    inference(rectify,[],[f1565])).

fof(f1569,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK140(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK140(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1568,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK139(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK139(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1567,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK138(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK137(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK137(X0,X1,X2),sK138(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK138(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK137(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK137(X0,X1,X2),sK138(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1570,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK138(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK137(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK137(X0,X1,X2),sK138(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK139(X0,X1,X2),sK138(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK137(X0,X1,X2),sK139(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK137(X0,X1,X2),sK138(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK140(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK140(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK137,sK138,sK139,sK140])],[f1566,f1569,f1568,f1567])).

fof(f2604,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK140(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1570])).

fof(f3339,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK140(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2604])).

fof(f2591,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK131(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1554])).

fof(f3332,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK131(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2591])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f703,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1189,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f703])).

fof(f1190,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1189])).

fof(f1191,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1192,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1190,f1191])).

fof(f1587,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1192])).

fof(f1588,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1192])).

fof(f683,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f684,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f683])).

fof(f1167,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f684])).

fof(f1576,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k1_relat_1(k5_relat_1(X0,sK144)),k1_relat_1(X0))
        & v1_relat_1(sK144) ) ) ),
    introduced(choice_axiom,[])).

fof(f1575,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK143,X1)),k1_relat_1(sK143))
          & v1_relat_1(X1) )
      & v1_relat_1(sK143) ) ),
    introduced(choice_axiom,[])).

fof(f1577,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143))
    & v1_relat_1(sK144)
    & v1_relat_1(sK143) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK143,sK144])],[f1167,f1576,f1575])).

fof(f2651,plain,(
    ~ r1_tarski(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)) ),
    inference(cnf_transformation,[],[f1577])).

fof(f2650,plain,(
    v1_relat_1(sK144) ),
    inference(cnf_transformation,[],[f1577])).

fof(f2649,plain,(
    v1_relat_1(sK143) ),
    inference(cnf_transformation,[],[f1577])).

cnf(c_1001,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3331])).

cnf(c_182655,plain,
    ( ~ r2_hidden(k4_tarski(sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)),sK140(sK143,sK144,sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)),sK131(k5_relat_1(sK143,sK144),sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143))))),sK143)
    | r2_hidden(sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)),k1_relat_1(sK143)) ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_1019,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2611])).

cnf(c_79504,plain,
    ( v1_relat_1(k5_relat_1(sK143,sK144))
    | ~ v1_relat_1(sK144)
    | ~ v1_relat_1(sK143) ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_1017,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(X0,sK140(X2,X3,X0,X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f3339])).

cnf(c_79485,plain,
    ( r2_hidden(k4_tarski(sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)),sK140(sK143,sK144,sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)),sK131(k5_relat_1(sK143,sK144),sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143))))),sK143)
    | ~ r2_hidden(k4_tarski(sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)),sK131(k5_relat_1(sK143,sK144),sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)))),k5_relat_1(sK143,sK144))
    | ~ v1_relat_1(k5_relat_1(sK143,sK144))
    | ~ v1_relat_1(sK144)
    | ~ v1_relat_1(sK143) ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_1002,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK131(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f3332])).

cnf(c_60247,plain,
    ( r2_hidden(k4_tarski(sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)),sK131(k5_relat_1(sK143,sK144),sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)))),k5_relat_1(sK143,sK144))
    | ~ r2_hidden(sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)),k1_relat_1(k5_relat_1(sK143,sK144))) ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1587])).

cnf(c_52279,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143))
    | r2_hidden(sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)),k1_relat_1(k5_relat_1(sK143,sK144))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1588])).

cnf(c_52271,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143))
    | ~ r2_hidden(sK11(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)),k1_relat_1(sK143)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1057,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK143,sK144)),k1_relat_1(sK143)) ),
    inference(cnf_transformation,[],[f2651])).

cnf(c_1058,negated_conjecture,
    ( v1_relat_1(sK144) ),
    inference(cnf_transformation,[],[f2650])).

cnf(c_1059,negated_conjecture,
    ( v1_relat_1(sK143) ),
    inference(cnf_transformation,[],[f2649])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_182655,c_79504,c_79485,c_60247,c_52279,c_52271,c_1057,c_1058,c_1059])).

%------------------------------------------------------------------------------
