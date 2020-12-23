%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0457+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:40 EST 2020

% Result     : Theorem 43.30s
% Output     : CNFRefutation 43.30s
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
fof(f643,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1557,plain,(
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
    inference(nnf_transformation,[],[f643])).

fof(f1558,plain,(
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
    inference(rectify,[],[f1557])).

fof(f1561,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK134(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1560,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK133(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1559,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK132(X0,X1)),X0)
          | ~ r2_hidden(sK132(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK132(X0,X1)),X0)
          | r2_hidden(sK132(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1562,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK132(X0,X1)),X0)
            | ~ r2_hidden(sK132(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK133(X0,X1),sK132(X0,X1)),X0)
            | r2_hidden(sK132(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK134(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK132,sK133,sK134])],[f1558,f1561,f1560,f1559])).

fof(f2598,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1562])).

fof(f3336,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f2598])).

fof(f651,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1130,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f651])).

fof(f1131,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1130])).

fof(f2613,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1131])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1128,plain,(
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

fof(f1567,plain,(
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
    inference(nnf_transformation,[],[f1128])).

fof(f1568,plain,(
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
    inference(rectify,[],[f1567])).

fof(f1571,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK140(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK140(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1570,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK139(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK139(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1569,plain,(
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

fof(f1572,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK137,sK138,sK139,sK140])],[f1568,f1571,f1570,f1569])).

fof(f2607,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK140(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1572])).

fof(f3341,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK140(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2607])).

fof(f2597,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK134(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1562])).

fof(f3337,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK134(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2597])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f704,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f1191,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f704])).

fof(f1192,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1191])).

fof(f1193,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1194,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f1192,f1193])).

fof(f1589,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1194])).

fof(f1590,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1194])).

fof(f684,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f685,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f684])).

fof(f1169,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f685])).

fof(f1578,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k2_relat_1(k5_relat_1(X0,sK144)),k2_relat_1(sK144))
        & v1_relat_1(sK144) ) ) ),
    introduced(choice_axiom,[])).

fof(f1577,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK143,X1)),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK143) ) ),
    introduced(choice_axiom,[])).

fof(f1579,plain,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))
    & v1_relat_1(sK144)
    & v1_relat_1(sK143) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK143,sK144])],[f1169,f1578,f1577])).

fof(f2654,plain,(
    ~ r1_tarski(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144)) ),
    inference(cnf_transformation,[],[f1579])).

fof(f2653,plain,(
    v1_relat_1(sK144) ),
    inference(cnf_transformation,[],[f1579])).

fof(f2652,plain,(
    v1_relat_1(sK143) ),
    inference(cnf_transformation,[],[f1579])).

cnf(c_1005,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f3336])).

cnf(c_179697,plain,
    ( ~ r2_hidden(k4_tarski(sK140(sK143,sK144,sK134(k5_relat_1(sK143,sK144),sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))),sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))),sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))),sK144)
    | r2_hidden(sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144)),k2_relat_1(sK144)) ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_1019,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2613])).

cnf(c_78741,plain,
    ( v1_relat_1(k5_relat_1(sK143,sK144))
    | ~ v1_relat_1(sK144)
    | ~ v1_relat_1(sK143) ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_1016,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
    | r2_hidden(k4_tarski(sK140(X2,X3,X0,X1),X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(k5_relat_1(X2,X3)) ),
    inference(cnf_transformation,[],[f3341])).

cnf(c_78723,plain,
    ( r2_hidden(k4_tarski(sK140(sK143,sK144,sK134(k5_relat_1(sK143,sK144),sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))),sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))),sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))),sK144)
    | ~ r2_hidden(k4_tarski(sK134(k5_relat_1(sK143,sK144),sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))),sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))),k5_relat_1(sK143,sK144))
    | ~ v1_relat_1(k5_relat_1(sK143,sK144))
    | ~ v1_relat_1(sK144)
    | ~ v1_relat_1(sK143) ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_1006,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK134(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f3337])).

cnf(c_60132,plain,
    ( r2_hidden(k4_tarski(sK134(k5_relat_1(sK143,sK144),sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))),sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))),k5_relat_1(sK143,sK144))
    | ~ r2_hidden(sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144)),k2_relat_1(k5_relat_1(sK143,sK144))) ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK11(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1589])).

cnf(c_52319,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))
    | r2_hidden(sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144)),k2_relat_1(k5_relat_1(sK143,sK144))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK11(X0,X1),X1) ),
    inference(cnf_transformation,[],[f1590])).

cnf(c_52311,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144))
    | ~ r2_hidden(sK11(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144)),k2_relat_1(sK144)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1058,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK143,sK144)),k2_relat_1(sK144)) ),
    inference(cnf_transformation,[],[f2654])).

cnf(c_1059,negated_conjecture,
    ( v1_relat_1(sK144) ),
    inference(cnf_transformation,[],[f2653])).

cnf(c_1060,negated_conjecture,
    ( v1_relat_1(sK143) ),
    inference(cnf_transformation,[],[f2652])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_179697,c_78741,c_78723,c_60132,c_52319,c_52311,c_1058,c_1059,c_1060])).

%------------------------------------------------------------------------------
