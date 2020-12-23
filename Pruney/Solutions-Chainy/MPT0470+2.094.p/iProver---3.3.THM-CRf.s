%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:11 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 199 expanded)
%              Number of clauses        :   54 (  86 expanded)
%              Number of leaves         :   14 (  45 expanded)
%              Depth                    :   19
%              Number of atoms          :  320 ( 700 expanded)
%              Number of equality atoms :  110 ( 204 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   17 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f33,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f26])).

fof(f42,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f14])).

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
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f24,f23,f22])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,
    ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16427,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_tarski(sK4(sK6,k1_xboole_0,X0),sK3(sK6,k1_xboole_0,X0)),X1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_16429,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_16427])).

cnf(c_1,negated_conjecture,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_16208,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),k2_zfmisc_1(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_16214,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_16208])).

cnf(c_7,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | r2_hidden(k4_tarski(X0,X1),X3)
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16184,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X0)
    | r2_hidden(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X2)
    | ~ r1_tarski(X0,X2)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_16207,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X0)
    | r2_hidden(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),k2_zfmisc_1(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X2))
    | ~ r1_tarski(X0,k2_zfmisc_1(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X2))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_16184])).

cnf(c_16210,plain,
    ( r2_hidden(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0))
    | ~ r2_hidden(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_16207])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12301,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12307,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10,plain,
    ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12302,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12303,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),X3) = iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12412,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X3) = iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12302,c_12303])).

cnf(c_12306,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12453,plain,
    ( k5_relat_1(X0,X1) = X2
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) = iProver_top
    | r1_tarski(X2,k2_zfmisc_1(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X3)) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12412,c_12306])).

cnf(c_12520,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12307,c_12453])).

cnf(c_2,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12305,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12304,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12374,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12305,c_12304])).

cnf(c_12379,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12301,c_12374])).

cnf(c_12525,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X0) = iProver_top
    | k5_relat_1(X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12520,c_12379])).

cnf(c_12526,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_12525])).

cnf(c_12533,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12526,c_12303])).

cnf(c_12546,plain,
    ( k5_relat_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,k2_zfmisc_1(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12533,c_12306])).

cnf(c_12579,plain,
    ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12307,c_12546])).

cnf(c_12585,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12579,c_12379])).

cnf(c_12586,plain,
    ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12585])).

cnf(c_12591,plain,
    ( k5_relat_1(k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12301,c_12586])).

cnf(c_12535,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_tarski(sK2(sK6,X0,k1_xboole_0),sK3(sK6,X0,k1_xboole_0)),X1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_12537,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12535])).

cnf(c_12382,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),k2_zfmisc_1(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_12388,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_12382])).

cnf(c_12367,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X1)
    | r2_hidden(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_12381,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X1)
    | r2_hidden(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),k2_zfmisc_1(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X2))
    | ~ r1_tarski(X1,k2_zfmisc_1(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X2))
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_12367])).

cnf(c_12384,plain,
    ( r2_hidden(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0))
    | ~ r2_hidden(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12381])).

cnf(c_12380,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12379])).

cnf(c_227,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4794,plain,
    ( k5_relat_1(k1_xboole_0,sK6) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_4795,plain,
    ( k5_relat_1(k1_xboole_0,sK6) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK6)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4794])).

cnf(c_2108,plain,
    ( X0 != X1
    | X0 = k5_relat_1(sK6,X2)
    | k5_relat_1(sK6,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_2109,plain,
    ( k5_relat_1(sK6,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(sK6,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_9,plain,
    ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1109,plain,
    ( r2_hidden(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X0)
    | r2_hidden(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(sK6)
    | k5_relat_1(sK6,X0) = X1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1116,plain,
    ( r2_hidden(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(k1_xboole_0)
    | k5_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_226,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_241,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16429,c_16214,c_16210,c_12591,c_12537,c_12388,c_12384,c_12380,c_4795,c_2109,c_1116,c_241,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.73/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/0.99  
% 3.73/0.99  ------  iProver source info
% 3.73/0.99  
% 3.73/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.73/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/0.99  git: non_committed_changes: false
% 3.73/0.99  git: last_make_outside_of_git: false
% 3.73/0.99  
% 3.73/0.99  ------ 
% 3.73/0.99  ------ Parsing...
% 3.73/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  ------ Proving...
% 3.73/0.99  ------ Problem Properties 
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  clauses                                 16
% 3.73/0.99  conjectures                             3
% 3.73/0.99  EPR                                     2
% 3.73/0.99  Horn                                    13
% 3.73/0.99  unary                                   4
% 3.73/0.99  binary                                  1
% 3.73/0.99  lits                                    57
% 3.73/0.99  lits eq                                 5
% 3.73/0.99  fd_pure                                 0
% 3.73/0.99  fd_pseudo                               0
% 3.73/0.99  fd_cond                                 0
% 3.73/0.99  fd_pseudo_cond                          3
% 3.73/0.99  AC symbols                              0
% 3.73/0.99  
% 3.73/0.99  ------ Input Options Time Limit: Unbounded
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.73/0.99  Current options:
% 3.73/0.99  ------ 
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  % SZS status Theorem for theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  fof(f1,axiom,(
% 3.73/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f28,plain,(
% 3.73/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f1])).
% 3.73/0.99  
% 3.73/0.99  fof(f2,axiom,(
% 3.73/0.99    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f29,plain,(
% 3.73/0.99    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f2])).
% 3.73/0.99  
% 3.73/0.99  fof(f6,axiom,(
% 3.73/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f13,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 3.73/0.99    inference(ennf_transformation,[],[f6])).
% 3.73/0.99  
% 3.73/0.99  fof(f16,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.73/0.99    inference(nnf_transformation,[],[f13])).
% 3.73/0.99  
% 3.73/0.99  fof(f17,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.73/0.99    inference(rectify,[],[f16])).
% 3.73/0.99  
% 3.73/0.99  fof(f18,plain,(
% 3.73/0.99    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)))),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f19,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) & r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 3.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 3.73/0.99  
% 3.73/0.99  fof(f33,plain,(
% 3.73/0.99    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f19])).
% 3.73/0.99  
% 3.73/0.99  fof(f8,conjecture,(
% 3.73/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f9,negated_conjecture,(
% 3.73/0.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.73/0.99    inference(negated_conjecture,[],[f8])).
% 3.73/0.99  
% 3.73/0.99  fof(f15,plain,(
% 3.73/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.73/0.99    inference(ennf_transformation,[],[f9])).
% 3.73/0.99  
% 3.73/0.99  fof(f26,plain,(
% 3.73/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6)) & v1_relat_1(sK6))),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f27,plain,(
% 3.73/0.99    (k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6)) & v1_relat_1(sK6)),
% 3.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f26])).
% 3.73/0.99  
% 3.73/0.99  fof(f42,plain,(
% 3.73/0.99    v1_relat_1(sK6)),
% 3.73/0.99    inference(cnf_transformation,[],[f27])).
% 3.73/0.99  
% 3.73/0.99  fof(f7,axiom,(
% 3.73/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f14,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.73/0.99    inference(ennf_transformation,[],[f7])).
% 3.73/0.99  
% 3.73/0.99  fof(f20,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.73/0.99    inference(nnf_transformation,[],[f14])).
% 3.73/0.99  
% 3.73/0.99  fof(f21,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.73/0.99    inference(rectify,[],[f20])).
% 3.73/0.99  
% 3.73/0.99  fof(f24,plain,(
% 3.73/0.99    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f23,plain,(
% 3.73/0.99    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),X4),X1) & r2_hidden(k4_tarski(X3,sK4(X0,X1,X2)),X0)))) )),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f22,plain,(
% 3.73/0.99    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f25,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f24,f23,f22])).
% 3.73/0.99  
% 3.73/0.99  fof(f39,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f25])).
% 3.73/0.99  
% 3.73/0.99  fof(f3,axiom,(
% 3.73/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f30,plain,(
% 3.73/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f3])).
% 3.73/0.99  
% 3.73/0.99  fof(f5,axiom,(
% 3.73/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f12,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.73/0.99    inference(ennf_transformation,[],[f5])).
% 3.73/0.99  
% 3.73/0.99  fof(f32,plain,(
% 3.73/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f12])).
% 3.73/0.99  
% 3.73/0.99  fof(f40,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f25])).
% 3.73/0.99  
% 3.73/0.99  fof(f43,plain,(
% 3.73/0.99    k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6)),
% 3.73/0.99    inference(cnf_transformation,[],[f27])).
% 3.73/0.99  
% 3.73/0.99  cnf(c_0,plain,
% 3.73/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_16427,plain,
% 3.73/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_tarski(sK4(sK6,k1_xboole_0,X0),sK3(sK6,k1_xboole_0,X0)),X1)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_16429,plain,
% 3.73/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_16427]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1,negated_conjecture,
% 3.73/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.73/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_16208,plain,
% 3.73/0.99      ( ~ r2_hidden(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),k2_zfmisc_1(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X2)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_16214,plain,
% 3.73/0.99      ( ~ r2_hidden(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_16208]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_7,plain,
% 3.73/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.73/0.99      | r2_hidden(k4_tarski(X0,X1),X3)
% 3.73/0.99      | ~ r1_tarski(X2,X3)
% 3.73/0.99      | ~ v1_relat_1(X2) ),
% 3.73/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_16184,plain,
% 3.73/0.99      ( ~ r2_hidden(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X0)
% 3.73/0.99      | r2_hidden(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X2)
% 3.73/0.99      | ~ r1_tarski(X0,X2)
% 3.73/0.99      | ~ v1_relat_1(X0) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_16207,plain,
% 3.73/0.99      ( ~ r2_hidden(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X0)
% 3.73/0.99      | r2_hidden(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),k2_zfmisc_1(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X2))
% 3.73/0.99      | ~ r1_tarski(X0,k2_zfmisc_1(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X2))
% 3.73/0.99      | ~ v1_relat_1(X0) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_16184]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_16210,plain,
% 3.73/0.99      ( r2_hidden(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0))
% 3.73/0.99      | ~ r2_hidden(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
% 3.73/0.99      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0))
% 3.73/0.99      | ~ v1_relat_1(k1_xboole_0) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_16207]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_15,negated_conjecture,
% 3.73/0.99      ( v1_relat_1(sK6) ),
% 3.73/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12301,plain,
% 3.73/0.99      ( v1_relat_1(sK6) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12307,plain,
% 3.73/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_10,plain,
% 3.73/0.99      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
% 3.73/0.99      | ~ v1_relat_1(X0)
% 3.73/0.99      | ~ v1_relat_1(X1)
% 3.73/0.99      | ~ v1_relat_1(X2)
% 3.73/0.99      | k5_relat_1(X0,X1) = X2 ),
% 3.73/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12302,plain,
% 3.73/0.99      ( k5_relat_1(X0,X1) = X2
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) = iProver_top
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) = iProver_top
% 3.73/0.99      | v1_relat_1(X2) != iProver_top
% 3.73/0.99      | v1_relat_1(X0) != iProver_top
% 3.73/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12303,plain,
% 3.73/0.99      ( r2_hidden(k4_tarski(X0,X1),X2) != iProver_top
% 3.73/0.99      | r2_hidden(k4_tarski(X0,X1),X3) = iProver_top
% 3.73/0.99      | r1_tarski(X2,X3) != iProver_top
% 3.73/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12412,plain,
% 3.73/0.99      ( k5_relat_1(X0,X1) = X2
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) = iProver_top
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X3) = iProver_top
% 3.73/0.99      | r1_tarski(X2,X3) != iProver_top
% 3.73/0.99      | v1_relat_1(X2) != iProver_top
% 3.73/0.99      | v1_relat_1(X0) != iProver_top
% 3.73/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_12302,c_12303]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12306,plain,
% 3.73/0.99      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12453,plain,
% 3.73/0.99      ( k5_relat_1(X0,X1) = X2
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) = iProver_top
% 3.73/0.99      | r1_tarski(X2,k2_zfmisc_1(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X3)) != iProver_top
% 3.73/0.99      | v1_relat_1(X2) != iProver_top
% 3.73/0.99      | v1_relat_1(X0) != iProver_top
% 3.73/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_12412,c_12306]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12520,plain,
% 3.73/0.99      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X0) = iProver_top
% 3.73/0.99      | v1_relat_1(X0) != iProver_top
% 3.73/0.99      | v1_relat_1(X1) != iProver_top
% 3.73/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_12307,c_12453]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2,plain,
% 3.73/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.73/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12305,plain,
% 3.73/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4,plain,
% 3.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/0.99      | ~ v1_relat_1(X1)
% 3.73/0.99      | v1_relat_1(X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12304,plain,
% 3.73/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.73/0.99      | v1_relat_1(X1) != iProver_top
% 3.73/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12374,plain,
% 3.73/0.99      ( v1_relat_1(X0) != iProver_top
% 3.73/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_12305,c_12304]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12379,plain,
% 3.73/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_12301,c_12374]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12525,plain,
% 3.73/0.99      ( v1_relat_1(X1) != iProver_top
% 3.73/0.99      | v1_relat_1(X0) != iProver_top
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X0) = iProver_top
% 3.73/0.99      | k5_relat_1(X0,X1) = k1_xboole_0 ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_12520,c_12379]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12526,plain,
% 3.73/0.99      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X0) = iProver_top
% 3.73/0.99      | v1_relat_1(X0) != iProver_top
% 3.73/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.73/0.99      inference(renaming,[status(thm)],[c_12525]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12533,plain,
% 3.73/0.99      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X2) = iProver_top
% 3.73/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.73/0.99      | v1_relat_1(X0) != iProver_top
% 3.73/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_12526,c_12303]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12546,plain,
% 3.73/0.99      ( k5_relat_1(X0,X1) = k1_xboole_0
% 3.73/0.99      | r1_tarski(X0,k2_zfmisc_1(k4_tarski(sK2(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X2)) != iProver_top
% 3.73/0.99      | v1_relat_1(X0) != iProver_top
% 3.73/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_12533,c_12306]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12579,plain,
% 3.73/0.99      ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.73/0.99      | v1_relat_1(X0) != iProver_top
% 3.73/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_12307,c_12546]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12585,plain,
% 3.73/0.99      ( v1_relat_1(X0) != iProver_top
% 3.73/0.99      | k5_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_12579,c_12379]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12586,plain,
% 3.73/0.99      ( k5_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.73/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.73/0.99      inference(renaming,[status(thm)],[c_12585]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12591,plain,
% 3.73/0.99      ( k5_relat_1(k1_xboole_0,sK6) = k1_xboole_0 ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_12301,c_12586]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12535,plain,
% 3.73/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_tarski(sK2(sK6,X0,k1_xboole_0),sK3(sK6,X0,k1_xboole_0)),X1)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12537,plain,
% 3.73/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_12535]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12382,plain,
% 3.73/0.99      ( ~ r2_hidden(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),k2_zfmisc_1(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X2)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12388,plain,
% 3.73/0.99      ( ~ r2_hidden(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_12382]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12367,plain,
% 3.73/0.99      ( ~ r2_hidden(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X1)
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X2)
% 3.73/0.99      | ~ r1_tarski(X1,X2)
% 3.73/0.99      | ~ v1_relat_1(X1) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12381,plain,
% 3.73/0.99      ( ~ r2_hidden(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X1)
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),k2_zfmisc_1(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X2))
% 3.73/0.99      | ~ r1_tarski(X1,k2_zfmisc_1(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X2))
% 3.73/0.99      | ~ v1_relat_1(X1) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_12367]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12384,plain,
% 3.73/0.99      ( r2_hidden(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k2_zfmisc_1(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0))
% 3.73/0.99      | ~ r2_hidden(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
% 3.73/0.99      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0))
% 3.73/0.99      | ~ v1_relat_1(k1_xboole_0) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_12381]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12380,plain,
% 3.73/0.99      ( v1_relat_1(k1_xboole_0) ),
% 3.73/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_12379]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_227,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4794,plain,
% 3.73/0.99      ( k5_relat_1(k1_xboole_0,sK6) != X0
% 3.73/0.99      | k1_xboole_0 != X0
% 3.73/0.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK6) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_227]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4795,plain,
% 3.73/0.99      ( k5_relat_1(k1_xboole_0,sK6) != k1_xboole_0
% 3.73/0.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK6)
% 3.73/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_4794]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2108,plain,
% 3.73/0.99      ( X0 != X1 | X0 = k5_relat_1(sK6,X2) | k5_relat_1(sK6,X2) != X1 ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_227]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2109,plain,
% 3.73/0.99      ( k5_relat_1(sK6,k1_xboole_0) != k1_xboole_0
% 3.73/0.99      | k1_xboole_0 = k5_relat_1(sK6,k1_xboole_0)
% 3.73/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_2108]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_9,plain,
% 3.73/0.99      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
% 3.73/0.99      | ~ v1_relat_1(X0)
% 3.73/0.99      | ~ v1_relat_1(X1)
% 3.73/0.99      | ~ v1_relat_1(X2)
% 3.73/0.99      | k5_relat_1(X0,X1) = X2 ),
% 3.73/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1109,plain,
% 3.73/0.99      ( r2_hidden(k4_tarski(sK4(sK6,X0,X1),sK3(sK6,X0,X1)),X0)
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(sK6,X0,X1),sK3(sK6,X0,X1)),X1)
% 3.73/0.99      | ~ v1_relat_1(X0)
% 3.73/0.99      | ~ v1_relat_1(X1)
% 3.73/0.99      | ~ v1_relat_1(sK6)
% 3.73/0.99      | k5_relat_1(sK6,X0) = X1 ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1116,plain,
% 3.73/0.99      ( r2_hidden(k4_tarski(sK4(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
% 3.73/0.99      | r2_hidden(k4_tarski(sK2(sK6,k1_xboole_0,k1_xboole_0),sK3(sK6,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
% 3.73/0.99      | ~ v1_relat_1(sK6)
% 3.73/0.99      | ~ v1_relat_1(k1_xboole_0)
% 3.73/0.99      | k5_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_1109]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_226,plain,( X0 = X0 ),theory(equality) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_241,plain,
% 3.73/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_226]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_14,negated_conjecture,
% 3.73/0.99      ( k1_xboole_0 != k5_relat_1(sK6,k1_xboole_0)
% 3.73/0.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK6) ),
% 3.73/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(contradiction,plain,
% 3.73/0.99      ( $false ),
% 3.73/0.99      inference(minisat,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_16429,c_16214,c_16210,c_12591,c_12537,c_12388,c_12384,
% 3.73/0.99                 c_12380,c_4795,c_2109,c_1116,c_241,c_14,c_15]) ).
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  ------                               Statistics
% 3.73/0.99  
% 3.73/0.99  ------ Selected
% 3.73/0.99  
% 3.73/0.99  total_time:                             0.434
% 3.73/0.99  
%------------------------------------------------------------------------------
