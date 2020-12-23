%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0548+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:32 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of clauses        :   15 (  20 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :   12
%              Number of atoms          :  130 ( 147 expanded)
%              Number of equality atoms :   28 (  29 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,conjecture,(
    ! [X0] : k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0] : k9_relat_1(k1_xboole_0,X0) != k1_xboole_0 ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,
    ( ? [X0] : k9_relat_1(k1_xboole_0,X0) != k1_xboole_0
   => k9_relat_1(k1_xboole_0,sK3) != k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k9_relat_1(k1_xboole_0,sK3) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).

fof(f33,plain,(
    k9_relat_1(k1_xboole_0,sK3) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_8,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_158,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_159,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_142,plain,
    ( v1_relat_1(X0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_143,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_142])).

cnf(c_176,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
    | k9_relat_1(X0,X1) = X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_143])).

cnf(c_177,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0,X1),X1)
    | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0,X1),sK0(k1_xboole_0,X0,X1)),k1_xboole_0)
    | k9_relat_1(k1_xboole_0,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_187,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0,X1),X1)
    | k9_relat_1(k1_xboole_0,X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_177,c_159])).

cnf(c_280,plain,
    ( sK0(k1_xboole_0,X0,X1) != X2
    | k9_relat_1(k1_xboole_0,X0) = X1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_159,c_187])).

cnf(c_281,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_11,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,sK3) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_319,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_281,c_11])).


%------------------------------------------------------------------------------
