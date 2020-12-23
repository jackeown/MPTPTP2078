%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0958+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:58 EST 2020

% Result     : Theorem 11.80s
% Output     : CNFRefutation 11.80s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of clauses        :    9 (  10 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 151 expanded)
%              Number of equality atoms :   30 (  30 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1126,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2577,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1126])).

fof(f3704,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ r4_relat_2(X0,k3_relat_1(X0)) )
        & ( r4_relat_2(X0,k3_relat_1(X0))
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2577])).

fof(f6052,plain,(
    ! [X0] :
      ( r4_relat_2(X0,k3_relat_1(X0))
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3704])).

fof(f1456,conjecture,(
    ! [X0] : r4_relat_2(k1_wellord2(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1457,negated_conjecture,(
    ~ ! [X0] : r4_relat_2(k1_wellord2(X0),X0) ),
    inference(negated_conjecture,[],[f1456])).

fof(f2951,plain,(
    ? [X0] : ~ r4_relat_2(k1_wellord2(X0),X0) ),
    inference(ennf_transformation,[],[f1457])).

fof(f4165,plain,
    ( ? [X0] : ~ r4_relat_2(k1_wellord2(X0),X0)
   => ~ r4_relat_2(k1_wellord2(sK510),sK510) ),
    introduced(choice_axiom,[])).

fof(f4166,plain,(
    ~ r4_relat_2(k1_wellord2(sK510),sK510) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK510])],[f2951,f4165])).

fof(f6857,plain,(
    ~ r4_relat_2(k1_wellord2(sK510),sK510) ),
    inference(cnf_transformation,[],[f4166])).

fof(f1420,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2908,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1420])).

fof(f2909,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2908])).

fof(f4075,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f2909])).

fof(f4076,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f4075])).

fof(f4077,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f4076])).

fof(f4078,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK465(X0,X1),sK466(X0,X1))
          | ~ r2_hidden(k4_tarski(sK465(X0,X1),sK466(X0,X1)),X1) )
        & ( r1_tarski(sK465(X0,X1),sK466(X0,X1))
          | r2_hidden(k4_tarski(sK465(X0,X1),sK466(X0,X1)),X1) )
        & r2_hidden(sK466(X0,X1),X0)
        & r2_hidden(sK465(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f4079,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK465(X0,X1),sK466(X0,X1))
              | ~ r2_hidden(k4_tarski(sK465(X0,X1),sK466(X0,X1)),X1) )
            & ( r1_tarski(sK465(X0,X1),sK466(X0,X1))
              | r2_hidden(k4_tarski(sK465(X0,X1),sK466(X0,X1)),X1) )
            & r2_hidden(sK466(X0,X1),X0)
            & r2_hidden(sK465(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK465,sK466])],[f4077,f4078])).

fof(f6725,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f4079])).

fof(f8140,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f6725])).

fof(f1425,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6753,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1425])).

fof(f1460,axiom,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6860,plain,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1460])).

cnf(c_1871,plain,
    ( r4_relat_2(X0,k3_relat_1(X0))
    | ~ v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f6052])).

cnf(c_2667,negated_conjecture,
    ( ~ r4_relat_2(k1_wellord2(sK510),sK510) ),
    inference(cnf_transformation,[],[f6857])).

cnf(c_40057,plain,
    ( ~ v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | k1_wellord2(sK510) != X0
    | k3_relat_1(X0) != sK510 ),
    inference(resolution_lifted,[status(thm)],[c_1871,c_2667])).

cnf(c_40058,plain,
    ( ~ v4_relat_2(k1_wellord2(sK510))
    | ~ v1_relat_1(k1_wellord2(sK510))
    | k3_relat_1(k1_wellord2(sK510)) != sK510 ),
    inference(unflattening,[status(thm)],[c_40057])).

cnf(c_2541,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f8140])).

cnf(c_2563,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6753])).

cnf(c_13510,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2541,c_2563])).

cnf(c_2670,plain,
    ( v4_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6860])).

cnf(c_40066,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_40058,c_13510,c_2563,c_2670])).

%------------------------------------------------------------------------------
