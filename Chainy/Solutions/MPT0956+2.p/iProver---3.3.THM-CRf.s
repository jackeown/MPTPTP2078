%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0956+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:58 EST 2020

% Result     : Theorem 11.18s
% Output     : CNFRefutation 11.18s
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
fof(f1139,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2589,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> r1_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1139])).

fof(f3743,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ~ r1_relat_2(X0,k3_relat_1(X0)) )
        & ( r1_relat_2(X0,k3_relat_1(X0))
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2589])).

fof(f6112,plain,(
    ! [X0] :
      ( r1_relat_2(X0,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3743])).

fof(f1453,conjecture,(
    ! [X0] : r1_relat_2(k1_wellord2(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1454,negated_conjecture,(
    ~ ! [X0] : r1_relat_2(k1_wellord2(X0),X0) ),
    inference(negated_conjecture,[],[f1453])).

fof(f2949,plain,(
    ? [X0] : ~ r1_relat_2(k1_wellord2(X0),X0) ),
    inference(ennf_transformation,[],[f1454])).

fof(f4163,plain,
    ( ? [X0] : ~ r1_relat_2(k1_wellord2(X0),X0)
   => ~ r1_relat_2(k1_wellord2(sK510),sK510) ),
    introduced(choice_axiom,[])).

fof(f4164,plain,(
    ~ r1_relat_2(k1_wellord2(sK510),sK510) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK510])],[f2949,f4163])).

fof(f6852,plain,(
    ~ r1_relat_2(k1_wellord2(sK510),sK510) ),
    inference(cnf_transformation,[],[f4164])).

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

fof(f2906,plain,(
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

fof(f2907,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2906])).

fof(f4073,plain,(
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
    inference(nnf_transformation,[],[f2907])).

fof(f4074,plain,(
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
    inference(flattening,[],[f4073])).

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
    inference(rectify,[],[f4074])).

fof(f4076,plain,(
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

fof(f4077,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK465,sK466])],[f4075,f4076])).

fof(f6723,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f4077])).

fof(f8136,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f6723])).

fof(f1425,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6751,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1425])).

fof(f1455,axiom,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6853,plain,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1455])).

cnf(c_1933,plain,
    ( r1_relat_2(X0,k3_relat_1(X0))
    | ~ v1_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f6112])).

cnf(c_2664,negated_conjecture,
    ( ~ r1_relat_2(k1_wellord2(sK510),sK510) ),
    inference(cnf_transformation,[],[f6852])).

cnf(c_31547,plain,
    ( ~ v1_relat_2(X0)
    | ~ v1_relat_1(X0)
    | k1_wellord2(sK510) != X0
    | k3_relat_1(X0) != sK510 ),
    inference(resolution_lifted,[status(thm)],[c_1933,c_2664])).

cnf(c_31548,plain,
    ( ~ v1_relat_2(k1_wellord2(sK510))
    | ~ v1_relat_1(k1_wellord2(sK510))
    | k3_relat_1(k1_wellord2(sK510)) != sK510 ),
    inference(unflattening,[status(thm)],[c_31547])).

cnf(c_2541,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f8136])).

cnf(c_2563,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6751])).

cnf(c_13496,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2541,c_2563])).

cnf(c_2665,plain,
    ( v1_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6853])).

cnf(c_31556,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_31548,c_13496,c_2563,c_2665])).

%------------------------------------------------------------------------------
