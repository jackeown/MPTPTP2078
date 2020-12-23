%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0957+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:58 EST 2020

% Result     : Theorem 11.22s
% Output     : CNFRefutation 11.22s
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
fof(f1128,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2578,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1128])).

fof(f3705,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2578])).

fof(f6055,plain,(
    ! [X0] :
      ( r8_relat_2(X0,k3_relat_1(X0))
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3705])).

fof(f1455,conjecture,(
    ! [X0] : r8_relat_2(k1_wellord2(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1456,negated_conjecture,(
    ~ ! [X0] : r8_relat_2(k1_wellord2(X0),X0) ),
    inference(negated_conjecture,[],[f1455])).

fof(f2950,plain,(
    ? [X0] : ~ r8_relat_2(k1_wellord2(X0),X0) ),
    inference(ennf_transformation,[],[f1456])).

fof(f4164,plain,
    ( ? [X0] : ~ r8_relat_2(k1_wellord2(X0),X0)
   => ~ r8_relat_2(k1_wellord2(sK510),sK510) ),
    introduced(choice_axiom,[])).

fof(f4165,plain,(
    ~ r8_relat_2(k1_wellord2(sK510),sK510) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK510])],[f2950,f4164])).

fof(f6855,plain,(
    ~ r8_relat_2(k1_wellord2(sK510),sK510) ),
    inference(cnf_transformation,[],[f4165])).

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
    inference(ennf_transformation,[],[f1420])).

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
    inference(flattening,[],[f2907])).

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
    inference(nnf_transformation,[],[f2908])).

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
    inference(flattening,[],[f4074])).

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
    inference(rectify,[],[f4075])).

fof(f4077,plain,(
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

fof(f4078,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK465,sK466])],[f4076,f4077])).

fof(f6724,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f4078])).

fof(f8138,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f6724])).

fof(f1425,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6752,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1425])).

fof(f1457,axiom,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6856,plain,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1457])).

cnf(c_1875,plain,
    ( r8_relat_2(X0,k3_relat_1(X0))
    | ~ v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f6055])).

cnf(c_2666,negated_conjecture,
    ( ~ r8_relat_2(k1_wellord2(sK510),sK510) ),
    inference(cnf_transformation,[],[f6855])).

cnf(c_41848,plain,
    ( ~ v8_relat_2(X0)
    | ~ v1_relat_1(X0)
    | k1_wellord2(sK510) != X0
    | k3_relat_1(X0) != sK510 ),
    inference(resolution_lifted,[status(thm)],[c_1875,c_2666])).

cnf(c_41849,plain,
    ( ~ v8_relat_2(k1_wellord2(sK510))
    | ~ v1_relat_1(k1_wellord2(sK510))
    | k3_relat_1(k1_wellord2(sK510)) != sK510 ),
    inference(unflattening,[status(thm)],[c_41848])).

cnf(c_2541,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f8138])).

cnf(c_2563,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6752])).

cnf(c_13503,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2541,c_2563])).

cnf(c_2667,plain,
    ( v8_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6856])).

cnf(c_41857,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_41849,c_13503,c_2563,c_2667])).

%------------------------------------------------------------------------------
