%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0616+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:48 EST 2020

% Result     : Theorem 19.24s
% Output     : CNFRefutation 19.24s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 412 expanded)
%              Number of clauses        :   35 (  96 expanded)
%              Number of leaves         :    8 (  81 expanded)
%              Depth                    :   19
%              Number of atoms          :  270 (2356 expanded)
%              Number of equality atoms :   84 ( 607 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f890,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1629,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f1630,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1629])).

fof(f2112,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1630])).

fof(f3474,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2112])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2126,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f4071,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | o_0_0_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f3474,f2126])).

fof(f4264,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f4071])).

fof(f893,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f894,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f893])).

fof(f1631,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f894])).

fof(f1632,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1631])).

fof(f2115,plain,(
    ? [X0,X1,X2] :
      ( ( k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1632])).

fof(f2116,plain,(
    ? [X0,X1,X2] :
      ( ( k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f2115])).

fof(f2117,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k1_funct_1(sK170,sK168) != sK169
        | ~ r2_hidden(sK168,k1_relat_1(sK170))
        | ~ r2_hidden(k4_tarski(sK168,sK169),sK170) )
      & ( ( k1_funct_1(sK170,sK168) = sK169
          & r2_hidden(sK168,k1_relat_1(sK170)) )
        | r2_hidden(k4_tarski(sK168,sK169),sK170) )
      & v1_funct_1(sK170)
      & v1_relat_1(sK170) ) ),
    introduced(choice_axiom,[])).

fof(f2118,plain,
    ( ( k1_funct_1(sK170,sK168) != sK169
      | ~ r2_hidden(sK168,k1_relat_1(sK170))
      | ~ r2_hidden(k4_tarski(sK168,sK169),sK170) )
    & ( ( k1_funct_1(sK170,sK168) = sK169
        & r2_hidden(sK168,k1_relat_1(sK170)) )
      | r2_hidden(k4_tarski(sK168,sK169),sK170) )
    & v1_funct_1(sK170)
    & v1_relat_1(sK170) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK168,sK169,sK170])],[f2116,f2117])).

fof(f3478,plain,(
    v1_funct_1(sK170) ),
    inference(cnf_transformation,[],[f2118])).

fof(f3477,plain,(
    v1_relat_1(sK170) ),
    inference(cnf_transformation,[],[f2118])).

fof(f3472,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2112])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2049,plain,(
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
    inference(nnf_transformation,[],[f656])).

fof(f2050,plain,(
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
    inference(rectify,[],[f2049])).

fof(f2053,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2052,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK145(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2051,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK144(X0,X1),X3),X0)
          | ~ r2_hidden(sK144(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK144(X0,X1),X4),X0)
          | r2_hidden(sK144(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2054,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK144(X0,X1),X3),X0)
            | ~ r2_hidden(sK144(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK144(X0,X1),sK145(X0,X1)),X0)
            | r2_hidden(sK144(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK144,sK145,sK146])],[f2050,f2053,f2052,f2051])).

fof(f3180,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2054])).

fof(f4251,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f3180])).

fof(f3480,plain,
    ( k1_funct_1(sK170,sK168) = sK169
    | r2_hidden(k4_tarski(sK168,sK169),sK170) ),
    inference(cnf_transformation,[],[f2118])).

fof(f3471,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2112])).

fof(f4266,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f3471])).

fof(f3481,plain,
    ( k1_funct_1(sK170,sK168) != sK169
    | ~ r2_hidden(sK168,k1_relat_1(sK170))
    | ~ r2_hidden(k4_tarski(sK168,sK169),sK170) ),
    inference(cnf_transformation,[],[f2118])).

fof(f3479,plain,
    ( r2_hidden(sK168,k1_relat_1(sK170))
    | r2_hidden(k4_tarski(sK168,sK169),sK170) ),
    inference(cnf_transformation,[],[f2118])).

cnf(c_1338,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4264])).

cnf(c_1347,negated_conjecture,
    ( v1_funct_1(sK170) ),
    inference(cnf_transformation,[],[f3478])).

cnf(c_14753,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = o_0_0_xboole_0
    | sK170 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1338,c_1347])).

cnf(c_14754,plain,
    ( r2_hidden(X0,k1_relat_1(sK170))
    | ~ v1_relat_1(sK170)
    | k1_funct_1(sK170,X0) = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_14753])).

cnf(c_1348,negated_conjecture,
    ( v1_relat_1(sK170) ),
    inference(cnf_transformation,[],[f3477])).

cnf(c_14758,plain,
    ( r2_hidden(X0,k1_relat_1(sK170))
    | k1_funct_1(sK170,X0) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14754,c_1348])).

cnf(c_53673,plain,
    ( k1_funct_1(sK170,X0) = o_0_0_xboole_0
    | r2_hidden(X0,k1_relat_1(sK170)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14758])).

cnf(c_1340,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f3472])).

cnf(c_1048,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4251])).

cnf(c_6313,plain,
    ( ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1340,c_1048])).

cnf(c_6314,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_6313])).

cnf(c_14789,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK170 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1347,c_6314])).

cnf(c_14790,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK170)
    | ~ v1_relat_1(sK170)
    | k1_funct_1(sK170,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_14789])).

cnf(c_14794,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK170)
    | k1_funct_1(sK170,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14790,c_1348])).

cnf(c_1345,negated_conjecture,
    ( r2_hidden(k4_tarski(sK168,sK169),sK170)
    | k1_funct_1(sK170,sK168) = sK169 ),
    inference(cnf_transformation,[],[f3480])).

cnf(c_14829,plain,
    ( k1_funct_1(sK170,sK168) = sK169 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_14794,c_1345])).

cnf(c_1341,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f4266])).

cnf(c_14735,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK170 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1341,c_1347])).

cnf(c_14736,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK170))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK170,X0)),sK170)
    | ~ v1_relat_1(sK170) ),
    inference(unflattening,[status(thm)],[c_14735])).

cnf(c_14740,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK170,X0)),sK170)
    | ~ r2_hidden(X0,k1_relat_1(sK170)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14736,c_1348])).

cnf(c_14741,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK170))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK170,X0)),sK170) ),
    inference(renaming,[status(thm)],[c_14740])).

cnf(c_53674,plain,
    ( r2_hidden(X0,k1_relat_1(sK170)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK170,X0)),sK170) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14741])).

cnf(c_60781,plain,
    ( r2_hidden(k4_tarski(sK168,sK169),sK170) = iProver_top
    | r2_hidden(sK168,k1_relat_1(sK170)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14829,c_53674])).

cnf(c_1344,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK168,sK169),sK170)
    | ~ r2_hidden(sK168,k1_relat_1(sK170))
    | k1_funct_1(sK170,sK168) != sK169 ),
    inference(cnf_transformation,[],[f3481])).

cnf(c_1353,plain,
    ( k1_funct_1(sK170,sK168) != sK169
    | r2_hidden(k4_tarski(sK168,sK169),sK170) != iProver_top
    | r2_hidden(sK168,k1_relat_1(sK170)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1344])).

cnf(c_60785,plain,
    ( r2_hidden(sK168,k1_relat_1(sK170)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_60781,c_1353,c_14829])).

cnf(c_62546,plain,
    ( k1_funct_1(sK170,sK168) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_53673,c_60785])).

cnf(c_62547,plain,
    ( sK169 = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_62546,c_14829])).

cnf(c_1346,negated_conjecture,
    ( r2_hidden(k4_tarski(sK168,sK169),sK170)
    | r2_hidden(sK168,k1_relat_1(sK170)) ),
    inference(cnf_transformation,[],[f3479])).

cnf(c_53746,plain,
    ( r2_hidden(k4_tarski(sK168,sK169),sK170) = iProver_top
    | r2_hidden(sK168,k1_relat_1(sK170)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1346])).

cnf(c_67269,plain,
    ( r2_hidden(k4_tarski(sK168,o_0_0_xboole_0),sK170) = iProver_top
    | r2_hidden(sK168,k1_relat_1(sK170)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_62547,c_53746])).

cnf(c_60673,plain,
    ( ~ r2_hidden(k4_tarski(sK168,X0),sK170)
    | r2_hidden(sK168,k1_relat_1(sK170)) ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_60674,plain,
    ( r2_hidden(k4_tarski(sK168,X0),sK170) != iProver_top
    | r2_hidden(sK168,k1_relat_1(sK170)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60673])).

cnf(c_60676,plain,
    ( r2_hidden(k4_tarski(sK168,o_0_0_xboole_0),sK170) != iProver_top
    | r2_hidden(sK168,k1_relat_1(sK170)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_60674])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_67269,c_60785,c_60676])).

%------------------------------------------------------------------------------
